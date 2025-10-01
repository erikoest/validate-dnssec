extern crate zoneparser;

use std::fs::File;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::cmp;
use std::env;

use base64::prelude::*;
use chrono::prelude::*;
use data_encoding::BASE32_DNSSEC;

use openssl::nid::Nid;
use openssl::pkey::{PKey, Public};
use openssl::ec::{EcGroup, EcKey};
use openssl::md::Md;
use openssl::md_ctx::MdCtx;
use openssl::bn::BigNum;
use openssl::ecdsa::EcdsaSig;

use zoneparser::{ZoneParser, Record, RecordData, RRType};

/* Check all signatures in a zone. The zone records are expected to
  be grouped by name. It is also expected that the apex records,
  having the key set, comes before all the other record sets.
 */

enum DnsPubKey {
    ECDSA(PKey<Public>),
    None,
}

#[derive(Eq)]
struct NsecLink {
    name: String,
    next: String,
}

impl PartialEq for NsecLink {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl PartialOrd for NsecLink {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        return Some(self.cmp(other));
    }
}

impl Ord for NsecLink {
    fn cmp(&self, other: &Self) -> Ordering {
        return self.name.cmp(&other.name);
    }
}

// Name and next name of an Nsec or Nsec3 record. Used for checking the
// completeness of the nsec/nsec3 daisy chain.
impl NsecLink {
    /*
    Note: Names are put into a more comparable format by reversing the labes,
    and inserting spaces in-between them. In this way, they are compared from
    top label to bottom, and end of label sorts before any other characters.
     */
    fn from_nsec3(name: &str, next: &str) -> Self {
        let mut name_labels: Vec<&str> = name.split(".").collect();
        name_labels.pop();
        name_labels.reverse();
        let name_reverse = name_labels.join(" .").to_string();

        let mut next_labels: Vec<&str> = next.split(".").collect();
        next_labels.pop();
        next_labels.reverse();
        let next_reverse = next_labels.join(" .").to_string();

        Self {
            name: name_reverse,
            next: next_reverse,
        }
    }

    fn from_nsec(rr: &Record) -> Self {
        let mut name_labels: Vec<&str> = rr.name.split(".").collect();
        name_labels.pop();
        name_labels.reverse();
        let name_reverse = name_labels.join(" .").to_string();

        let mut next_labels: Vec<&str> = rr.data[0].data.split(".").collect();
        next_labels.pop();
        next_labels.reverse();
        let next_reverse = next_labels.join(" .").to_string();

        Self {
            name: name_reverse,
            next: next_reverse,
        }
    }

    fn name_unreversed(&self) -> String {
        let mut labels: Vec<&str> = self.name.split(" .").collect();

        labels.reverse();
        let mut ret = labels.join(".");
        ret.push('.');
        
        return ret;
    }

    fn next_unreversed(&self) -> String {
        let mut labels: Vec<&str> = self.next.split(" .").collect();

        labels.reverse();
        let mut ret = labels.join(".");
        ret.push('.');
        
        return ret;
    }
}

#[derive(Eq, PartialEq)]
struct Signature {
    wire_data: Vec<u8>,
    algorithm: u8,
    keytag: u16,
    sig_data: Vec<u8>,
    name: String,
}

impl Signature {
    fn from_record(rr: &Record, p: &ZoneParser, now_epoch: u32,
                   verbose: bool) -> Self {
        let mut sdata: Vec<u8> = vec!();
        for d in &rr.data[8..] {
            sdata.append(&mut BASE64_STANDARD.decode(&d.data).unwrap());
        }

        let wdata = p.rdata_to_wireformat(rr, now_epoch).into_bytes();
        let alg = wdata[2];
        let keytag: u16 = rr.data[6].data.parse().unwrap();
        let name;
        if verbose {
            name = format!("{} {:?}", rr.name, rr.data[0]);
        }
        else {
            name = "".to_string();
        }

        Self {
            wire_data: wdata,
            algorithm: alg,
            keytag: keytag,
            sig_data: sdata,
            name: name,
        }
    }
}

struct DnsKey {
    algorithm: u8,
    pubkey: DnsPubKey,
    keytag: u16,
}

impl DnsKey {
    fn from_record(rr: &Record, p: &ZoneParser) -> Self {
        let algorithm = rr.data[2].data.parse().expect("Algorithm number");

        let pubkey = match algorithm {
            13 => {
                let mut bytes: Vec<u8> = vec!();
                for d in &rr.data[3..] {
                    bytes.append(&mut BASE64_STANDARD.decode(&d.data)
                                 .expect("Key b64decode"));
                }

                let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1)
                    .unwrap();
                let eckey = EcKey::from_public_key_affine_coordinates(
                    group.as_ref(),
                    BigNum::from_slice(&bytes[0..32]).as_ref().unwrap(),
                    BigNum::from_slice(&bytes[32..64]).as_ref().unwrap(),
                ).unwrap();
                eckey.check_key().unwrap();

                let key = PKey::from_ec_key(eckey).unwrap();
                DnsPubKey::ECDSA(key)
            },
            _ => {
                DnsPubKey::None
            },
        };

        let keytag = DnsKey::calc_keytag(&rr, p);

        Self {
            algorithm: algorithm,
            pubkey: pubkey,
            keytag: keytag,
        }
    }

    fn calc_keytag(rr: &Record, p: &ZoneParser) -> u16 {
        let mut tag: u32 = 0;

        let key = p.rdata_to_wireformat(rr, 0).into_bytes();

        for i in 0..key.len() {
            if (i & 1) > 0 {
                tag += key[i] as u32;
            }
            else {
                tag += (key[i] as u32) << 8;
            }
        }

        tag += (tag >> 16) & 0xFFFF;

        return (tag & 0xFFFF) as u16;
    }
}

#[derive(Eq, PartialEq)]
struct WireRecord {
    bytes: Vec<u8>,
}

impl PartialOrd for WireRecord {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        return Some(self.cmp(other));
    }
}

impl Ord for WireRecord {
    fn cmp(&self, other: &Self) -> Ordering {
        // First compare the label
        let mut this_c = 0;
        let mut that_c = 0;
        // FIXME: try to find a more effective way to do this
        let mut this_name: Vec<&[u8]> = vec!();
        let mut that_name: Vec<&[u8]> = vec!();
        loop {
            let len = self.bytes[this_c] as usize;
            if len == 0 {
                this_c += 1;
                break;
            }
            this_name.push(&self.bytes[this_c + 1..this_c + 1 + len]);
            this_c += len + 1;
        }
        loop {
            let len = other.bytes[that_c] as usize;
            if len == 0 {
                that_c += 1;
                break;
            }
            that_name.push(&other.bytes[that_c + 1..that_c + 1 + len]);
            that_c += len + 1;
        }

        loop {
            if this_name.is_empty() {
                if that_name.is_empty() {
                    break;
                }
                return Ordering::Less;
            }
            if that_name.is_empty() {
                return Ordering::Greater;
            }

            let res = Self::cmp_slice(this_name.pop().unwrap(),
                                      that_name.pop().unwrap());
            if res != Ordering::Equal {
                return res;
            }
        }

        // Then compare the next 8 bytes
        let res = Self::cmp_slice(
            &self.bytes[this_c..this_c + 8], &other.bytes[that_c..that_c + 8]);
        if res != Ordering::Equal {
            return res;
        }

        // Skip rdata length field
        this_c += 10;
        that_c += 10;

        // Finally, compare the rdata (not including the length field)
        return Self::cmp_slice(&self.bytes[this_c..],
                               &other.bytes[that_c..]);
    }
}

// Additional functions for records
impl WireRecord {
    fn cmp_slice(this: &[u8], that: &[u8]) -> Ordering {
        let this_len = this.len();
        let that_len = that.len();
        
        for i in 0..this_len {
            if i < that_len {
                if this[i] == that[i] {
                    continue;
                }
                return this[i].cmp(&that[i]);
            }
            else {
                return Ordering::Less;
            }
        }

        if this_len == that_len {
            return Ordering::Equal;
        }
        else {
            return Ordering::Greater;
        }
    }

    fn into_bytes(self) -> Vec<u8> {
        return self.bytes;
    }
}

#[derive(Eq, PartialEq)]
struct SignedSet {
    wire_data: Vec<WireRecord>,
    sig: Vec<Signature>,
}

impl PartialOrd for SignedSet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // Possible to speed up this by storing the first record separately?
        return self.wire_data.last().partial_cmp(&other.wire_data.last());
    }
}

impl Ord for SignedSet {
    fn cmp(&self, other: &Self) -> Ordering {
        return self.wire_data.last().cmp(&other.wire_data.last());
    }
}

impl SignedSet {
    fn new() -> Self {
        Self {
            wire_data: vec!(),
            sig: vec!(),
        }
    }

    fn add_sig(&mut self, sig: Signature) {
        self.sig.push(sig);
    }
    
    fn add_data(&mut self, wire: WireRecord) {
        self.wire_data.push(wire);
    }

    fn sort_data(&mut self) {
        self.wire_data.sort();
    }
}

// Extension to the ZoneParser for building wire format records
trait ToWireFormat {
    fn to_wireformat(&self, rr: &Record) -> WireRecord;
    fn rdata_to_wireformat(&self, rr: &Record, now_epoch: u32) -> WireRecord;
    fn add_rdata(&self, rr: &Record, bytes: &mut Vec<u8>,
                 now_epoch: u32) -> u16;
    fn add_type_bitmap(&self, bytes: &mut Vec<u8>, rd: &[RecordData]) -> u16;
    fn add_domain_name_canonical(&self, bytes: &mut Vec<u8>,
                                 name: &str) -> u16;
    fn add_u8_canonical(&self, bytes: &mut Vec<u8>, val: u8) -> u16;
    fn add_u16_canonical(&self, bytes: &mut Vec<u8>, val: u16) -> u16;
    fn add_u32_canonical(&self, bytes: &mut Vec<u8>, val: u32) -> u16;
    fn add_domain_name_rdata(&self, bytes: &mut Vec<u8>,
                             rd: &RecordData) -> u16;
    fn add_character_string_rdata(&self, bytes: &mut Vec<u8>,
                                  rd: &RecordData) -> u16;
    fn parse_dt_rdata(&self, rd: &RecordData) -> u32;
    fn add_u8_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16;
    fn add_u16_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16;
    fn add_u32_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16;
}

impl ToWireFormat for ZoneParser<'_> {
    fn to_wireformat(&self, rr: &Record) -> WireRecord {
        let mut bytes = vec!();

        // name
        self.add_domain_name_canonical(&mut bytes, &rr.name);
        // type
        self.add_u16_canonical(&mut bytes, rr.rrtype as u16);
        // class
        self.add_u16_canonical(&mut bytes, rr.class as u16);
        // ttl
        self.add_u32_canonical(&mut bytes, rr.ttl);

        // rdlength (add space, set values later)
        let rdlength_pos = bytes.len();
        bytes.push(0);
        bytes.push(0);

        let len = self.add_rdata(rr, &mut bytes, 0);

        bytes[rdlength_pos] = (len >> 8) as u8;
        bytes[rdlength_pos + 1] = (len & 255) as u8;

        WireRecord {
            bytes: bytes,
        }
    }

    fn rdata_to_wireformat(&self, rr: &Record, now_epoch: u32) -> WireRecord {
        let mut bytes = vec!();
        let _ = self.add_rdata(rr, &mut bytes, now_epoch);

        WireRecord {
            bytes: bytes,
        }
    }
    
    fn add_rdata(&self, rr: &Record, bytes: &mut Vec<u8>,
                 now_epoch: u32) -> u16 {
        let mut len: u16 = 0;

        // RecordData in canonical form
        match rr.rrtype {
            RRType::SOA => {
                // mname, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
                // rname, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[1]);
                // serial, u32
                len += self.add_u32_rdata(bytes, &rr.data[2]);
                // refresh, u32
                len += self.add_u32_rdata(bytes, &rr.data[3]);
                // retry, u32
                len += self.add_u32_rdata(bytes, &rr.data[4]);
                // expire, u32
                len += self.add_u32_rdata(bytes, &rr.data[5]);
                // minimum, u32
                len += self.add_u32_rdata(bytes, &rr.data[6]);
            },
            RRType::NS => {
                // nsdname, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
            },
            RRType::PTR => {
                // Ptr dname
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
            },
            RRType::SRV => {
                // Priority, u16
                len += self.add_u16_rdata(bytes, &rr.data[0]);
                // Weight, u16
                len += self.add_u16_rdata(bytes, &rr.data[1]);
                // Port, u16
                len += self.add_u16_rdata(bytes, &rr.data[2]);
                // Target, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[3]);
            },
            RRType::A => {
                // address, u32
                let addr: Ipv4Addr = rr.data[0].data.parse().unwrap();

                for o in addr.octets() {
                    bytes.push(o);
                }

                len += 4;
            },
            RRType::AAAA => {
                // Complete address, u128
                let addr: Ipv6Addr = rr.data[0].data.parse().unwrap();

                for o in addr.octets() {
                    bytes.push(o);
                }

                len += 16;
            },
            RRType::TXT => {
                // Each txt field is a character strings
                for d in &rr.data {
                    len += self.add_character_string_rdata(bytes, &d);
                }
            },
            RRType::MX => {
                // Preference
                len += self.add_u16_rdata(bytes, &rr.data[0]);
                // Exchange, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[1]);
            },
            RRType::CNAME => {
                // Cname, (domain name)
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
            },
            RRType::CAA => {
                // Flags, u8
                len += self.add_u8_rdata(bytes, &rr.data[0]);
                // Tag length, u8 [1 - 15]
                // Tag, [0..tag length - 1] x u8
                len += self.add_character_string_rdata(bytes, &rr.data[1]);
                // Value, [0..data - tag length - 2]
                let mut val = rr.data[2].data.clone().into_bytes();
                len += val.len() as u16;
                bytes.append(&mut val);
            },
            RRType::HINFO => {
                // CPU, (character string)
                len += self.add_character_string_rdata(bytes, &rr.data[0]);
                // OS, (character string)
                len += self.add_character_string_rdata(bytes, &rr.data[1]);
            },
            RRType::DNSKEY => {
                // Flags, u16
                len += self.add_u16_rdata(bytes, &rr.data[0]);
                // Protocol, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Algorithm, u8
                len += self.add_u8_rdata(bytes, &rr.data[2]);
                // Pubkey, &[u8]
                for d in &rr.data[3..] {
                    let pk = &mut BASE64_STANDARD.decode(&d.data).unwrap();
                    len += pk.len() as u16;
                    bytes.append(pk);
                }
            },
            RRType::DS => {
                // Key tag, u16
                len += self.add_u16_rdata(bytes, &rr.data[0]);
                // Algorith, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Digest type, u8
                len += self.add_u8_rdata(bytes, &rr.data[2]);
                // Digest
                for d in &rr.data[3..] {
                    let dig = &mut hex::decode(&d.data).unwrap();
                    len += dig.len() as u16;
                    bytes.append(dig);
                }
            },
            RRType::NSEC3 => {
                // Hash algorithm, u8
                len += self.add_u8_rdata(bytes, &rr.data[0]);
                // Flags, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Iterations, u16
                len += self.add_u16_rdata(bytes, &rr.data[2]);
                // Salt length, u8
                // Salt, &[u8]
                if rr.data[3].data == "-" {
                    bytes.push(0);
                    len += 1;
                }
                else {
                    let mut salt = rr.data[3].data.clone().into_bytes();
                    bytes.push(salt.len() as u8);
                    bytes.append(&mut salt);
                    len += salt.len() as u16 + 1;
                }
                // Hash length, u8
                // Next hashed owner name &[u8],
                let mut hname = BASE32_DNSSEC.decode(
                    &rr.data[4].data.as_bytes()).unwrap();
                bytes.push(hname.len() as u8);
                len += hname.len() as u16 + 1;
                bytes.append(&mut hname);
                // Type bitmap
                len += self.add_type_bitmap(bytes, &rr.data[5..]);
            },
            RRType::NSEC => {
                // Next domain
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
                // Type bitmap
                len += self.add_type_bitmap(bytes, &rr.data[1..]);
            },
            RRType::NSEC3PARAM => {
                // Hash algorithm, u8
                len += self.add_u8_rdata(bytes, &rr.data[0]);
                // Flags, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Iterations, u16
                len += self.add_u16_rdata(bytes, &rr.data[2]);
                // Salt length, u8
                // Salt, &[u8]
                if rr.data[3].data == "-" {
                    bytes.push(0);
                    len += 1;
                }
                else {
                    let mut salt = rr.data[3].data.clone().into_bytes();
                    bytes.push(salt.len() as u8);
                    bytes.append(&mut salt);
                    len += salt.len() as u16 + 1;
                }
            },
            RRType::RRSIG => {
                // Type covered, u16
                len += self.add_u16_canonical(
                    bytes, self.rrtype_from_str(&rr.data[0].data) as u16);
                // Algorithm, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Labels, u8
                len += self.add_u8_rdata(bytes, &rr.data[2]);
                // Original TTL, u32
                len += self.add_u32_rdata(bytes, &rr.data[3]);
                // Signature expiration, u32
                let expiry = self.parse_dt_rdata(&rr.data[4]);
                if now_epoch != 0 {
                    if expiry < now_epoch {
                        println!("Signature {} is too old.", rr);
                    }
                }
                len += self.add_u32_canonical(bytes, expiry);
                // Signature inception, u32
                let incept = self.parse_dt_rdata(&rr.data[5]);
                if now_epoch != 0 {
                    if incept > now_epoch {
                        println!("Signature {} is from the future.", rr);
                    }
                }
                len += self.add_u32_canonical(bytes, incept);
                // Key tag, u16
                len += self.add_u16_rdata(bytes, &rr.data[6]);
                // Signers name, (domain name)
                len += self.add_domain_name_rdata(bytes, &rr.data[7]);
                // Signature (omitted, we're only using this wire data for
                // verifying the signature)
            },
            RRType::TLSA => {
                // Cert usage, u8
                len += self.add_u8_rdata(bytes, &rr.data[0]);
                // Selector, u8
                len += self.add_u8_rdata(bytes, &rr.data[1]);
                // Matching type, u8
                len += self.add_u8_rdata(bytes, &rr.data[2]);
                // Certification data
                for d in &rr.data[3..] {
                    let dig = &mut hex::decode(&d.data).unwrap();
                    len += dig.len() as u16;
                    bytes.append(dig);
                }
            },
            _ => {
                panic!("Unknown RRType {}", rr.rrtype);
            },
        }

        return len;
    }

    fn add_type_bitmap(&self, bytes: &mut Vec<u8>, rd: &[RecordData]) -> u16 {
        if rd.is_empty() {
            // Corner case: No types
            return 0;
        }

        let mut bm_hash: HashMap<u8, (u128, u128)> = HashMap::new();
        let mut blocks: Vec<u8> = vec!();

        for d in rd {
            let (window_block, bit1, bit2) = self.rrtype_bm_from_str(&d.data);
            if let Some(&(mut bm1, mut bm2)) = bm_hash.get(&window_block) {
                bm1 |= bit1;
                bm2 |= bit2;
                bm_hash.insert(window_block, (bm1, bm2));
            }
            else {
                bm_hash.insert(window_block, (bit1, bit2));
                blocks.push(window_block);
            }
        }

        let mut len: u16 = 0;

        blocks.sort();
        for b in blocks {
            let (bm1, bm2) = bm_hash.get(&b).unwrap();
            let bm1array = bm1.to_be_bytes();
            let bm2array = bm2.to_be_bytes();

            let mut bmlen = 32;
            loop {
                if bmlen > 16 {
                    if bm2array[bmlen - 17] != 0 {
                        break;
                    }
                }
                else {
                    if bm1array[bmlen - 1] != 0 {
                        break;
                    }
                }
                bmlen -= 1;
            }

            bytes.push(b);
            bytes.push(bmlen as u8);
            for i in 0..cmp::min(bmlen,16) {
                bytes.push(bm1array[i]);
            }
            if bmlen > 16 {
                for i in 0..bmlen - 17 {
                    bytes.push(bm2array[i]);
                }
            }
            len += bmlen as u16 + 2;
        }

        return len;
    }

    fn add_domain_name_canonical(&self, bytes: &mut Vec<u8>,
                                 name: &str) -> u16 {
        let mut length = 0;

        for label in self.absolute_name(&name).to_lowercase().split(".") {
            let mut lbytes = String::from(label).into_bytes();
            let llength = lbytes.len() as u8;
            bytes.push(llength);
            bytes.append(&mut lbytes);

            length += llength as u16 + 1;
        }

        return length;
    }

    fn add_u8_canonical(&self, bytes: &mut Vec<u8>, val: u8) -> u16 {
        bytes.push(val);
        return 1;
    }

    fn add_u16_canonical(&self, bytes: &mut Vec<u8>, val: u16) -> u16 {
        bytes.push((val >> 8) as u8);
        bytes.push((val & 255) as u8);
        return 2;
    }

    fn add_u32_canonical(&self, bytes: &mut Vec<u8>, val: u32) -> u16 {
        bytes.push((val >> 24) as u8);
        bytes.push(((val >> 16) & 255) as u8);
        bytes.push(((val >> 8) & 255) as u8);
        bytes.push((val & 255) as u8);
        return 4;
    }

    // FIXME: Do we need absolute name here?
    fn add_domain_name_rdata(&self, bytes: &mut Vec<u8>,
                             rd: &RecordData) -> u16 {
        let mut length = 0;

        for label in rd.data.to_lowercase().split(".") {
            let mut lbytes = String::from(label).into_bytes();
            let llength = lbytes.len() as u8;
            bytes.push(llength as u8);
            bytes.append(&mut lbytes);

            length += llength as u16 + 1;
        }

        return length;
    }

    fn add_character_string_rdata(&self, bytes: &mut Vec<u8>,
                                  rd: &RecordData) -> u16 {
        let length = rd.data.len() as u8;
        let mut txt = rd.data.clone().into_bytes();
        bytes.push(length);
        bytes.append(&mut txt);
        return length as u16 + 1;
    }
    
    fn parse_dt_rdata(&self, rd: &RecordData) -> u32 {
        // Convert YYYYMMDDhhmmss field into epoch
        let n: u64 = rd.data.parse().unwrap();
        let date = (n/(1000000 as u64)) as u32;
        let time = (n%(1000000 as u64)) as u32;
        return Utc.with_ymd_and_hms(
            (date/10000) as i32,
            (date/100)%100,
            date%100,
            (time/10000)%100,
            (time/100)%100,
            time%100
        ).unwrap().timestamp() as u32;
    }

    fn add_u8_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16 {
        return self.add_u8_canonical(bytes, rd.data.parse().unwrap());
    }

    fn add_u16_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16 {
        return self.add_u16_canonical(bytes, rd.data.parse().unwrap());
    }

    fn add_u32_rdata(&self, bytes: &mut Vec<u8>, rd: &RecordData) -> u16 {
        return self.add_u32_canonical(bytes, rd.data.parse().unwrap());
    }
}

/* Iterator which gets rrset on each iteration. In a strict sense,
this struct is not an iterator (it does not implement the iterator
trait). Also, it does not return the next item. Rather, it keeps it
until the next iteration step is performed.
 */

// FIXME: Also count
//   delegation_count
//   record sets ?
struct SetIterator<'a> {
    parser: ZoneParser<'a>,
    next: Option<Record>,
    keys: Vec<DnsKey>,
    nsec_chain: Vec<NsecLink>,
    rr_count: u32,
    name_count: u32,
    key_count: u32,
    sig_count: u32,
    sig_failures: u32,
    nsec_failures: u32,
    now_epoch: u32,
    verbose: bool,
}

impl<'a> SetIterator<'a> {
    fn new(file: &'a File, origin: &str, now_epoch: u32,
           verbose: bool) -> Self {
	let mut parser = ZoneParser::new(&file, origin);
	let next = parser.next();

	Self {
	    parser: parser,
	    next: next,
            keys: vec!(),
            nsec_chain: vec!(),
            rr_count: 0,
            name_count: 0,
            key_count: 0,
            sig_count: 0,
            sig_failures: 0,
            nsec_failures: 0,
            now_epoch: now_epoch,
            verbose: verbose,
	}
    }

    fn print_stats(&self) {
        println!("Records found: {}", self.rr_count);
        println!("Unique names found: {}", self.name_count);
        println!("Keys found: {}", self.key_count);
        println!("Signatures verified: {}", self.sig_count);
        println!("Signatures failed: {}", self.sig_failures);
        println!("Nsec/nsec3 broken links: {}", self.nsec_failures);
    }

    fn fetch_next_name(&mut self) -> Vec<Record> {
        let mut set = vec!();
	if self.next.is_some() {
	    let name = self.next.as_ref().unwrap().name.clone();
	    while self.next.is_some() {
		if &self.next.as_ref().unwrap().name == &name {
		    let nx = self.parser.next();
		    if nx.is_some() {
			set.push(self.next.replace(nx.unwrap()).unwrap());
		    }
		    else {
			set.push(self.next.take().unwrap());
		    }
                    self.rr_count += 1;
		}
		else {
		    break;
		}
	    }
	}
        return set;
    }

    fn check_zone(&mut self) {
        loop {
            let set = self.fetch_next_name();
            if set.is_empty() {
                break;
            }

            self.name_count += 1;
            
            // Get keys
            for rr in &set {
	        if rr.rrtype == RRType::DNSKEY {
		    self.keys.push(DnsKey::from_record(&rr, &self.parser));
                    self.key_count += 1;
	        }
            }

	    let mut hashed: HashMap<RRType, SignedSet> = HashMap::new();

            // Collect signatures
            for rr in &set {
                if rr.rrtype == RRType::RRSIG {
                    let rrtype = self.parser.rrtype_from_str(
                        &rr.data[0].data);
                    if !hashed.contains_key(&rrtype) {
                        hashed.insert(rrtype, SignedSet::new());
                    }
                    hashed.get_mut(&rrtype).unwrap().add_sig(
                        Signature::from_record(
                            &rr, &self.parser, self.now_epoch, self.verbose));
                    self.sig_count += 1;
                }
                
            }

            // Collect signed records and nsec/nsec3 records
            for rr in &set {
                // Nsec and nsec3 records are pushed to the nsec chain before
                // being examined in canonical order
                if rr.rrtype == RRType::NSEC {
                    self.nsec_chain.push(NsecLink::from_nsec(rr));
                }

                if rr.rrtype == RRType::NSEC3 {
                    self.nsec_chain.push(NsecLink::from_nsec3(
                        &rr.name, &self.parser.absolute_name(&rr.data[4].data)
                            .to_lowercase()));
                }
                
                if let Some(sig) = hashed.get_mut(&rr.rrtype) {
                    sig.add_data(
                        self.parser.to_wireformat(&rr));
                }
            }

            // Validate each signature
            for sset in hashed.values_mut() {
                self.verify_signature(sset);
            }
        }

        self.nsec_chain.sort();

        let mut somelast: Option<&NsecLink> = None;
        for link in self.nsec_chain.iter() {
            if let Some(last) = somelast {
                if last.next != link.name {
                    if self.verbose {
                        println!("Broken NSEC link between {} and {}",
                                 last.next_unreversed(),
                                 link.name_unreversed());
                    }
                    self.nsec_failures += 1;
                }
            }
            let _ = somelast.insert(link);
        }

        if let Some(last) = somelast {
            if last.next != self.nsec_chain[0].name {
                if self.verbose {
                    println!("Broken NSEC link between {} and {}",
                             last.next_unreversed(),
                             self.nsec_chain[0].name_unreversed());
                }
                self.nsec_failures += 1;
            }
        }
    }

    fn verify_signature(&mut self, ss: &mut SignedSet) {
        ss.sort_data();

        for sig in &ss.sig {
            for dnskey in &self.keys {
                if sig.keytag != dnskey.keytag {
                    continue;
                }
        
                match &dnskey.pubkey {
                    DnsPubKey::ECDSA(key) => {
                        // ECDSAP256SHA256
                        let mut ctx = MdCtx::new().unwrap();
                        ctx.digest_verify_init(Some(Md::sha256()),
                                               &key).unwrap();
                        ctx.digest_verify_update(&sig.wire_data).unwrap();
                    
                        for wd in &ss.wire_data {
                            ctx.digest_verify_update(&wd.bytes).unwrap();
                        }

                        let esig = EcdsaSig::from_private_components(
                            BigNum::from_slice(&sig.sig_data[0..32]).unwrap(),
                            BigNum::from_slice(&sig.sig_data[32..64]).unwrap(),
                        ).unwrap();

                        match ctx.digest_verify_final(&esig.to_der().unwrap()) {
                            Ok(verify_ok) => {
                                if verify_ok {
                                    if self.verbose {
                                        println!("Signature {} is valid",
                                                 sig.name);
                                    }
                                }
                                else {
                                    if self.verbose {
                                        println!("Signature {} is not valid",
                                                 sig.name);
                                    }
                                    self.sig_failures += 1;
                                }
                            },
                            Err(_) => {
                                if self.verbose {
                                    println!(
                                        "Verification of signature {} failed",
                                        sig.name);
                                    // println!("Data {}", hex::encode(bytes));
                                }
                                self.sig_failures += 1;
                            },
                        }
                    },
                    _ => {
                        panic!("Unknown dnskey algorithm {}", dnskey.algorithm);
                    },
                }
            }
        }
    }
}

fn usage() {
    println!("Usage: validate_dnssec [-o origin] [-t] [-v] <signed zonefile>");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut origin = "";
    let mut verbose = false;
    let mut now_epoch: u32 = Utc::now().timestamp() as u32;
    let mut arg_count = 1;

    loop {
        if args.len() >= arg_count + 2 {
	    match args[arg_count].as_str() {
                "-o" | "--origin" => {
                    origin = &args[arg_count + 1];
                    arg_count += 2;
                    continue;
                },
	        "-t" | "--time" => {
		    now_epoch = args[arg_count + 1].parse().unwrap();
		    arg_count += 2;
                    continue;
	        },
                &_ => { }
            }
        }

        if args.len() >= arg_count + 1 {
	    match args[arg_count].as_str() {
	        "-v" | "--verbose" => {
		    verbose = true;
		    arg_count += 1;
                    continue;
	        },
                &_ => { }
            }
        }

	break;
    }

    if args.len() < 1 + arg_count {
        usage();
        return;
    }

    if origin == "" {
        origin = &args[arg_count];
    }

    let file = File::open(&args[arg_count]).unwrap();

    let mut si = SetIterator::new(&file, origin, now_epoch, verbose);

    si.check_zone();
    si.print_stats();
}
