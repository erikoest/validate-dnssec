extern crate zoneparser;

use std::fs::File;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::cmp;
use std::env;
use rayon::prelude::*;
use rayon::ThreadPoolBuilder;
use crossbeam_channel::{unbounded, Sender, Receiver};
use std::thread::spawn;

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
use openssl::rsa::Rsa;

use zoneparser::{ZoneParser, Record, RecordData, RRType};

/* Check all signatures in a zone. The zone records are expected to
  be grouped by name. It is also expected that the apex records,
  having the key set, comes before all the other record sets.
 */

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

#[derive(Clone, Eq, PartialEq)]
struct Signature {
    wire_data: Vec<u8>,
    algorithm: u8,
    keytag: u16,
    sig_data: Vec<u8>,
    name: String,
}

impl Signature {
    fn from_record(rr: &Record, p: &ZoneParser, now_epoch: u32,
                   verbose: bool) -> Result<Self, String> {
        let mut sdata: Vec<u8> = vec!();
        for d in &rr.data[8..] {
            sdata.append(&mut BASE64_STANDARD.decode(&d.data).map_err(|_| "Invalid base64 encoding")?);
        }

        let wdata = p.rdata_to_wireformat(rr, now_epoch)?.into_bytes();
        let alg = wdata[2];
        let keytag: u16 = rr.data[6].data.parse().unwrap();
        let name;
        if verbose {
            name = format!("{} {:?}", rr.name, rr.data[0]);
        }
        else {
            name = "".to_string();
        }

        Ok(Self {
            wire_data: wdata,
            algorithm: alg,
            keytag: keytag,
            sig_data: sdata,
            name: name,
        })
    }
}

#[derive(Clone)]
struct DnsKey {
    algorithm: u8,
    pubkey: PKey<Public>,
    keytag: u16,
}

impl DnsKey {
    fn from_record(rr: &Record, p: &ZoneParser) -> Result<Self, String> {
        let algorithm = rr.data[2].data.parse().map_err(|_| "Bad algorithm number")?;

        let mut bytes: Vec<u8> = vec!();
        for d in &rr.data[3..] {
            bytes.append(&mut BASE64_STANDARD.decode(&d.data)
                         .map_err(|_| "Invalid base64 encoding")?);
        }

        let pubkey = match algorithm {
            5 | 8 => {
                // RSASHA1
                let e_start;
                let e_len;

                if bytes[0] == 0 {
                    e_start = 3;
                    e_len = (bytes[1] << 8 + bytes[2]) as usize;
                }
                else {
                    e_start = 1;
                    e_len = bytes[0] as usize;
                }

                let e = &bytes[e_start..e_start + e_len];
                let n = &bytes[e_start + e_len..];

                let rsa = Rsa::from_public_components(
                    BigNum::from_slice(n).unwrap(),
                    BigNum::from_slice(e).unwrap(),
                ).unwrap();

                PKey::from_rsa(rsa).unwrap()
            },
            13 => {
                // ECDSAP256SHA256
                let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1)
                    .unwrap();
                let eckey = EcKey::from_public_key_affine_coordinates(
                    group.as_ref(),
                    BigNum::from_slice(&bytes[0..32]).as_ref().unwrap(),
                    BigNum::from_slice(&bytes[32..64]).as_ref().unwrap(),
                ).unwrap();
                eckey.check_key().unwrap();

                PKey::from_ec_key(eckey).unwrap()
            },
            _ => {
                panic!("Don't know algorithm {}", algorithm);
            },
        };

        let keytag = DnsKey::calc_keytag(&rr, p)?;

        Ok(Self {
            algorithm: algorithm,
            pubkey: pubkey,
            keytag: keytag,
        })
    }

    fn calc_keytag(rr: &Record, p: &ZoneParser) -> Result<u16, String> {
        let mut tag: u32 = 0;

        let key = p.rdata_to_wireformat(rr, 0)?.into_bytes();

        for i in 0..key.len() {
            if (i & 1) > 0 {
                tag += key[i] as u32;
            }
            else {
                tag += (key[i] as u32) << 8;
            }
        }

        tag += (tag >> 16) & 0xFFFF;

        return Ok((tag & 0xFFFF) as u16);
    }
}

#[derive(Clone, Eq, PartialEq)]
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

#[derive(Clone, Eq, PartialEq)]
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

type CheckSigReceiver = Receiver<SignedSet>;
type FailuresSender = Sender<u32>;

// Extension to the ZoneParser for building wire format records
trait ToWireFormat {
    fn to_wireformat(&self, rr: &Record) -> Result<WireRecord, String>;
    fn rdata_to_wireformat(&self, rr: &Record, now_epoch: u32) -> Result<WireRecord, String>;
    fn add_rdata(&self, rr: &Record, bytes: &mut Vec<u8>,
                 now_epoch: u32) -> Result<u16, String>;
    fn add_type_bitmap(&self, bytes: &mut Vec<u8>, rd: &[RecordData])
                       -> Result<u16, String>;
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
    fn to_wireformat(&self, rr: &Record) -> Result<WireRecord, String> {
        let mut bytes = vec!();

        // name
        self.add_domain_name_canonical(&mut bytes, &rr.name);
        // type
        self.add_u16_canonical(&mut bytes, rr.rrtype.discriminant());
        // class
        self.add_u16_canonical(&mut bytes, rr.class as u16);
        // ttl
        self.add_u32_canonical(&mut bytes, rr.ttl);

        // rdlength (add space, set values later)
        let rdlength_pos = bytes.len();
        bytes.push(0);
        bytes.push(0);

        let len = self.add_rdata(rr, &mut bytes, 0)?;

        bytes[rdlength_pos] = (len >> 8) as u8;
        bytes[rdlength_pos + 1] = (len & 255) as u8;

        Ok(WireRecord {
            bytes: bytes,
        })
    }

    fn rdata_to_wireformat(&self, rr: &Record, now_epoch: u32) -> Result<WireRecord, String> {
        let mut bytes = vec!();
        let _ = self.add_rdata(rr, &mut bytes, now_epoch)?;

        Ok(WireRecord {
            bytes: bytes,
        })
    }
    
    fn add_rdata(&self, rr: &Record, bytes: &mut Vec<u8>,
                 now_epoch: u32) -> Result<u16, String> {
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
                let addr: Ipv4Addr = rr.data[0].data.parse().map_err(|_| "Bad address")?;

                for o in addr.octets() {
                    bytes.push(o);
                }

                len += 4;
            },
            RRType::AAAA => {
                // Complete address, u128
                let addr: Ipv6Addr = rr.data[0].data.parse().map_err(|_| "Bad address")?;

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
                    let pk = &mut BASE64_STANDARD.decode(&d.data).map_err(|_| "Invalid base64 encoding")?;
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
                    let dig = &mut hex::decode(&d.data).map_err(|_| "Bad hex encoding")?;
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
                    let mut salt = hex::decode(&rr.data[3].data).map_err(|_| "Bad hex encoding")?;
                    bytes.push(salt.len() as u8);
                    len += salt.len() as u16 + 1;
                    bytes.append(&mut salt);
                }
                // Hash length, u8
                // Next hashed owner name &[u8],
                let mut hname = BASE32_DNSSEC.decode(
                    &rr.data[4].data.as_bytes()).map_err(|_| "Bad base32 encoding")?;
                bytes.push(hname.len() as u8);
                len += hname.len() as u16 + 1;
                bytes.append(&mut hname);
                // Type bitmap
                len += self.add_type_bitmap(bytes, &rr.data[5..])?;
            },
            RRType::NSEC => {
                // Next domain
                len += self.add_domain_name_rdata(
                    bytes, &rr.data[0]);
                // Type bitmap
                len += self.add_type_bitmap(bytes, &rr.data[1..])?;
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
                    let mut salt = hex::decode(&rr.data[3].data).map_err(|_| "Bad hex encoding")?;
                    bytes.push(salt.len() as u8);
                    len += salt.len() as u16 + 1;
                    bytes.append(&mut salt);
                }
            },
            RRType::RRSIG => {
                // Type covered, u16
                len += self.add_u16_canonical(
                    bytes, self.rrtype_from_str(
                        &rr.data[0].data)?.discriminant());
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
                    let dig = &mut hex::decode(&d.data).map_err(|_| "Bad hex encoding")?;
                    len += dig.len() as u16;
                    bytes.append(dig);
                }
            },
            _ => {
                // Assuming anonymous type with 'TYPEXXX \# MM NNNN' syntax
                // Require first field to be '#'
                if rr.data[0].data != "#" {
                    return Err("Bad rdata".to_string());
                }
                let length = rr.data[1].data.parse::<usize>().map_err(
                    |_| "Bad rdata length field")?;
                let data = hex::decode(&rr.data[2].data).map_err(
                    |_| "Bad rdata hex data")?;
                // Require data length to match the length field
                if data.len() != length {
                    return Err("Bad rdata".to_string());
                }
                for i in 0..length {
                    len += self.add_u8_canonical(bytes, data[i]);
                }
            },
        }

        return Ok(len);
    }

    fn add_type_bitmap(&self, bytes: &mut Vec<u8>, rd: &[RecordData])
                       -> Result<u16, String> {
        if rd.is_empty() {
            // Corner case: No types
            return Ok(0);
        }

        let mut bm_hash: HashMap<u8, (u128, u128)> = HashMap::new();
        let mut blocks: Vec<u8> = vec!();

        for d in rd {
            let (window_block, bit1, bit2) = self.rrtype_bm_from_str(&d.data)?;
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
                for i in 0..bmlen - 16 {
                    bytes.push(bm2array[i]);
                }
            }
            len += bmlen as u16 + 2;
        }
        return Ok(len);
    }

    fn add_domain_name_canonical(&self, bytes: &mut Vec<u8>,
                                 name: &str) -> u16 {
        let mut length = 0;

        for label in name.to_lowercase().split(".") {
            let mut lbytes = String::from(label).into_bytes();
            let llength = lbytes.len() as u8;
            bytes.push(llength);
            // Root domain corner case
            if llength == 0 {
                return length + 1;
            }
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
            // Root domain corner case
            if llength == 0 {
                return length + 1;
            }
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

fn verify_signature(keys: &Vec<DnsKey>, ss: &mut SignedSet, verbose: bool) -> u32 {
    ss.sort_data();

    let mut sig_failures = 0;

    for sig in &ss.sig {
        let mut keys_matched = 0;

        for dnskey in keys {
            if sig.keytag != dnskey.keytag {
                continue;
            }

            keys_matched += 1;

            let digest = match &dnskey.algorithm {
                5 => { // RSASHA1
                    Md::sha1()
                },
                8 | 13 => { // ECDSAP256SHA256
                    Md::sha256()
                },
                _ => {
                    panic!("Unknown dnskey algorithm {}", dnskey.algorithm);
                },
            };

            let mut ctx = MdCtx::new().unwrap();
            ctx.digest_verify_init(Some(&digest), &dnskey.pubkey).unwrap();
            ctx.digest_verify_update(&sig.wire_data).unwrap();

            for wd in &ss.wire_data {
                ctx.digest_verify_update(&wd.bytes).unwrap();
            }

            let result = match &dnskey.algorithm {
                5 | 8 => {
                    ctx.digest_verify_final(&sig.sig_data)
                },
                13 => {
                    let esig = &EcdsaSig::from_private_components(
                        BigNum::from_slice(&sig.sig_data[0..32]).unwrap(),
                        BigNum::from_slice(&sig.sig_data[32..64]).unwrap(),
                    ).unwrap();
                    ctx.digest_verify_final(&esig.to_der().unwrap())
                },
                _ => {
                    panic!("Unknown dnskey algorithm {}", dnskey.algorithm);
                },
            };

            match result {
                Ok(verify_ok) => {
                    if verify_ok {
                        if verbose {
                            println!("Signature {} is valid",
                                     sig.name);
                        }
                    }
                    else {
                        if verbose {
                            println!("Signature {} is not valid",
                                     sig.name);
                        }
                        sig_failures += 1;
                    }
                },
                Err(e) => {
                    if verbose {
                        println!(
                            "Verification of signature {}: {}", sig.name, e);
                        // println!("Sig data {}", hex::encode(bytes));
                    }
                    sig_failures += 1;
                },
            }

            if keys_matched == 0 {
                if verbose {
                    println!("No keys matched signature {}", sig.name);
                }
                sig_failures += 1;
            }
        }
    }

    return sig_failures;
}

fn verify_signatures(keys: Vec<DnsKey>, rx: CheckSigReceiver, tx: FailuresSender, verbose: bool) {
    for mut sset in rx.iter() {
        let failures = verify_signature(&keys, &mut sset, verbose);
        if failures > 0 {
            tx.send(failures).unwrap();
        }
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
    nsec_count: u32,
    sig_failures: u32,
    nsec_failures: u32,
    invalid_rrs: u32,
    now_epoch: u32,
    verbose: bool,
}

impl<'a> SetIterator<'a> {
    fn new(file: &'a File, origin: &str, now_epoch: u32,
           verbose: bool) -> Result<Self, String> {
	let mut parser = ZoneParser::new(&file, origin);
        let next: Option<Record>;

        // Unpack next Option<Result<rr)>>
	match parser.next() {
            Some(result) => {
                if let Err(e) = result {
                    return Err(e);
                }

                next = Some(result.unwrap());
            },
            None => {
                next = None;
            }
        }

	Ok(Self {
	    parser: parser,
	    next: next,
            keys: vec!(),
            nsec_chain: vec!(),
            rr_count: 0,
            name_count: 0,
            key_count: 0,
            sig_count: 0,
            sig_failures: 0,
            nsec_count: 0,
            nsec_failures: 0,
            invalid_rrs: 0,
            now_epoch: now_epoch,
            verbose: verbose,
	})
    }

    fn print_stats(&self) {
        println!("Records found: {}", self.rr_count);
        println!("Unique names found: {}", self.name_count);
        println!("Keys found: {}", self.key_count);
        println!("Signatures verified: {}", self.sig_count);
        println!("Signatures failed: {}", self.sig_failures);
        println!("Nsec/nsec3 records verified: {}", self.nsec_count);
        println!("Nsec/nsec3 broken links: {}", self.nsec_failures);
        println!("Invalid records: {}", self.invalid_rrs);
    }

    fn fetch_next_name(&mut self) -> Result<Vec<Record>, String> {
        let mut set = vec!();
	if self.next.is_some() {
	    let name = self.next.as_ref().unwrap().name.clone();
	    while self.next.is_some() {
		if &self.next.as_ref().unwrap().name == &name {
		    let optnx = self.parser.next();
		    if let Some(result) = optnx {
                        match result {
                            Err(e) => {
                                return Err(e);
                            },
                            Ok(nx) => {
			        set.push(self.next.replace(nx).unwrap());
                            },
                        }
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
        return Ok(set);
    }

    fn check_zone(&mut self, nthreads: usize) -> Result<(), String> {
        let mut threads = Vec::new();
        let mut senders = Vec::new();

        let mut ti = 0;
        let verbose = self.verbose;

        let (failures_tx, failures_rx) = unbounded();

        loop {
            let set = self.fetch_next_name()?;
            if set.is_empty() {
                break;
            }

            self.name_count += 1;
            
            // Get keys
            for rr in &set {
	        if rr.rrtype == RRType::DNSKEY {
                    let r_key  = DnsKey::from_record(&rr, &self.parser);
                    match r_key {
                        Ok(key) => {
		            self.keys.push(key);
                            self.key_count += 1;
                        }
                        Err(e) => {
                            if self.verbose {
                                println!("Invalid record {}: {}", rr, e);
                            }
                            self.invalid_rrs += 1
                        }
                    }
	        }
            }

            if nthreads > 1 && senders.len() == 0 {
                for _ in 0..nthreads {
                    let (sset_tx, sset_rx) = unbounded();
                    let keys = self.keys.clone();
                    let f_tx = failures_tx.clone();
                    senders.push(sset_tx);
                    let t = spawn(move || verify_signatures(keys, sset_rx, f_tx, verbose));
                    threads.push(t);
                }
            }

	    let mut hashed: HashMap<RRType, SignedSet> = HashMap::new();

            // Collect signatures
            for rr in &set {
                if rr.rrtype == RRType::RRSIG {
                    let rrtype = self.parser.rrtype_from_str(
                        &rr.data[0].data)?;
                    if !hashed.contains_key(&rrtype) {
                        hashed.insert(rrtype, SignedSet::new());
                    }
                    let r_sig = Signature::from_record(&rr, &self.parser, self.now_epoch, self.verbose);
                    match r_sig {
                        Ok(sig) => {
                            hashed.get_mut(&rrtype).unwrap().add_sig(sig);
                            self.sig_count += 1;
                        }
                        Err(e) => {
                            if self.verbose {
                                println!("Invalid record {}: {}", rr, e);
                            }
                            self.invalid_rrs += 1;
                        }
                    }
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
                    let wire_r = self.parser.to_wireformat(&rr);
                    match wire_r {
                        Ok(wire) => {
                            sig.add_data(wire);
                        },
                        Err(e) => {
                            // FIXME: Don't count errors twice
                            if self.verbose {
                                println!("Invalid record {}: {}", rr, e);
                            }
                            self.invalid_rrs += 1;
                        }
                    }
                }
            }

            // Validate each signature
            for sset in hashed.values_mut() {
                if nthreads > 1 {
                    senders[ti].send(sset.clone()).unwrap();
                    ti = (ti + 1)%nthreads;

                    for f in failures_rx.try_iter() {
                        self.sig_failures += f;
                    }
                }
                else {
                    self.sig_failures += verify_signature(&self.keys, sset, self.verbose);
                }
            }
        }

        // Finish threads
        if nthreads > 1 {
            for s in senders {
                drop(s);
            }

            for t in threads {
                t.join().unwrap();
            }

            for f in failures_rx.try_iter() {
                self.sig_failures += f;
            }
        }

        ThreadPoolBuilder::new().num_threads(nthreads).build_global().unwrap();
        self.nsec_chain.par_sort();

        let mut somelast: Option<&NsecLink> = None;
        self.nsec_count = self.nsec_chain.len() as u32;
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

        return Ok(());
    }
}

fn usage() {
    println!("Usage: validate_dnssec [-o origin] [-t] [-v] [-n threads] <signed zonefile>");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut origin = "";
    let mut verbose = false;
    let mut now_epoch: u32 = Utc::now().timestamp() as u32;
    let mut nthreads:usize = 1;
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
                "-n" | "--threads" => {
                    nthreads = args[arg_count + 1].parse().unwrap();
                    arg_count += 2;
                    continue;
                }
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

    match SetIterator::new(&file, origin, now_epoch, verbose) {
        Err(e) => {
            println!("{}", e);
        },
        Ok(mut si) => {
            si.check_zone(nthreads).unwrap();
            si.print_stats();
        },
    }
}
