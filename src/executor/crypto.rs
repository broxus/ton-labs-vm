/*
* Copyright (C) 2019-2021 TON Labs. All Rights Reserved.
*
* Licensed under the SOFTWARE EVALUATION License (the "License"); you may not use
* this file except in compliance with the License.
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific TON DEV software governing permissions and
* limitations under the License.
*/

use crate::{
    error::TvmError,
    executor::{
        engine::{Engine, SignatureDomain, storage::fetch_stack},
        gas::gas_state::Gas,
        types::Instruction
    },
    stack::{
        StackItem,
        integer::{
            IntegerData,
            serialization::UnsignedIntegerBigEndianEncoding
        },
    },
    types::{Exception, Status}
};
use ed25519::signature::Verifier;
use std::borrow::Cow;
use sha2::{Digest, Sha256};
use ton_block::GlobalCapabilities;
use ton_types::{BuilderData, error, GasConsumer, ExceptionCode, Result, UInt256, SliceData};

const PUBLIC_KEY_BITS:  usize = PUBLIC_KEY_BYTES * 8;
const SIGNATURE_BITS:   usize = SIGNATURE_BYTES * 8;
const PUBLIC_KEY_BYTES: usize = ed25519_dalek::PUBLIC_KEY_LENGTH;
const SIGNATURE_BYTES:  usize = ed25519_dalek::SIGNATURE_LENGTH;
const SIGNATURE_DOMAIN_L2_TLB_TAG: u32 = 0x71b34ee1;
const SIGNATURE_DOMAIN_EMPTY_TLB_TAG: u32 = 0x0e1d571b;

fn hash_to_uint(bits: impl AsRef<[u8]>) -> IntegerData {
    IntegerData::from_unsigned_bytes_be(bits)
}

/// HASHCU (c – x), computes the representation hash of a Cell c
/// and returns it as a 256-bit unsigned integer x.
pub(super) fn execute_hashcu(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("HASHCU"))?;
    fetch_stack(engine, 1)?;
    let hash_int = hash_to_uint(engine.cmd.var(0).as_cell()?.repr_hash());
    engine.cc.stack.push(StackItem::integer(hash_int));
    Ok(())
}

/// Computes the hash of a Slice s and returns it as a 256-bit unsigned integer x.
/// The result is the same as if an ordinary cell containing only data
/// and references from s had been created and its hash computed by HASHCU.
pub(super) fn execute_hashsu(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("HASHSU"))?;
    fetch_stack(engine, 1)?;
    let builder = BuilderData::from_slice(engine.cmd.var(0).as_slice()?);
    let cell = engine.finalize_cell(builder)?;
    let hash_int = hash_to_uint(cell.repr_hash());
    engine.cc.stack.push(StackItem::integer(hash_int));
    Ok(())
}

// SHA256U ( s – x )
// Computes sha256 of the data bits of Slices.
// If the bit length of s is not divisible by eight, throws a cell underflow exception.
// The hash value is returned as a 256-bit unsigned integer x.
pub(super) fn execute_sha256u(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SHA256U"))?;
    fetch_stack(engine, 1)?;
    let slice = engine.cmd.var(0).as_slice()?;
    if slice.remaining_bits() % 8 == 0 {
        let hash = UInt256::calc_file_hash(&slice.get_bytestring(0));
        let hash_int = hash_to_uint(hash);
        engine.cc.stack.push(StackItem::integer(hash_int));
        Ok(())
    } else {
        err!(ExceptionCode::CellUnderflow)
    }
}

pub(super) fn execute_hash_ext(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("HASHEXT_SHA256"))?;
    fetch_stack(engine, 2)?;

    let cnt = engine.cmd.var(0).as_integer()?.into(0..=u8::MAX)?;
    if cnt != 1 {
        return err!(ExceptionCode::TypeCheckError)
    }

    let builder = engine.cmd.var(1).as_builder()?.clone();
    let slice = SliceData::load_builder(builder)?;

    if slice.remaining_bits() % 8 == 0 {
        let hash_id = engine.last_cmd();
        if hash_id != 0 {
            return err!(ExceptionCode::TypeCheckError)
        }

        let hash: [u8; 32] = Sha256::digest(&slice.get_bytestring(0)).into();
        let hash_int = hash_to_uint(hash);
        engine.cc.stack.push(StackItem::integer(hash_int));
        Ok(())
    } else {
        err!(ExceptionCode::CellUnderflow)
    }
}

pub(super) fn execute_hash_extr(_engine: &mut Engine) -> Status {
    err!(ExceptionCode::FatalError)
}

pub(super) fn execute_hash_exta(_engine: &mut Engine) -> Status {
    err!(ExceptionCode::FatalError)
}

pub(super) fn execute_hash_extar(_engine: &mut Engine) -> Status {
    err!(ExceptionCode::FatalError)
}

enum DataForSignature {
    Hash(BuilderData),
    Slice(Vec<u8>)
}

impl AsRef<[u8]> for DataForSignature {
    fn as_ref(&self) -> &[u8] {
        match self {
            DataForSignature::Hash(hash) => hash.data(),
            DataForSignature::Slice(slice) => slice.as_slice()
        }
    }
}

fn preprocess_signed_data<'a>(engine: &Engine, data: &'a [u8], can_use_id: bool) -> Cow<'a, [u8]> {
    if !can_use_id {
        return Cow::Borrowed(data)
    }

    let signature_id_enabled = engine.check_capabilities(GlobalCapabilities::CapSignatureWithId as u64);
    if !engine.modifiers.enable_signature_domains {
        if signature_id_enabled {
            let mut extended_data = Vec::with_capacity(4 + data.len());
            extended_data.extend_from_slice(&engine.signature_id().to_be_bytes());
            extended_data.extend_from_slice(data);
            return Cow::Owned(extended_data)
        }
        return Cow::Borrowed(data)
    }

    let signature_domain = match engine.signature_domain() {
        Some(signature_domain) => signature_domain,
        // fallback to signature_id
        None if signature_id_enabled => {
            SignatureDomain::L2 { global_id: engine.signature_id() }
        }
        None => SignatureDomain::Empty
    };

    if let SignatureDomain::Empty = signature_domain {
        return Cow::Borrowed(data)
    }

    let mut extended_data = Vec::with_capacity(32 + data.len());
    extended_data.extend_from_slice(&signature_domain_tl_hash(signature_domain));
    extended_data.extend_from_slice(data);
    Cow::Owned(extended_data)
}

fn signature_domain_tl_hash(signature_domain: SignatureDomain) -> [u8; 32] {
    let mut raw = Vec::with_capacity(match signature_domain {
        SignatureDomain::Empty => 4,
        SignatureDomain::L2 { .. } => 8
    });
    match signature_domain {
        SignatureDomain::Empty => {
            raw.extend_from_slice(&SIGNATURE_DOMAIN_EMPTY_TLB_TAG.to_le_bytes());
        }
        SignatureDomain::L2 { global_id } => {
            raw.extend_from_slice(&SIGNATURE_DOMAIN_L2_TLB_TAG.to_le_bytes());
            raw.extend_from_slice(&global_id.to_le_bytes());
        }
    }
    Sha256::digest(&raw).into()
}

fn check_signature(engine: &mut Engine, name: &'static str, hash: bool, can_use_id: bool) -> Status {
    engine.load_instruction(Instruction::new(name))?;
    fetch_stack(engine, 3)?;
    let pub_key = engine.cmd.var(0).as_integer()?
        .as_builder::<UnsignedIntegerBigEndianEncoding>(PUBLIC_KEY_BITS)?;
    engine.cmd.var(1).as_slice()?;
    if hash {
        engine.cmd.var(2).as_integer()?;
    } else {
        engine.cmd.var(2).as_slice()?;
    }
    if engine.cmd.var(1).as_slice()?.remaining_bits() < SIGNATURE_BITS {
        return err!(ExceptionCode::CellUnderflow)
    }
    let data = if hash {
        DataForSignature::Hash(engine.cmd.var(2).as_integer()?
            .as_builder::<UnsignedIntegerBigEndianEncoding>(256)?)
    } else {
        if engine.cmd.var(2).as_slice()?.remaining_bits() % 8 != 0 {
            return err!(ExceptionCode::CellUnderflow)
        }
        DataForSignature::Slice(engine.cmd.var(2).as_slice()?.get_bytestring(0))
    };
    let pub_key = match ed25519_dalek::PublicKey::from_bytes(pub_key.data()) {
        Ok(pub_key) => pub_key,
        Err(err) => if engine.check_capabilities(GlobalCapabilities::CapsTvmBugfixes2022 as u64) {
                engine.cc.stack.push(boolean!(false));
                return Ok(())
            } else {
                return err!(ExceptionCode::FatalError, "cannot load public key {}", err)
            }
    };
    let signature = engine.cmd.var(1).as_slice()?.get_bytestring(0);
    let signature = match ed25519::signature::Signature::from_bytes(&signature[..SIGNATURE_BYTES]) {
        Ok(signature) => signature,
        Err(err) => {
            #[allow(clippy::collapsible_else_if)]
            if engine.check_capabilities(GlobalCapabilities::CapsTvmBugfixes2022 as u64) {
                engine.cc.stack.push(boolean!(false));
                return Ok(())
            } else {
                if hash {
                    engine.cc.stack.push(boolean!(false));
                    return Ok(())
                } else {
                    return err!(ExceptionCode::FatalError, "cannot load signature {}", err)
                }
            }
        }
    };
    let data = preprocess_signed_data(engine, data.as_ref(), can_use_id);
    let result =
        engine.modifiers.chksig_always_succeed || pub_key.verify(&data, &signature).is_ok();
    engine.cc.stack.push(boolean!(result));
    Ok(())
}

// CHKSIGNS (d s k – ?)
// checks whether s is a valid Ed25519-signature of the data portion of Slice d using public key k,
// similarly to CHKSIGNU. If the bit length of Slice d is not divisible by eight,
// throws a cell underflow exception. The verification of Ed25519 signatures is the standard one,
// with sha256 used to reduce d to the 256-bit number that is actually signed.
pub(super) fn execute_chksigns(engine: &mut Engine) -> Status {
    check_signature(engine, "CHKSIGNS", false, true)
}

/// CHKSIGNU (h s k – -1 or 0)
/// checks the Ed25519-signature s (slice) of a hash h (a 256-bit unsigned integer)
/// using public key k (256-bit unsigned integer).
pub(super) fn execute_chksignu(engine: &mut Engine) -> Status {
    check_signature(engine, "CHKSIGNU", true, true)
}

/// ED25519_CHKSIGNS (d s k – ?)
/// checks Ed25519 signature in legacy mode without signature-id or signature-domain prefix.
pub(super) fn execute_ed25519_chksigns(engine: &mut Engine) -> Status {
    check_signature(engine, "ED25519_CHKSIGNS", false, false)
}

pub(super) fn execute_signature_domain(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SIGNDOMAIN"))?;
    let domain = engine.signature_domain().unwrap_or(SignatureDomain::Empty);
    engine.cc.stack.push(domain_to_stack_item(domain));
    Ok(())
}

pub(super) fn execute_pop_signature_domain(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SIGNDOMAIN_POP"))?;
    engine.use_gas(Gas::tuple_gas_price(engine.signature_domains_len()));
    let domain = engine.pop_signature_domain();
    engine.cc.stack.push(domain_to_stack_item(domain));
    Ok(())
}

pub(super) fn execute_push_signature_domain(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SIGNDOMAIN_PUSH"))?;
    fetch_stack(engine, 1)?;
    let domain = domain_from_stack_item(engine.cmd.var(0))?;
    engine.push_signature_domain(domain);
    engine.use_gas(Gas::tuple_gas_price(engine.signature_domains_len()));
    Ok(())
}

fn domain_to_stack_item(domain: SignatureDomain) -> StackItem {
    match domain {
        SignatureDomain::Empty => StackItem::None,
        SignatureDomain::L2 { global_id } => int!(global_id)
    }
}

fn domain_from_stack_item(item: &StackItem) -> Result<SignatureDomain> {
    if item.is_null() {
        return Ok(SignatureDomain::Empty)
    }
    let global_id = item.as_integer()?.into(i32::MIN..=i32::MAX)?;
    Ok(SignatureDomain::L2 { global_id })
}