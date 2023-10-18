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
        engine::{Engine, storage::fetch_stack}, types::Instruction
    },
    stack::{
        StackItem,
        integer::{
            IntegerData,
            serialization::UnsignedIntegerBigEndianEncoding
        },
    },
    types::{ExceptionCode, Exception, Status}
};
use std::borrow::Cow;
use everscale_types::cell::CellBuilder;
use everscale_types::models::GlobalCapability;
use sha2::Digest;

const PUBLIC_KEY_BYTES: usize = 32;
const PUBLIC_KEY_BITS: usize = PUBLIC_KEY_BYTES * 8;
const SIGNATURE_BYTES: usize = 64;
const SIGNATURE_BITS: u16 = SIGNATURE_BYTES as u16 * 8;

fn hash_to_uint(bits: impl AsRef<[u8]>) -> IntegerData {
    IntegerData::from_unsigned_bytes_be(bits)
}

/// HASHCU (c – x), computes the representation hash of a Cell c
/// and returns it as a 256-bit unsigned integer x.
pub(super) fn execute_hashcu(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("HASHCU"))?;
    fetch_stack(engine, 1)?;
    let hash_int = hash_to_uint(engine.cmd.var(0).as_cell()?.repr_hash().as_ref());
    engine.cc.stack.push(StackItem::integer(hash_int));
    Ok(())
}

/// Computes the hash of a Slice s and returns it as a 256-bit unsigned integer x.
/// The result is the same as if an ordinary cell containing only data
/// and references from s had been created and its hash computed by HASHCU.
pub(super) fn execute_hashsu(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("HASHSU"))?;
    fetch_stack(engine, 1)?;
    let mut builder = CellBuilder::new();
    builder.store_slice(engine.cmd.var(0).as_slice()?.as_ref())?;
    let cell = engine.gas_consumer.ctx(|c| builder.build_ext(c))?;
    let hash_int = hash_to_uint(cell.repr_hash().as_ref());
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
    let slice = engine.cmd.var(0).as_slice()?.as_ref();
    if slice.remaining_bits() % 8 == 0 {
        let mut bytes = [0; 32];
        let bytes = slice.get_raw(0, &mut bytes, slice.remaining_bits())?;
        let hash_int = hash_to_uint(sha2::Sha256::digest(bytes));
        engine.cc.stack.push(StackItem::integer(hash_int));
        Ok(())
    } else {
        err!(ExceptionCode::CellUnderflow)
    }
}

enum DataForSignature {
    Hash(CellBuilder),
    Slice(Vec<u8>)
}

impl AsRef<[u8]> for DataForSignature {
    fn as_ref(&self) -> &[u8] {
        match self {
            DataForSignature::Hash(hash) => hash.raw_data(),
            DataForSignature::Slice(slice) => slice.as_slice()
        }
    }
}

fn preprocess_signed_data<'a>(engine: &Engine, data: &'a [u8]) -> Cow<'a, [u8]> {
    if engine.has_capability(GlobalCapability::CapSignatureWithId) {
        let mut extended_data = Vec::with_capacity(4 + data.len());
        extended_data.extend_from_slice(&engine.signature_id().to_be_bytes());
        extended_data.extend_from_slice(data);
        return Cow::Owned(extended_data)
    }
    Cow::Borrowed(data)
}

fn check_signature(engine: &mut Engine, name: &'static str, hash: bool) -> Status {
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
    if engine.cmd.var(1).as_slice()?.as_ref().remaining_bits() < SIGNATURE_BITS {
        return err!(ExceptionCode::CellUnderflow)
    }
    let data = if hash {
        DataForSignature::Hash(engine.cmd.var(2).as_integer()?
            .as_builder::<UnsignedIntegerBigEndianEncoding>(256)?)
    } else {
        let var2 = engine.cmd.var(2).as_slice()?.as_ref();
        if var2.remaining_bits() % 8 != 0 {
            return err!(ExceptionCode::CellUnderflow)
        }
        DataForSignature::Slice(Vec::from(var2.get_raw(0, &mut [0; 128], var2.remaining_bits())?))
    };
    let pub_key = {
        let mut buffer = [0; PUBLIC_KEY_BYTES];
        pub_key.as_data_slice().get_raw(0, &mut buffer, PUBLIC_KEY_BITS as u16)?;
        match everscale_crypto::ed25519::PublicKey::from_bytes(buffer) {
            Some(pub_key) => pub_key,
            None if engine.has_capability(GlobalCapability::CapsTvmBugfixes2022) => {
                engine.cc.stack.push(boolean!(false));
                return Ok(())
            },
            None => return err!(ExceptionCode::FatalError, "cannot load public key")
        }
    };
    let mut signature = [0; SIGNATURE_BYTES];
    engine.cmd.var(1).as_slice()?.as_ref().get_raw(0, &mut signature, SIGNATURE_BITS)?;
    let data = preprocess_signed_data(engine, data.as_ref());
    let result = engine.modifiers.chksig_always_succeed || pub_key.verify(&*data, &signature);
    engine.cc.stack.push(boolean!(result));
    Ok(())
}

// CHKSIGNS (d s k – ?)
// checks whether s is a valid Ed25519-signature of the data portion of Slice d using public key k,
// similarly to CHKSIGNU. If the bit length of Slice d is not divisible by eight,
// throws a cell underflow exception. The verification of Ed25519 signatures is the standard one,
// with sha256 used to reduce d to the 256-bit number that is actually signed.
pub(super) fn execute_chksigns(engine: &mut Engine) -> Status {
    check_signature(engine, "CHKSIGNS", false)
}

/// CHKSIGNU (h s k – -1 or 0)
/// checks the Ed25519-signature s (slice) of a hash h (a 256-bit unsigned integer)
/// using public key k (256-bit unsigned integer).
pub(super) fn execute_chksignu(engine: &mut Engine) -> Status {
    check_signature(engine, "CHKSIGNU", true)
}
