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

use everscale_types::cell::{CellBuilder, CellSlice, HashBytes, LoadMode};
use everscale_types::error::Error;
use everscale_types::models::{
    ChangeLibraryMode, CurrencyCollection, ExtraCurrencyCollection, GlobalCapability, IntAddr,
    Lazy, LibRef, OutAction, ReserveCurrencyFlags, SendMsgFlags
};
use everscale_types::num::Tokens;
use everscale_types::prelude::{Cell, CellFamily, Load, Store};
use num::{BigInt, bigint::Sign};

use crate::utils::CellSliceExt;
use crate::{OwnedCellSlice, types::{Result, ExceptionCode}};

use crate::{
    error::TvmError,
    executor::{
        engine::{Engine, storage::fetch_stack}, GasConsumer,
        types::Instruction,
    },
    stack::{
        integer::{
            behavior::OperationBehavior, IntegerData,
            serialization::UnsignedIntegerBigEndianEncoding,
        },
        StackItem,
    },
    types::{Exception, Status},
};

fn get_bigint(slice: &CellSlice) -> Result<BigInt> {
    let bits = slice.size_bits();
    if bits == 0 {
        Ok(BigInt::from(0))
    } else if bits < 256 {
        Ok(BigInt::from_bytes_be(Sign::Plus, &slice.get_raw(0, &mut [0; 32], bits)?) << (256 - bits))
    } else {
        Ok(BigInt::from_bytes_be(Sign::Plus, &slice.get_raw(0, &mut [0; 32], 256)?))
    }
}


// Blockchain related instructions ********************************************

fn add_action(engine: &mut Engine, action: &OutAction) -> Status {
    let mut new_action = CellBuilder::new();
    let c5 = engine.ctrls.get(5).ok_or(ExceptionCode::TypeCheckError)?;
    new_action.store_reference(c5.as_cell()?.clone())?;
    action.store_into(&mut new_action, &mut Cell::empty_context())?;
    let cell = engine.gas_consumer.ctx(|c| new_action.build_ext(c))?;
    engine.ctrls.put(5, &mut StackItem::Cell(cell))?;
    Ok(())
}

/// CHANGELIB (h x - )
pub(super) fn execute_changelib(engine: &mut Engine) -> Status {
    engine.check_capability(GlobalCapability::CapSetLibCode)?;
    engine.load_instruction(Instruction::new("CHANGELIB"))?;
    fetch_stack(engine, 2)?;
    let x = engine.cmd.var(0).as_integer()?.into(0..=2)? as u8;
    let hash = engine.cmd.var(1).as_integer()?.as_builder::<UnsignedIntegerBigEndianEncoding>(256)?;
    let action = OutAction::ChangeLibrary {
        mode: ChangeLibraryMode::try_from(x)?,
        lib: LibRef::Hash(HashBytes::from_slice(hash.raw_data()))
    };
    add_action(engine, &action)
}

/// SENDRAWMSG (c x – ): pop mode and message cell from stack and put it at the
/// end of output actions list.
pub(super) fn execute_sendrawmsg(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SENDRAWMSG"))?;
    fetch_stack(engine, 2)?;
    let x = engine.cmd.var(0).as_integer()?.into(0..=255)?;
    let cell = engine.cmd.var(1).as_cell()?.clone();
    let action = OutAction::SendMsg {
        mode: SendMsgFlags::from_bits(x).ok_or(error!(Error::InvalidData))?,
        out_msg: Lazy::from_raw(cell),
    };
    add_action(engine, &action)
}

/// SETCODE (c - )
pub(super) fn execute_setcode(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("SETCODE"))?;
    fetch_stack(engine, 1)?;
    let cell = engine.cmd.var(0).as_cell()?.clone();
    let action = OutAction::SetCode { new_code: cell };
    add_action(engine, &action)
}

/// SETLIBCODE (c x - )
pub(super) fn execute_setlibcode(engine: &mut Engine) -> Status {
    engine.check_capability(GlobalCapability::CapSetLibCode)?;
    engine.load_instruction(Instruction::new("SETLIBCODE"))?;
    fetch_stack(engine, 2)?;
    let x = engine.cmd.var(0).as_integer()?.into(0..=2)?;
    let cell = engine.cmd.var(1).as_cell()?.clone();
    let action = OutAction::ChangeLibrary {
        mode: ChangeLibraryMode::try_from(x)?,
        lib: LibRef::Cell(cell)
    };
    add_action(engine, &action)
}

/// COPYLEFT (s n - )
pub(super) fn execute_copyleft(engine: &mut Engine) -> Status {
    engine.check_capability(GlobalCapability::CapCopyleft)?;
    if engine.check_or_set_flags(Engine::FLAG_COPYLEFTED) {
        return Err(ExceptionCode::IllegalInstruction.into());
    }
    engine.load_instruction(Instruction::new("COPYLEFT"))?;

    let mut myaddr_slice = engine.smci_param(8)?.as_slice()?.clone();
    let myaddr = IntAddr::load_from(myaddr_slice.as_mut())?;
    fetch_stack(engine, 2)?;
    if !myaddr.is_masterchain() {
        let num = engine.cmd.var(0).as_integer()?.into(0..=255)?;
        let slice = engine.cmd.var(1).as_slice()?;
        if slice.as_ref().size_bits() != 256 {
            return Err(ExceptionCode::TypeCheckError.into());
        }
        let action = OutAction::CopyLeft {
            license: num,
            address: slice.as_ref().get_u256(0)?,
        };
        add_action(engine, &action)
    } else {
        Ok(())
    }
}

/// RAWRESERVE (x y - )
pub(super) fn execute_rawreserve(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("RAWRESERVE"))?;
    fetch_stack(engine, 2)?;
    let y = engine.cmd.var(0).as_integer()?.into(0..=15)?;
    let x = engine.cmd.var(1).as_grams()?;
    let action = OutAction::ReserveCurrency {
        mode: ReserveCurrencyFlags::from_bits(y).ok_or(error!(Error::InvalidData))?,
        value: CurrencyCollection::new(x),
    };
    add_action(engine, &action)
}

/// RAWRESERVEX (s y - )
pub(super) fn execute_rawreservex(engine: &mut Engine) -> Status {
    engine.load_instruction(Instruction::new("RAWRESERVEX"))?;
    fetch_stack(engine, 3)?;
    let y = engine.cmd.var(0).as_integer()?.into(0..=15)?;
    let other = engine.cmd.var(1).as_dict()?.cloned();
    let x = engine.cmd.var(2).as_grams()?;
    let action = OutAction::ReserveCurrency {
        mode: ReserveCurrencyFlags::from_bits(y).ok_or(error!(Error::InvalidData))?,
        value: CurrencyCollection{ tokens: Tokens::new(x), other: ExtraCurrencyCollection::from_raw(other) },
    };
    add_action(engine, &action)
}

pub(super) fn execute_ldmsgaddr<T: OperationBehavior>(engine: &mut Engine) -> Status {
    engine.load_instruction(
        Instruction::new(if T::quiet() {"LDMSGADDRQ"} else {"LDMSGADDR"})
    )?;
    fetch_stack(engine, 1)?;
    let mut slice = engine.cmd.var(0).as_slice()?.clone();
    let mut remainder = slice.clone();
    if parse_address(&mut remainder).is_ok() {
        let (bits_to_move, refs_to_move) = {
            let remainder = remainder.as_ref();
            let slice = slice.as_ref();
            let bits_to_move = remainder.offset_bits() - slice.offset_bits();
            let refs_to_move = remainder.offset_refs() - slice.offset_refs();
            (bits_to_move, refs_to_move)
        };
        slice.as_mut().shrink(Some(bits_to_move), Some(refs_to_move))?;
        engine.cc.stack.push(StackItem::Slice(slice));
        engine.cc.stack.push(StackItem::Slice(remainder));
        if T::quiet() {
            engine.cc.stack.push(boolean!(true));
        }
        Ok(())
    } else if T::quiet() {
        let var = engine.cmd.pop_var()?;
        engine.cc.stack.push(var);
        engine.cc.stack.push(boolean!(false));
        Ok(())
    } else {
        err!(ExceptionCode::CellUnderflow)
    }
}

fn load_address<F, T>(engine: &mut Engine, name: &'static str, op: F) -> Status
where F: FnOnce(Vec<StackItem>, &mut GasConsumer) -> Result<Vec<StackItem>>, T: OperationBehavior {
    engine.load_instruction(Instruction::new(name))?;
    fetch_stack(engine, 1)?;
    let mut slice = engine.cmd.var(0).as_slice()?.clone();
    let mut result = false;
    if let Ok(addr) = parse_address(&mut slice) {
        if let Ok(mut stack) = op(addr, &mut engine.gas_consumer) {
            stack.drain(..).for_each(|var| {engine.cc.stack.push(var);});
            result = true;
        }
    }
    if T::quiet() {
        engine.cc.stack.push(boolean!(result));
        Ok(())
    } else if result {
        Ok(())
    } else {
        err!(ExceptionCode::CellUnderflow)
    }
}

pub(super) fn execute_parsemsgaddr<T: OperationBehavior>(engine: &mut Engine) -> Status {
    load_address::<_, T>(engine, if T::quiet() {"PARSEMSGADDRQ"} else {"PARSEMSGADDR"},
        |tuple, _| Ok(vec![StackItem::tuple(tuple)])
    )
}

// (s - x y) compose rewrite_pfx and address to a 256 bit integer
pub(super) fn execute_rewrite_std_addr<T: OperationBehavior>(engine: &mut Engine) -> Status {
    load_address::<_, T>(engine, if T::quiet() {"REWRITESTDADDRQ"} else {"REWRITESTDADDR"}, |tuple, _| {
        if tuple.len() == 4 {
            let addr = tuple[3].as_slice()?;
            let mut y = match addr.as_ref().size_bits() {
                256 => IntegerData::from(get_bigint(addr.as_ref())?)?,
                _ => return err!(ExceptionCode::CellUnderflow)
            };
            if tuple[1].is_slice() {
                let rewrite_pfx = tuple[1].as_slice()?;
                let bits = rewrite_pfx.as_ref().size_bits();
                if bits > 256 {
                    return err!(ExceptionCode::CellUnderflow)
                } else if bits > 0 {
                    let prefix = IntegerData::from(get_bigint(rewrite_pfx.as_ref())?)?;
                    let mask = IntegerData::mask((256 - bits) as usize);
                    y = y.and::<T>(&mask)?.or::<T>(&prefix)?;
                }
            };
            let x = tuple[2].clone();
            Ok(vec![x, StackItem::int(y)])
        } else {
            err!(ExceptionCode::CellUnderflow)
        }
    })
}

// (s - x s') compose rewrite_pfx and address to a slice
pub(super) fn execute_rewrite_var_addr<T: OperationBehavior>(engine: &mut Engine) -> Status {
    load_address::<_, T>(engine, if T::quiet() {"REWRITEVARADDRQ"} else {"REWRITEVARADDR"}, |tuple, gas_consumer| {
        if tuple.len() == 4 {
            let mut addr = tuple[3].as_slice()?.clone();
            if let Ok(rewrite_pfx) = tuple[1].as_slice() {
                let pfx_bits = rewrite_pfx.as_ref().size_bits();
                if pfx_bits > addr.as_ref().size_bits() {
                    return err!(ExceptionCode::CellUnderflow)
                } else if pfx_bits > 0 {
                    let mut b = CellBuilder::new();
                    b.store_slice_data(rewrite_pfx.as_ref())?;
                    addr.as_mut().skip_first(pfx_bits, 0)?;
                    b.store_slice_data(addr.as_ref())?;
                    let cell = gas_consumer.ctx(|c| b.build_ext(c))?;
                    addr = OwnedCellSlice::new(
                        gas_consumer.ctx(|c| c.load_cell(cell, LoadMode::Full))?
                    )?;
                }
            };
            let x = tuple[2].clone();
            Ok(vec![x, StackItem::Slice(addr)])
        } else {
            err!(ExceptionCode::CellUnderflow)
        }
    })
}

fn read_rewrite_pfx(slice: &mut OwnedCellSlice) -> Result<Option<OwnedCellSlice>> {
    match slice.as_mut().load_bit()? {
        true => {
            let len = slice.as_mut().load_small_uint(5)? as u16;
            Ok(Some(get_next_slice(slice, len)?))
        }
        false => Ok(None)
    }
}

fn get_next_slice(slice: &mut OwnedCellSlice, bit_len: u16) -> Result<OwnedCellSlice> {
    let mut result = slice.clone();
    result.as_mut().shrink(Some(bit_len), Some(0))?;
    slice.as_mut().skip_first(bit_len, 0)?;
    Ok(result)
}

fn parse_address(slice: &mut OwnedCellSlice) -> Result<Vec<StackItem>> {
    let addr_type = slice.as_mut().load_small_uint(2)?;
    let mut tuple = vec!(int!(addr_type));
    match addr_type & 0b11 {
        0b00 => (),
        0b01 => {
            let len = slice.as_mut().load_uint(9)? as u16;
            tuple.push(StackItem::Slice(get_next_slice(slice, len)?));
        }
        0b10 => {
            tuple.push(match read_rewrite_pfx(slice)? {
                Some(slice) => StackItem::Slice(slice),
                None => StackItem::None
            });
            tuple.push(int!(slice.as_mut().load_u8()? as i8));
            tuple.push(StackItem::Slice(get_next_slice(slice, 256)?));
        }
        0b11 => {
            tuple.push(match read_rewrite_pfx(slice)? {
                Some(slice) => StackItem::Slice(slice),
                None => StackItem::None
            });
            let len = slice.as_mut().load_uint(9)? as u16;
            tuple.push(int!(slice.as_mut().load_u32()? as i32));
            tuple.push(StackItem::Slice(get_next_slice(slice, len)?));
        }
        _ => ()
    }
    Ok(tuple)
}
