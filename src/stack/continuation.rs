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

use std::{fmt, mem};

use everscale_types::cell::{Cell, CellBuilder, CellFamily, CellSlice, LoadMode};
use everscale_types::prelude::{Load, Store};

use crate::{OwnedCellSlice, types::{ExceptionCode, Result}};

use crate::{
    error::TvmError,
    executor::gas::gas_state::Gas,
    stack::{savelist::SaveList, Stack, StackItem},
    types::{Exception, ResultOpt},
};
use crate::executor::GasConsumer;
use crate::stack::SaveListDict;

use super::{DeserializeItem, items_deserialize, items_serialize, prepare_cont_serialize_vars, slice_deserialize, slice_serialize};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContinuationType {
    AgainLoopBody(OwnedCellSlice),
    TryCatch,
    CatchRevert(u32),
    Ordinary,
    PushInt(i32),
    Quit(i32),
    RepeatLoopBody(OwnedCellSlice, isize),
    UntilLoopCondition(OwnedCellSlice),
    WhileLoopCondition(OwnedCellSlice, OwnedCellSlice),
    ExcQuit,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ContinuationData {
    code: OwnedCellSlice,
    pub nargs: isize,
    pub savelist: SaveList,
    pub stack: Stack,
    pub type_of: ContinuationType,
}

impl ContinuationData {
    pub fn new_empty() -> Self {
        Self {
            code: OwnedCellSlice::empty(),
            nargs: -1,
            savelist: SaveList::new(),
            stack: Stack::new(),
            type_of: ContinuationType::Ordinary,
        }
    }

    pub fn move_without_stack(cont: &mut ContinuationData, body: OwnedCellSlice) -> Self {
        debug_assert!(cont.code.cell().is_empty());
        debug_assert!(cont.nargs < 0);
        debug_assert!(cont.savelist.is_empty());
        Self {
            code: mem::replace(&mut cont.code, body),
            nargs: -1,
            savelist: Default::default(),
            stack: Stack::new(),
            type_of: mem::replace(&mut cont.type_of, ContinuationType::Ordinary)
        }
    }

    pub fn copy_without_stack(&self) -> Self {
        Self {
            code: self.code.clone(),
            nargs: self.nargs,
            savelist: self.savelist.clone(),
            stack: Stack::new(),
            type_of: self.type_of.clone(),
        }
    }

    pub fn code(&self) -> &OwnedCellSlice {
        &self.code
    }

    pub fn code_mut(&mut self) -> &mut OwnedCellSlice {
        &mut self.code
    }

    pub fn can_put_to_savelist_once(&self, i: usize) -> bool {
        self.savelist.get(i).is_none()
    }

    pub fn move_to_end(&mut self) {
        self.code = OwnedCellSlice::empty()
    }

    pub fn put_to_savelist(&mut self, i: usize, val: &mut StackItem) -> ResultOpt<StackItem> {
        self.savelist.put(i, val)
    }

    pub fn remove_from_savelist(&mut self, i: usize) -> Option<StackItem> {
        self.savelist.remove(i)
    }

    pub fn with_code(code: OwnedCellSlice) -> Self {
        ContinuationData {
           code,
           nargs: -1,
           savelist: SaveList::new(),
           stack: Stack::new(),
           type_of: ContinuationType::Ordinary,
        }
    }

    pub fn with_type(type_of: ContinuationType) -> Self {
        ContinuationData {
           code: OwnedCellSlice::empty(),
           nargs: -1,
           savelist: SaveList::new(),
           stack: Stack::new(),
           type_of,
        }
    }

    pub fn withdraw(&mut self) -> Self {
        mem::replace(self, ContinuationData::new_empty())
    }

    pub fn drain_reference(&mut self) -> Result<Cell> {
        self.code.as_mut().load_reference_cloned()
            .map_err(|_| exception!(ExceptionCode::InvalidOpcode))
    }

    pub(crate) fn serialize(&self, gas_consumer: &mut GasConsumer) -> Result<CellBuilder> {
        let mut items = Vec::new();
        prepare_cont_serialize_vars(self, CellBuilder::new(), &mut items, false);
        items_serialize(items, gas_consumer)
    }

    pub(super) fn serialize_internal(&self, stack: CellBuilder, savelist: SaveListDict, gas_consumer: &mut GasConsumer) -> Result<CellBuilder> {
        let mut builder = CellBuilder::new();
        match &self.type_of {
            ContinuationType::AgainLoopBody(body) => {
                builder.store_small_uint(0xd, 4)?;
                let body = slice_serialize(body)?;
                let child_cell = gas_consumer.ctx(|c| body.build_ext(c))?;
                builder.store_reference(child_cell)?;
            }
            ContinuationType::TryCatch => {
                builder.store_small_uint(0x9, 4)?;
            }
            ContinuationType::CatchRevert(depth) => {
                builder.store_small_uint(0x7, 4)?;
                builder.store_u32(*depth)?;
            }
            ContinuationType::Ordinary => {
                builder.store_small_uint(0x0, 2)?;
            }
            ContinuationType::PushInt(value) => {
                builder.store_small_uint(0xf, 4)?;
                builder.store_u32(*value as u32)?;
            }
            ContinuationType::Quit(exit_code) => {
                builder.store_small_uint(0x8, 4)?;
                builder.store_u32(*exit_code as u32)?;
            }
            ContinuationType::ExcQuit => {
                builder.store_small_uint(0xb, 4)?;
            }
            ContinuationType::RepeatLoopBody(body, counter) => {
                builder.store_small_uint(0xe, 4)?;
                let body = slice_serialize(body)?;
                let child_cell = gas_consumer.ctx(|c| body.build_ext(c))?;
                builder.store_reference(child_cell)?;
                builder.store_u32(*counter as u32)?;
            }
            ContinuationType::UntilLoopCondition(body) => {
                builder.store_small_uint(0xa, 4)?;
                let body = slice_serialize(body)?;
                let child_cell = gas_consumer.ctx(|c| body.build_ext(c))?;
                builder.store_reference(child_cell)?;
            }
            ContinuationType::WhileLoopCondition(body, cond) => {
                builder.store_small_uint(0xc, 4)?;
                let mut child_cell = slice_serialize(cond)?;
                child_cell.store_builder(&slice_serialize(body)?)?;
                let child_cell = gas_consumer.ctx(|c| child_cell.build_ext(c))?;
                builder.store_reference(child_cell)?;
            }
        }
        // can be one reference

        builder.store_uint(self.nargs as u64, 22)?;
        if self.stack.is_empty() {
            builder.store_bit_zero()?;
        } else {
            builder.store_bit_one()?;
            builder.store_uint(self.stack.depth() as u64, 24)?;
            let cell = gas_consumer.ctx(|c| stack.build_ext(c))?;
            builder.store_reference(cell)?; // second ref
        }
        savelist.store_into(&mut builder, &mut Cell::empty_context())?; // third ref
        builder.store_u16(0)?; // codepage
        builder.store_builder(&slice_serialize(self.code())?)?; // last ref
        Ok(builder)
    }

    pub(crate) fn deserialize(slice: &mut CellSlice, gas_consumer: &mut GasConsumer) -> Result<Self> {
        let mut list = Vec::new();
        ContinuationData::deserialize_internal(&mut list, slice, gas_consumer)?;
        Ok(std::mem::replace(
            items_deserialize(list, gas_consumer)?.remove(0).as_continuation_mut()?,
            ContinuationData::new_empty()
        ))
    }

    pub(crate) fn deserialize_internal(
        list: &mut Vec<DeserializeItem>,
        slice: &mut CellSlice,
        gas_consumer: &mut GasConsumer
    ) -> Result<()> {
        let mut new_list = Vec::new();
        let type_of = match slice.load_small_uint(2)? {
            0 => ContinuationType::Ordinary,
            1 => {
                match slice.load_small_uint(2)? {
                    3 => {
                        let depth = slice.load_u32()?;
                        ContinuationType::CatchRevert(depth)
                    }
                    typ => return err!(ExceptionCode::UnknownError, "wrong continuation type 01{:2b}", typ)
                }
            }
            2 => {
                match slice.load_small_uint(2)? {
                    0 => {
                        let exit_code = slice.load_u32()? as i32;
                        ContinuationType::Quit(exit_code)
                    }
                    1 => ContinuationType::TryCatch,
                    2 => {
                        let mut child_slice = gas_consumer
                            .ctx(|c| c.load_dyn_cell(slice.load_reference()?, LoadMode::Full))?
                            .as_slice()?;
                        let body = slice_deserialize(child_slice.as_mut())?;
                        ContinuationType::UntilLoopCondition(body)
                    }
                    3 => ContinuationType::ExcQuit,
                    typ => return err!(ExceptionCode::UnknownError, "wrong continuation type 10{:2b}", typ)
                }
            }
            3 => {
                match slice.load_small_uint(2)? {
                    0 => {
                        let mut child_slice = gas_consumer
                            .ctx(|c| c.load_dyn_cell(slice.load_reference()?, LoadMode::Full))?
                            .as_slice()?;
                        let cond = slice_deserialize(child_slice.as_mut())?;
                        let body = slice_deserialize(child_slice.as_mut())?;
                        ContinuationType::WhileLoopCondition(body, cond)
                    }
                    1 => {
                        let mut child_slice = gas_consumer
                            .ctx(|c| c.load_dyn_cell(slice.load_reference()?, LoadMode::Full))?
                            .as_slice()?;
                        let body = slice_deserialize(child_slice.as_mut())?;
                        ContinuationType::AgainLoopBody(body)
                    }
                    2 => {
                        let mut child_slice = gas_consumer
                            .ctx(|c| c.load_dyn_cell(slice.load_reference()?, LoadMode::Full))?
                            .as_slice()?;
                        let code = slice_deserialize(child_slice.as_mut())?;
                        let counter = slice.load_u32()? as isize;
                        ContinuationType::RepeatLoopBody(code, counter)
                    }
                    3 => {
                        let value = slice.load_u32()? as i32;
                        ContinuationType::PushInt(value)
                    }
                    typ => return err!(ExceptionCode::UnknownError, "wrong continuation type 10{:2b}", typ)
                }
            }
            typ => return err!(ExceptionCode::UnknownError, "wrong continuation type {:2b}", typ)
        };

        let nargs = match slice.load_uint(22)? as isize {
            0x3fffff => -1, // 4194303
            x => x
        };
        let stack = if slice.load_bit()? {
            let length = slice.load_uint(24)? as usize;
            let cell = gas_consumer
                .ctx(|c| c.load_cell(slice.load_reference_cloned()?, LoadMode::Full))?;
            DeserializeItem::Items(length, OwnedCellSlice::new(cell)?)
        } else {
            DeserializeItem::Items(0, OwnedCellSlice::empty())
        };
        // savelist
        if slice.load_bit()? {
            let dict = SaveListDict::load_from(&mut slice.load_reference_as_slice()?)?;
            for entry in dict.iter_owned() {
                let (key, value) = entry?;
                let key = key.raw_data()[0] >> 4 ;
                new_list.push(DeserializeItem::SaveListItem(key as usize));
                new_list.push(DeserializeItem::Items(1, OwnedCellSlice::try_from(value)?));
            }
        }
        new_list.push(DeserializeItem::SaveList);
        let _codepage = slice.load_u16()?; // codepage
        let code = slice_deserialize(slice)?;
        let cont = ContinuationData {
            code,
            nargs,
            savelist: SaveList::default(),
            stack: Stack::default(),
            type_of,
        };
        list.push(DeserializeItem::Cont(cont));
        list.append(&mut new_list);
        list.push(stack);
        Ok(())
    }
}

impl ContinuationData {
    pub fn serialize_old(&self) -> Result<(CellBuilder, i64)> {
        let mut gas = 0;
        let mut builder = CellBuilder::new();
        match &self.type_of {
            ContinuationType::AgainLoopBody(body) => {
                builder.store_small_uint(0xd, 4)?;
                builder.store_reference(slice_serialize(body)?.build()?)?;
            }
            ContinuationType::TryCatch => {
                builder.store_small_uint(0x9, 4)?;
            }
            ContinuationType::Ordinary => {
                builder.store_small_uint(0x0, 2)?;
            }
            ContinuationType::PushInt(value) => {
                builder.store_small_uint(0xf, 4)?;
                builder.store_u32(*value as u32)?;
            }
            ContinuationType::Quit(exit_code) => {
                builder.store_small_uint(0x8, 4)?;
                builder.store_u32(*exit_code as u32)?;
            }
            ContinuationType::RepeatLoopBody(code, counter) => {
                builder.store_small_uint(0xe, 4)?;
                builder.store_reference(slice_serialize(code)?.build()?)?;
                builder.store_u32(*counter as u32)?;
            }
            ContinuationType::UntilLoopCondition(body) => {
                builder.store_small_uint(0xa, 4)?;
                builder.store_reference(slice_serialize(body)?.build()?)?;
            }
            ContinuationType::WhileLoopCondition(body, cond) => {
                builder.store_small_uint(0xc, 4)?;
                builder.store_reference(slice_serialize(cond)?.build()?)?;
                builder.store_reference(slice_serialize(body)?.build()?)?;
            }
            ContinuationType::ExcQuit => {
                builder.store_small_uint(0xb, 4)?;
            }
            ContinuationType::CatchRevert(_depth) => {
                // old serialization knows nothing about CatchRevert
                return err!(ExceptionCode::UnknownError)
            }
        }

        let mut stack = CellBuilder::new();
        stack.store_uint(self.stack.depth() as u64, 24)?;
        let mut stack_list = CellBuilder::new();
        for item in self.stack.iter().rev() {
            let mut cons = CellBuilder::new();
            let (serialized, gas2) = item.serialize_old()?;
            gas += gas2;
            cons.store_builder(&serialized)?;
            cons.store_reference(stack_list.build()?)?;
            gas += Gas::finalize_price();
            stack_list = cons;
        }
        stack.store_builder(&stack_list)?;

        builder.store_uint(self.nargs as u64, 22)?;
        if self.stack.depth() == 0 {
            builder.store_bit_zero()?;
        } else {
            builder.store_bit_one()?;
            builder.store_builder(&stack)?;
        }
        let (serialized, gas2) = self.savelist.serialize_old()?;
        gas += gas2;
        builder.store_builder(&serialized)?;
        builder.store_u16(0)?; // codepage
        builder.store_builder(&slice_serialize(&self.code)?)?;
        Ok((builder, gas))
    }

    pub fn deserialize_old(slice: &mut CellSlice) -> Result<(Self, i64)> {
        let mut gas = 0;
        let cont_type = match slice.load_small_uint(2)? {
            0 => Ok(ContinuationType::Ordinary),
            2 => {
                match slice.load_small_uint(2)? {
                    0 => {
                        let exit_code = slice.load_u32()? as i32;
                        Ok(ContinuationType::Quit(exit_code))
                    }
                    1 => Ok(ContinuationType::TryCatch),
                    2 => {
                        let mut body_slice = slice.load_reference_as_slice()?;
                        let body = slice_deserialize(&mut body_slice)?;
                        Ok(ContinuationType::UntilLoopCondition(body))
                    }
                    3 => {
                        Ok(ContinuationType::ExcQuit)
                    }
                    _ => err!(ExceptionCode::UnknownError)
                }
            }
            3 => {
                match slice.load_small_uint(2)? {
                    0 => {
                        let mut cond_slice = slice.load_reference_as_slice()?;
                        let cond = slice_deserialize(&mut cond_slice)?;
                        gas += Gas::load_cell_price(true);
                        let mut body_slice = slice.load_reference_as_slice()?;
                        let body = slice_deserialize(&mut body_slice)?;
                        gas += Gas::load_cell_price(true);
                        Ok(ContinuationType::WhileLoopCondition(body, cond))
                    }
                    1 => {
                        let mut body_slice = slice.load_reference_as_slice()?;
                        let body = slice_deserialize(&mut body_slice)?;
                        Ok(ContinuationType::AgainLoopBody(body))
                    }
                    2 => {
                        let mut code_slice = slice.load_reference_as_slice()?;
                        let code = slice_deserialize(&mut code_slice)?;
                        let counter = slice.load_u32()? as isize;
                        Ok(ContinuationType::RepeatLoopBody(code, counter))
                    }
                    3 => {
                        let value = slice.load_u32()? as i32;
                        Ok(ContinuationType::PushInt(value))
                    }
                    _ => err!(ExceptionCode::UnknownError)
                }
            }
            _ => err!(ExceptionCode::UnknownError)
        }?;

        let nargs = match slice.load_uint(22)? as isize {
            0x3fffff => -1,
            x => x
        };
        let stack = match slice.load_bit()? {
            false => vec![],
            true => {
                let depth = slice.load_uint(24)? as usize;
                let mut stack = vec![];
                if depth > 0 {
                    let (item, gas2) = StackItem::deserialize_old(slice)?;
                    gas += gas2;
                    stack.push(item);
                    let mut cell = slice.load_reference_cloned()?;
                    for _ in 1..depth {
                        let (item, gas2) = StackItem::deserialize_old(&mut cell.as_slice()?)?;
                        stack.push(item);
                        gas += gas2;
                        cell = slice.load_reference_cloned().unwrap_or_else(|_| Cell::empty_cell());
                    }
                }
                stack
            }
        };
        let (save, gas2) = SaveList::deserialize_old(slice)?;
        gas += gas2;
        slice.load_u16()?; // codepage
        let code = slice_deserialize(slice)?;
        gas += Gas::load_cell_price(true);
        Ok((ContinuationData {
            code,
            nargs,
            savelist: save,
            stack: Stack {
                storage: stack
            },
            type_of: cont_type
        }, gas))
    }
}

impl Default for ContinuationData {
    fn default() -> Self {
        Self::new_empty()
    }
}

impl fmt::Display for ContinuationData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{\n    type: {}\n    code: {}    nargs: {}\n    stack: ", self.type_of, self.code, self.nargs)?;
        if self.stack.depth() == 0 {
            writeln!(f, "empty")?;
        } else {
            writeln!(f)?;
            for x in self.stack.storage.iter() {
                write!(f, "        {}", x)?;
                writeln!(f)?;
            }
        }
        write!(f, "    savelist: ")?;
        if self.savelist.is_empty() {
            writeln!(f, "empty")?;
        } else {
            writeln!(f)?;
            for i in SaveList::REGS {
                if let Some(item) = self.savelist.get(i) {
                    writeln!(f, "        {}: {}", i, item)?
                }
            }
        }
        write!(f, "}}")
    }
}

impl fmt::Display for ContinuationType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            ContinuationType::AgainLoopBody(_) => "again",
            ContinuationType::TryCatch => "try-catch",
            ContinuationType::CatchRevert(_) => "catch-revert",
            ContinuationType::Ordinary => "ordinary",
            ContinuationType::PushInt(_) => "pushint",
            ContinuationType::Quit(_) => "quit",
            ContinuationType::RepeatLoopBody(_, _) => "repeat",
            ContinuationType::UntilLoopCondition(_) => "until",
            ContinuationType::WhileLoopCondition(_, _) => "while",
            ContinuationType::ExcQuit => "exception-quit",
        };
        write!(f, "{}", name)
    }
}
