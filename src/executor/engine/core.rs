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

use std::{ops::Range, sync::{Arc, Mutex}};

use everscale_types::cell::{CellSlice, LoadMode};
use everscale_types::dict::dict_get;
use everscale_types::models::{GlobalCapabilities, GlobalCapability, LibDescr, ShardAccount, SimpleLib};
use everscale_types::prelude::{Cell, CellBuilder, CellFamily, Dict, HashBytes};
use num_traits::FromPrimitive;

use crate::{
    OwnedCellSlice,
    types::{ExceptionCode, Result},
    utils::get_dictionary_opt
};

use crate::{
    error::{tvm_exception_full, TvmError, update_error_description},
    executor::{
        continuation::{switch, switch_to_c0}, engine::handlers::Handlers, gas::gas_state::Gas,
        GasConsumer, math::DivMode, microcode::{CTRL, VAR},
        types::{
            Instruction, InstructionExt, InstructionOptions, InstructionParameter, LengthAndIndex,
            RegisterPair, RegisterTrio, WhereToGetParams,
        }
    },
    smart_contract_info::SmartContractInfo,
    stack::{
        continuation::{ContinuationData, ContinuationType}, integer::IntegerData, savelist::SaveList,
        Stack, StackItem
    },
    types::{Exception, ResultMut, ResultRef, Status}
};
use crate::types::ResultOpt;

pub(super) type ExecuteHandler = fn(&mut Engine) -> Status;

pub trait IndexProvider: Send + Sync {
    fn get_accounts_by_init_code_hash(&self, hash: &HashBytes) -> Result<Vec<ShardAccount>>;
    fn get_accounts_by_code_hash(&self, hash: &HashBytes) -> Result<Vec<ShardAccount>>;
    fn get_accounts_by_data_hash(&self, hash: &HashBytes) -> Result<Vec<ShardAccount>>;
}

pub(super) struct SliceProto {
    data_window: Range<u16>,
    references_window: Range<u8>,
}

impl Default for SliceProto {
    fn default() -> Self {
        Self {
            data_window: 0..0,
            references_window: 0..0,
        }
    }
}

impl SliceProto {
    fn bits_offset(&self) -> u16 {
        self.data_window.start
    }
}

impl<'a> From<&CellSlice<'a>> for SliceProto {
    fn from(slice: &CellSlice<'a>) -> Self {
        Self {
            data_window: slice.bits_offset() ..(slice.bits_offset() + slice.remaining_bits()),
            references_window: slice.refs_offset() ..(slice.refs_offset() + slice.remaining_refs())
        }
    }
}

pub type TraceCallback = dyn Fn(&Engine, &EngineTraceInfo) + Send + Sync;

pub struct Engine {
    pub(in crate::executor) cc: ContinuationData,
    pub(in crate::executor) cmd: InstructionExt,
    pub(in crate::executor) ctrls: SaveList,
    pub(in crate::executor) index_provider: Option<Arc<dyn IndexProvider>>,
    pub(in crate::executor) modifiers: BehaviorModifiers,
    pub(in crate::executor) gas_consumer: GasConsumer,
    cstate: CommittedState,
    time: u64,
    code_page: isize,
    debug_on: isize, // status of debug can be recursively incremented
    step: u32, // number of executable command
    debug_buffer: String,
    cmd_code: SliceProto, // start of current cmd
    last_cmd: u8,
    trace: u8,
    trace_callback: Option<Arc<TraceCallback>>,
    log_string: Option<&'static str>,
    flags: u64,
    block_version: u32,
    signature_id: i32,
}

#[derive(Debug, Clone, Default)]
pub struct BehaviorModifiers {
    pub chksig_always_succeed: bool
}

#[derive(Eq, Debug, PartialEq)]
pub enum EngineTraceInfoType {
    Start,
    Normal,
    Finish,
    Implicit,
    Exception,
    Dump,
}

pub struct EngineTraceInfo<'a> {
    pub info_type: EngineTraceInfoType,
    pub step: u32, // number of executable command
    pub cmd_str: String,
    pub cmd_code: OwnedCellSlice, // start of current cmd
    pub stack: &'a Stack,
    pub gas_used: i64,
    pub gas_cmd: i64,
}

impl<'a> EngineTraceInfo<'a> {
    pub fn has_cmd(&self) -> bool {
        matches!(self.info_type, EngineTraceInfoType::Normal | EngineTraceInfoType::Implicit)
    }
}

pub struct CommittedState {
    c4: StackItem,
    c5: StackItem,
    committed: bool
}

impl CommittedState {
    pub fn new_empty() -> CommittedState {
        CommittedState {
            c4: StackItem::None,
            c5: StackItem::None,
            committed: false
        }
    }
    pub fn with_params(c4: StackItem, c5: StackItem) -> CommittedState {
        if SaveList::can_put(4, &c4) && SaveList::can_put(5, &c5) {
            CommittedState {
                c4,
                c5,
                committed: true
            }
        } else {
            debug_assert!(false);
            CommittedState::new_empty()
        }
    }
    pub fn get_actions(&self) -> &StackItem {
        &self.c5
    }
    pub fn get_root(&self) -> &StackItem {
        &self.c4
    }
    pub fn is_committed(&self) -> bool {
        self.committed
    }
}

lazy_static::lazy_static! {
    static ref HANDLERS_CP0: Handlers = Handlers::new_code_page_0();
}

impl Engine {

    pub const TRACE_NONE:  u8 = 0x00;
    pub const TRACE_CODE:  u8 = 0x01;
    pub const TRACE_GAS:   u8 = 0x02;
    pub const TRACE_STACK: u8 = 0x04;
    pub const TRACE_CTRLS: u8 = 0x08;
    pub const TRACE_ALL:   u8 = 0xFF;
    pub const TRACE_ALL_BUT_CTRLS: u8 = 0x07;

    pub (crate) const FLAG_COPYLEFTED: u64 = 0x01;

    // External API ***********************************************************

    pub fn with_capabilities(capabilities: GlobalCapabilities) -> Engine {
        let trace = if cfg!(feature="fift_check") {
            Engine::TRACE_ALL_BUT_CTRLS
        } else if cfg!(feature="verbose") {
            Engine::TRACE_ALL
        } else {
            Engine::TRACE_NONE
        };
        let log_enabled = log::log_enabled!(target: "tvm", log::Level::Debug)
            || log::log_enabled!(target: "tvm", log::Level::Trace)
            || log::log_enabled!(target: "tvm", log::Level::Info)
            || log::log_enabled!(target: "tvm", log::Level::Error)
            || log::log_enabled!(target: "tvm", log::Level::Warn);
        let trace_callback: Option<Arc<TraceCallback>> = if !log_enabled {
            None
        } else if cfg!(feature="fift_check") {
            Some(Arc::new(Self::fift_trace_callback))
        } else if cfg!(feature="verbose") {
            Some(Arc::new(Self::default_trace_callback))
        } else {
            Some(Arc::new(Self::simple_trace_callback))
        };
        Engine {
            cc: ContinuationData::new_empty(),
            cmd: InstructionExt::new("NOP"),
            ctrls: SaveList::new(),
            index_provider: None,
            modifiers: BehaviorModifiers::default(),
            gas_consumer: GasConsumer::new(capabilities),
            cstate: CommittedState::new_empty(),
            time: 0,
            code_page: 0,
            debug_on: 1,
            step: 0,
            debug_buffer: String::new(),
            cmd_code: SliceProto::default(),
            last_cmd: 0,
            trace,
            trace_callback,
            log_string: None,
            flags: 0,
            block_version: 0,
            signature_id: 0,
        }
    }

    pub fn set_block_version(&mut self, block_version: u32) {
        self.block_version = block_version
    }

    pub fn set_signature_id(&mut self, signature_id: i32) {
        self.signature_id = signature_id;
    }

    pub fn assert_ctrl(&self, ctrl: usize, item: &StackItem) -> &Engine {
        match self.ctrls.get(ctrl) {
            Some(x) => assert!(Stack::eq_item(x, item)),
            None => unreachable!("ctrl[{}] is empty", ctrl),
        }
        self
    }

    pub fn assert_stack(&self, stack: &Stack) -> &Engine {
        assert!(self.cc.stack.eq(stack));
        self
    }

    pub fn has_capability(&self, capability: GlobalCapability) -> bool {
        self.gas_consumer.has_capability(capability)
    }

    pub fn check_capability(&self, capability: GlobalCapability) -> Status {
        self.gas_consumer.check_capability(capability)
    }

    pub fn block_version(&self) -> u32 {
        self.block_version
    }

    pub fn signature_id(&self) -> i32 {
        self.signature_id
    }

    pub fn check_or_set_flags(&mut self, flags: u64) -> bool {
        if (self.flags & flags) == flags {
            true
        } else {
            self.flags |= flags;
            false
        }
    }

    pub fn eq_stack(&self, stack: &Stack) -> bool {
        self.cc.stack.eq(stack)
    }

    pub fn stack(&self) -> &Stack {
        &self.cc.stack
    }

    pub fn withdraw_stack(&mut self) -> Stack {
        std::mem::replace(&mut self.cc.stack, Stack::new())
    }

    pub fn get_stack_result_fift(&self) -> String {
        self.cc.stack.iter().map(|item| item.dump_as_fift()).collect::<Vec<_>>().join(" ")
    }

    pub fn get_committed_state_fift(&self) -> String {
        format!(" {} {}", self.cstate.c4.dump_as_fift(), self.cstate.c5.dump_as_fift())
    }

    pub fn commit(&mut self) {
        self.cstate = CommittedState::with_params(self.get_root(), self.get_actions());
    }

    pub fn steps(&self) -> u32 {
        self.step
    }

    fn is_trace_enabled(&self) -> bool {
        self.trace_callback.is_some()
    }

    fn trace_info(&self, info_type: EngineTraceInfoType, gas: i64, log_string: Option<String>) {
        if let Some(trace_callback) = self.trace_callback.as_ref() {
            // bigint param has been withdrawn during execution, so take it from the stack
            let cmd_str = if self.cmd.biginteger_raw().is_some() {
                format!("{}{} {}", self.cmd.proto.name_prefix.unwrap_or_default(),
                    self.cmd.proto.name, self.cc.stack.get(0).as_integer().unwrap_or(&IntegerData::default()))
            } else if let Some(string) = log_string {
                string
            } else if let Some(string) = self.cmd.dump_with_params() {
                string
            } else {
                String::new()
            };
            let info = EngineTraceInfo {
                info_type,
                step: self.step,
                cmd_str,
                cmd_code: self.cmd_code().unwrap_or(OwnedCellSlice::empty()),
                stack: &self.cc.stack,
                gas_used: self.gas_consumer.gas().used(),
                gas_cmd: self.gas_consumer.gas().used() - gas,
            };
            trace_callback(self, &info);
        }
    }

    fn default_trace_callback(&self, info: &EngineTraceInfo) {
        if self.trace_bit(Engine::TRACE_CODE) && info.has_cmd() {
            log::trace!(
                target: "tvm",
                "{}: {}\n{}\n",
                info.step,
                info.cmd_str,
                self.cmd_code_string()
            );
        }
        if self.trace_bit(Engine::TRACE_GAS) {
            log::trace!(
                target: "tvm",
                "Gas: {} ({})\n",
                info.gas_used,
                info.gas_cmd
            );
        }
        if self.trace_bit(Engine::TRACE_STACK) {
            log::trace!(target: "tvm", "{}", self.dump_stack("Stack trace", false));
        }
        if self.trace_bit(Engine::TRACE_CTRLS) {
            log::trace!(target: "tvm", "{}", self.dump_ctrls(true));
        }
        if info.info_type == EngineTraceInfoType::Dump {
            log::info!(target: "tvm", "{}", info.cmd_str);
        }
    }

    #[allow(dead_code)]
    fn fift_trace_callback(&self, info: &EngineTraceInfo) {
        if info.info_type == EngineTraceInfoType::Dump {
            log::info!(target: "tvm", "{}", info.cmd_str);
        } else if info.info_type == EngineTraceInfoType::Start {
            if self.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", self.dump_ctrls(true));
            }
            if self.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", self.get_stack_result_fift());
            }
            if self.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        } else if info.info_type == EngineTraceInfoType::Exception {
            if self.trace_bit(Engine::TRACE_CODE) {
                log::info!(target: "tvm", "BAD_CODE: {}\n", info.cmd_str);
            }
            if self.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", self.get_stack_result_fift());
            }
            if self.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", self.dump_ctrls(true));
            }
            if self.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        } else if info.has_cmd() {
            if self.trace_bit(Engine::TRACE_CODE) {
                log::info!(target: "tvm", "execute {}\n", info.cmd_str);
            }
            if self.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", self.get_stack_result_fift());
            }
            if self.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", self.dump_ctrls(true));
            }
            if self.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        }
    }

    #[allow(dead_code)]
    fn dump_stack_result(stack: &Stack) -> String {
        lazy_static::lazy_static!(
            static ref PREV_STACK: Mutex<Stack> = Mutex::new(Stack::new());
        );
        let mut prev_stack = PREV_STACK.lock().unwrap();
        let mut result = String::new();
        let mut iter = prev_stack.iter();
        let mut same = false;
        for item in stack.iter() {
            if let Some(prev) = iter.next() {
                if prev == item {
                    same = true;
                    continue;
                }
                while iter.next().is_some() {}
            }
            if same {
                same = false;
                result = "--\"-- ".to_string();
            }
            let string = match item {
                StackItem::None => "N".to_string(),
                StackItem::Integer(data) => match data.bitsize() {
                    Ok(0..=230) => data.to_string(),
                    Ok(bitsize) => format!("I{}", bitsize),
                    Err(err) => err.to_string()
                },
                StackItem::Cell(data) => {
                    format!("C{}-{}", data.bit_len(), data.reference_count())
                }
                StackItem::Continuation(data) => format!("T{}", data.code().as_ref().remaining_bits() / 8),
                StackItem::Builder(data) => {
                    format!("B{}-{}", data.bit_len(), data.references().len())
                }
                StackItem::Slice(data) => {
                    format!("S{}-{}", data.as_ref().remaining_bits(), data.as_ref().remaining_refs())
                }
                StackItem::Tuple(data) => match data.len() {
                    0 => "[]".to_string(),
                    len => format!("[@{}]", len),
                },
            };
            result += &string;
            result += " ";
        }
        *prev_stack = stack.clone();
        result
    }

    #[allow(dead_code)]
    pub fn simple_trace_callback(enine: &Engine, info: &EngineTraceInfo) {
        if info.info_type == EngineTraceInfoType::Dump {
            log::info!(target: "tvm", "{}", info.cmd_str);
        } else if info.info_type == EngineTraceInfoType::Start {
            if enine.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", enine.dump_ctrls(true));
            }
            if enine.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", Self::dump_stack_result(info.stack));
            }
            if enine.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        } else if info.info_type == EngineTraceInfoType::Exception {
            if enine.trace_bit(Engine::TRACE_CODE) {
                log::info!(target: "tvm", "{} ({}) BAD_CODE: {}\n", info.step, info.gas_cmd, info.cmd_str);
            }
            if enine.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", Self::dump_stack_result(info.stack));
            }
            if enine.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", enine.dump_ctrls(true));
            }
            if enine.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        } else if info.has_cmd() {
            if enine.trace_bit(Engine::TRACE_CODE) {
                log::info!(target: "tvm", "{}\n", info.cmd_str);
            }
            if enine.trace_bit(Engine::TRACE_STACK) {
                log::info!(target: "tvm", " [ {} ] \n", Self::dump_stack_result(info.stack));
            }
            if enine.trace_bit(Engine::TRACE_CTRLS) {
                log::trace!(target: "tvm", "{}", enine.dump_ctrls(true));
            }
            if enine.trace_bit(Engine::TRACE_GAS) {
                log::info!(target: "tvm", "gas - {}\n", info.gas_used);
            }
        }
    }

    pub fn execute(&mut self) -> Result<i32> {
        self.trace_info(EngineTraceInfoType::Start, 0, None);
        let result = loop {
            if let Some(result) = self.seek_next_cmd()? {
                break result
            }
            let gas = self.gas_consumer.gas().used();
            self.cmd_code = SliceProto::from(self.cc.code().as_ref());
            let execution_result = match HANDLERS_CP0.get_handler(self) {
                Err(err) => {
                    self.basic_use_gas(8);
                    Some(err)
                }
                Ok(handler) => {
                    match handler(self) {
                        Err(e) => {
                            Some(update_error_description(e, |e|
                                format!("CMD: {}{} err: {}", self.cmd.proto.name_prefix.unwrap_or_default(), self.cmd.proto.name, e)
                            ))
                        }
                        Ok(_) => self.gas_consumer.gas().check_gas_remaining().err(),
                    }
                }
            };
            self.trace_info(EngineTraceInfoType::Normal, gas, None);
            self.cmd.clear();
            if let Some(err) = execution_result {
                if self.has_capability(GlobalCapability::CapsTvmBugfixes2022) {
                    self.raise_exception_bugfix0(err)?;
                } else {
                    self.raise_exception(err)?;
                }
            }
        };
        self.trace_info(EngineTraceInfoType::Finish, self.gas_consumer.gas().used(), Some("NORMAL TERMINATION".to_string()));
        self.commit();
        Ok(result)
    }

    fn step_next_ref(&mut self, reference: Cell) -> Result<Option<i32>> {
        self.step += 1;
        self.log_string = Some("IMPLICIT JMPREF");
        self.gas_consumer.gas_mut().try_use_gas(Gas::implicit_jmp_price())?;
        let code = self.gas_consumer.ctx(|c| c.load_cell(reference, LoadMode::Full))?;
        *self.cc.code_mut() = OwnedCellSlice::new(code)?;
        Ok(None)
    }
    fn step_ordinary(&mut self) -> Result<Option<i32>> {
        self.step += 1;
        self.log_string = Some("implicit RET");
        self.gas_consumer.gas_mut().try_use_gas(Gas::implicit_ret_price())?;
        if self.ctrls.get(0).is_none() {
            return Ok(Some(0))
        }
        switch_to_c0(self)?;
        Ok(None)
    }
    fn step_pushint(&mut self, code: i32) -> Result<Option<i32>> {
        self.step += 1;
        self.log_string = Some("implicit PUSHINT");
        self.cc.stack.push(int!(code));
        switch(self, ctrl!(0))?;
        Ok(None)
    }
    fn step_try_catch(&mut self) -> Result<Option<i32>> {
        self.step += 1;
        self.log_string = Some("IMPLICIT RET FROM TRY-CATCH");
        self.gas_consumer.gas_mut().try_use_gas(Gas::implicit_ret_price())?;
        self.ctrls.remove(2);
        switch(self, ctrl!(0))?;
        Ok(None)
    }
    fn step_catch_revert(&mut self, depth: u32) -> Result<Option<i32>> {
        self.step += 1;
        self.log_string = Some("IMPLICIT CATCH REVERT");
        // save exception pair
        let exc_pair = self.cc.stack.drop_range_straight(0..2)?;
        // revert stack depth to the state before try-catch
        let cur_depth = self.cc.stack.depth();
        if cur_depth < depth as usize {
            return err!(ExceptionCode::StackUnderflow)
        }
        self.cc.stack.drop_top(cur_depth - depth as usize);
        // restore exception pair
        for item in exc_pair {
            self.cc.stack.push(item);
        }
        switch(self, ctrl!(0))?;
        Ok(None)
    }
    fn step_while_loop(&mut self, body: OwnedCellSlice, cond: OwnedCellSlice) -> Result<Option<i32>> {
        match self.check_while_loop_condition() {
            Ok(true) => {
                self.log_string = Some("NEXT WHILE ITERATION");
                self.discharge_nargs();
                let mut cond = ContinuationData::with_code(cond);
                let mut while_ = ContinuationData::move_without_stack(&mut self.cc, body);
                while_.savelist.put_opt(0, self.ctrl_mut(0)?);
                cond.savelist.put_opt(0, &mut StackItem::continuation(while_));
                self.ctrls.put_opt(0, &mut StackItem::continuation(cond));
            }
            Ok(false) => {
                self.log_string = Some("RET FROM WHILE");
                switch(self, ctrl!(0))?;
            }
            Err(err) => {
                if self.has_capability(GlobalCapability::CapsTvmBugfixes2022) {
                    let quit = ContinuationType::Quit(ExceptionCode::NormalTermination as i32);
                    self.ctrls.put(0, &mut StackItem::continuation(ContinuationData::with_type(quit)))?;
                }
                return Err(err)
            }
        }
        Ok(None)
    }
    fn step_repeat_loop(&mut self, body: OwnedCellSlice) -> Result<Option<i32>> {
        if let ContinuationType::RepeatLoopBody(_, ref mut counter) = self.cc.type_of {
            if *counter > 1 {
                *counter -= 1;
                self.log_string = Some("NEXT REPEAT ITERATION");
                self.discharge_nargs();
                let mut repeat = ContinuationData::move_without_stack(&mut self.cc, body);
                repeat.savelist.put_opt(0, self.ctrl_mut(0)?);
                self.ctrls.put_opt(0, &mut StackItem::continuation(repeat));
            } else {
                self.log_string = Some("RET FROM REPEAT");
                switch(self, ctrl!(0))?;
            }
        }
        Ok(None)
    }
    fn step_until_loop(&mut self, body: OwnedCellSlice) -> Result<Option<i32>> {
        match self.check_until_loop_condition() {
            Ok(true) => {
                self.log_string = Some("NEXT UNTIL ITERATION");
                self.discharge_nargs();
                let mut until = ContinuationData::move_without_stack(&mut self.cc, body);
                until.savelist.put_opt(0, self.ctrl_mut(0)?);
                self.ctrls.put_opt(0, &mut StackItem::continuation(until));
            }
            Ok(false) => {
                self.log_string = Some("RET FROM UNTIL");
                switch(self, ctrl!(0))?;
            }
            Err(err) => return Err(err)
        }
        Ok(None)
    }
    fn step_again_loop(&mut self, body: OwnedCellSlice) -> Result<Option<i32>> {
        self.log_string = Some("NEXT AGAIN ITERATION");
        self.discharge_nargs();
        let again = ContinuationData::move_without_stack(&mut self.cc, body);
        self.ctrls.put_opt(0, &mut StackItem::continuation(again));
        Ok(None)
    }

    fn discharge_nargs(&mut self) {
        if self.has_capability(GlobalCapability::CapsTvmBugfixes2022) && self.cc.nargs != -1 {
            let depth = self.cc.stack.depth();
            let _ = self.cc.stack.drop_range_straight((depth - self.cc.nargs as usize)..depth);
            self.cc.nargs = -1;
        }
    }

    fn make_external_error(&mut self) -> Result<Option<i32>> {
        let number = self.cc.stack.drop(0)?.as_integer()?.into(0..=0xffff)?;
        if number == ExceptionCode::NormalTermination as usize ||
            number == ExceptionCode::AlternativeTermination as usize {
            return Ok(Some(number as i32))
        }
        let value = match self.cc.stack.drop(0) {
            Ok(item) => item.as_integer().cloned().unwrap_or_default(),
            Err(_) => IntegerData::zero()
        };
        let exception = match ExceptionCode::from_usize(number) {
            Some(code) => Exception::from_code_and_value(code, value, file!(), line!()),
            None => Exception::from_number_and_value(number, StackItem::int(value), file!(), line!())
        };
        Err(error!(TvmError::TvmExceptionFull(exception, String::new())))
    }

    // return Ok(Some(exit_code)) - if you want to stop execution
    pub(in crate::executor) fn seek_next_cmd(&mut self) -> Result<Option<i32>> {
        while self.cc.code().as_ref().remaining_bits() == 0 {
            let gas = self.gas_consumer.gas().used();
            self.log_string = None;
            let result = if let Some(reference) = self.cc.code().as_ref().get_reference_cloned(0).ok() {
                self.step_next_ref(reference)
            } else {
                match self.cc.type_of.clone() {
                    ContinuationType::Ordinary => self.step_ordinary(),
                    ContinuationType::PushInt(code) => self.step_pushint(code),
                    ContinuationType::Quit(exit_code) => Ok(Some(exit_code)),
                    ContinuationType::TryCatch => self.step_try_catch(),
                    ContinuationType::WhileLoopCondition(body, cond) => self.step_while_loop(body, cond),
                    ContinuationType::RepeatLoopBody(code, _counter) => self.step_repeat_loop(code),
                    ContinuationType::UntilLoopCondition(body) => self.step_until_loop(body),
                    ContinuationType::AgainLoopBody(slice) => self.step_again_loop(slice),
                    ContinuationType::ExcQuit => Ok(self.make_external_error()?),
                    ContinuationType::CatchRevert(depth) => self.step_catch_revert(depth),
                }
            };
            if self.is_trace_enabled() {
                if let Some(log_string) = self.log_string {
                    self.trace_info(EngineTraceInfoType::Implicit, gas, Some(log_string.to_string()));
                }
            }
            match self.gas_consumer.gas().check_gas_remaining().and(result) {
                Ok(None) => (),
                Ok(Some(exit_code)) => return Ok(Some(exit_code)),
                Err(err) => {
                    if self.has_capability(GlobalCapability::CapsTvmBugfixes2022) {
                        match self.raise_exception_bugfix0(err) {
                            Ok(Some(exit_code)) => return Ok(Some(exit_code)),
                            Ok(None) => (),
                            Err(err) => return Err(err)
                        }
                    } else {
                        self.raise_exception(err)?
                    }
                }
            }
        }
        Ok(None)
    }


    pub fn get_committed_state(&self) -> &CommittedState {
        &self.cstate
    }

    pub fn get_actions(&self) -> StackItem {
        match self.ctrls.get(5) {
            Some(x) => x.clone(),
            None => StackItem::None,
        }
    }

    fn get_root(&self) -> StackItem {
        match self.ctrls.get(4) {
            Some(x) => x.clone(),
            None => StackItem::None,
        }
    }

    pub fn ctrl(&self, index: usize) -> ResultRef<StackItem> {
        self.ctrls.get(index)
            .ok_or_else(|| exception!(ExceptionCode::RangeCheckError, "get ctrl {} failed", index))
    }

    pub fn ctrl_mut(&mut self, index: usize) -> ResultMut<StackItem> {
        self.ctrls.get_mut(index)
            .ok_or_else(|| exception!(ExceptionCode::RangeCheckError, "get ctrl {} failed", index))
    }

    pub fn ctrls(&self) -> &SaveList {
        &self.ctrls
    }

    pub fn cc(&self) -> &ContinuationData {
        &self.cc
    }

    fn dump_msg(message: &'static str, data: String) -> String {
        format!("--- {} {:-<4$}\n{}\n{:-<40}\n", message, "", data, "", 35-message.len())
    }

    pub fn dump_ctrls(&self, short: bool) -> String {
        Self::dump_msg("Control registers", SaveList::REGS.iter()
            .filter_map(|i| self.ctrls.get(*i).map(|item| if !short {
                format!("{}: {}", i, item)
            } else if *i == 3 {
                "3: copy of CC".to_string()
            } else if *i == 7 {
                "7: SmartContractInfo".to_string()
            } else if let StackItem::Continuation(x) = item {
                format!("{}: {:?}", i, x.type_of)
            } else {
                format!("{}: {}", i, item.dump_as_fift())
            })).collect::<Vec<_>>().join("\n")
        )
    }

    pub fn dump_stack(&self, message: &'static str, short: bool) -> String {
        Self::dump_msg(message, self.cc.stack.iter()
            .map(|item| if !short {
                format!("{}", item)
            } else {
                item.dump_as_fift()
            })
            .collect::<Vec<_>>().join("\n")
        )
    }

    // TODO: check if it should be in SmartContractInfo
    pub fn set_local_time(&mut self, time: u64) {
        self.time = time
    }

    pub fn set_trace(&mut self, trace_mask: u8) {
        self.trace = trace_mask
    }

    pub fn set_trace_callback(&mut self, callback: impl Fn(&Engine, &EngineTraceInfo) + Send + Sync + 'static) {
        self.trace_callback = Some(Arc::new(callback));
    }

    pub fn set_arc_trace_callback(&mut self, callback: Arc<TraceCallback>) {
        self.trace_callback = Some(callback);
    }

    pub fn trace_bit(&self, trace_mask: u8) -> bool {
        (self.trace & trace_mask) == trace_mask
    }

    pub fn set_index_provider(&mut self, index_provider: Arc<dyn IndexProvider>) {
        self.index_provider = Some(index_provider)
    }

    pub fn behavior_modifiers(&self) -> &BehaviorModifiers {
        &self.modifiers
    }

    pub fn modify_behavior(&mut self, modifiers: &BehaviorModifiers) {
        self.modifiers = modifiers.clone();
    }

    pub fn set_libraries(
        &mut self,
        account_libs: &Dict<HashBytes, SimpleLib>,
        shared_libs: &Dict<HashBytes, LibDescr>
    ) -> Result<()> {
        Ok(self.gas_consumer.set_libraries(account_libs, shared_libs)?)
    }

    pub fn setup(
        mut self,
        code: OwnedCellSlice,
        mut ctrls: Option<SaveList>,
        stack: Option<Stack>,
        gas: Gas,
    ) -> Result<Self> {
        *self.cc.code_mut() = code.clone();
        self.cmd_code = SliceProto::from(self.cc.code().as_ref());
        if let Some(stack) = stack {
            self.cc.stack = stack;
        }
        *self.gas_consumer.gas_mut() = gas;
        let cont = ContinuationType::Quit(ExceptionCode::NormalTermination as i32);
        self.ctrls.put(0, &mut StackItem::continuation(ContinuationData::with_type(cont)))?;
        let cont = ContinuationType::Quit(ExceptionCode::AlternativeTermination as i32);
        self.ctrls.put(1, &mut StackItem::continuation(ContinuationData::with_type(cont)))?;
        if self.has_capability(GlobalCapability::CapsTvmBugfixes2022) {
            self.ctrls.put(2, &mut StackItem::continuation(ContinuationData::with_type(ContinuationType::ExcQuit)))?;
        }
        self.ctrls.put(3, &mut StackItem::continuation(ContinuationData::with_code(code.clone())))?;
        self.ctrls.put(4, &mut StackItem::cell(Cell::empty_cell()))?;
        self.ctrls.put(5, &mut StackItem::cell(Cell::empty_cell()))?;
        self.ctrls.put(7, &mut SmartContractInfo::old_default(code.into_cell()?).into_temp_data_item())?;
        if let Some(ref mut ctrls) = ctrls {
            self.ctrls.apply(ctrls);
        }
        Ok(self)
    }

    // Internal API ***********************************************************

    #[allow(dead_code)]
    pub(in crate::executor) fn local_time(&mut self) -> u64 {
        self.time += 1;
        self.time
    }

    // Implementation *********************************************************

    pub(in crate::executor) fn load_instruction(&mut self, proto: Instruction) -> Status {
        self.cmd.proto = proto;
        self.cmd.params.clear();
        self.cmd.vars.clear();
        self.step += 1;
        self.extract_instruction()
    }

    pub(in crate::executor) fn switch_debug(&mut self, on_off: bool) {
        self.debug_on += if on_off {1} else {-1}
    }

    pub(in crate::executor) fn debug(&self) -> bool {
        self.debug_on > 0 && self.is_trace_enabled()
    }

    pub(in crate::executor) fn dump(&mut self, dump: &str) {
        self.debug_buffer += dump;
    }

    pub(in crate::executor) fn flush(&mut self) {
        if self.debug_on > 0 {
            let buffer = std::mem::take(&mut self.debug_buffer);
            if self.trace_callback.is_none() {
                log::info!(target: "tvm", "{}", buffer);
            } else {
                self.trace_info(EngineTraceInfoType::Dump, 0, Some(buffer));
            }
        } else {
            self.debug_buffer = String::new()
        }
    }

    /// Get gas state outside of VM, for executor
    pub fn gas(&self) -> &Gas {
        &self.gas_consumer.gas()
    }

    fn check_while_loop_condition(&mut self) -> Result<bool> {
        let x = self.cc.stack.drop(0)?;
        let y = x.as_integer()?;
        Ok(!y.is_zero())
    }

    fn check_until_loop_condition(&mut self) -> Result<bool> {
        Ok(!self.check_while_loop_condition()?)
    }

    fn extract_slice(&mut self, offset: usize, r: usize, x: usize, refs: usize, bytes: usize) -> Result<OwnedCellSlice> {
        let offset = offset as u16;
        let r = r as u16;
        let x = x as u16;
        let mut refs = refs as u8;
        let mut bytes = bytes as u16;

        let mut code = self.cmd_code()?;
        let mut slice = code.clone();
        if offset >= slice.as_ref().remaining_bits() {
            return err!(ExceptionCode::InvalidOpcode)
        }
        slice.as_mut().advance(offset, 0)?;
        if r != 0 {
            refs += slice.as_mut().load_uint(r)? as u8;
        }
        if x != 0 {
            bytes += slice.as_mut().load_uint(x)? as u16;
        }
        let mut shift = 8 * bytes + offset + r + x + 7;
        let remainder = shift % 8;
        shift -= remainder;
        if (slice.as_ref().remaining_bits() < shift - r - x - offset)
            || (slice.as_ref().remaining_refs() < refs) {
            return err!(ExceptionCode::InvalidOpcode)
        }
        code.as_mut().advance(shift, refs)?;
        *self.cc.code_mut() = code;

        slice.as_mut().shrink(Some(shift - r - x - offset), Some(refs))?;

        Ok(slice)
    }

    fn basic_use_gas(&mut self, mut bits: usize) -> i64 {
        let higher = self.cc.code().as_ref().bits_offset();
        bits += higher.saturating_sub(self.cmd_code.bits_offset()) as usize;
        self.gas_consumer.gas_mut().use_gas(Gas::basic_gas_price(bits, 0))
    }

    fn extract_instruction(&mut self) -> Status {
        match self.cmd.proto.opts {
            Some(InstructionOptions::ArgumentConstraints) => {
                let param = self.next_cmd()?;
                self.basic_use_gas(0);
                self.cmd.params.push(
                    InstructionParameter::Pargs(((param >> 4) & 0x0F) as usize)
                );
                self.cmd.params.push(
                    InstructionParameter::Nargs(
                        if (param & 0x0F) == 15 {
                            -1
                        } else {
                            (param & 0x0F) as isize
                        }
                    )
                )
            },
            Some(InstructionOptions::ArgumentAndReturnConstraints) => {
                let param = self.next_cmd()?;
                self.basic_use_gas(0);
                self.cmd.params.push(
                    InstructionParameter::Pargs(((param >> 4) & 0x0F) as usize)
                );
                self.cmd.params.push(
                    InstructionParameter::Rargs((param & 0x0F) as usize)
                )
            },
            Some(InstructionOptions::BigInteger) => {
                self.basic_use_gas(5);

                let bigint = IntegerData::from_big_endian_octet_stream(|| self.next_cmd())?;
                self.cmd.params.push(InstructionParameter::BigInteger(bigint))
            }
            Some(InstructionOptions::ControlRegister) => {
                self.basic_use_gas(0);
                let creg = (self.last_cmd() & 0x0F) as usize;
                if !SaveList::REGS.contains(&creg) {
                    return err!(ExceptionCode::RangeCheckError)
                }
                self.cmd.params.push(
                    InstructionParameter::ControlRegister(creg)
                )
            },
            Some(InstructionOptions::DivisionMode) => {
                let mode = DivMode::with_flags(self.next_cmd()?);
                if mode.shift_parameter() {
                    let len = self.next_cmd()? as usize + 1;
                    self.cmd.params.push(InstructionParameter::Length(len))
                }
                self.basic_use_gas(0);
                self.cmd.proto.name = mode.command_name()?;
                self.cmd.params.push(InstructionParameter::DivisionMode(mode));
            },
            Some(InstructionOptions::Integer(ref range)) => {
                let number = if *range == (-32768..32768) {
                    self.basic_use_gas(16);
                    (((self.next_cmd()? as i16) << 8) | (self.next_cmd()? as i16)) as isize
                } else if *range == (-128..128) {
                    self.basic_use_gas(8);
                    (self.next_cmd()? as i8) as isize
                } else if *range == (-5..11) {
                    self.basic_use_gas(0);
                    match self.last_cmd() & 0x0F {
                        value @ 0..=10 => value as isize,
                        value => value as isize - 16
                    }
                } else if *range == (0..32) {
                    self.basic_use_gas(0);
                    (self.last_cmd() & 0x1F) as isize
                } else if *range == (0..64) {
                    self.basic_use_gas(0);
                    (self.last_cmd() % 64) as isize
                } else if *range == (0..2048) {
                    self.basic_use_gas(8);
                    let hi = (self.last_cmd() as i16) & 0x07;
                    let lo = self.next_cmd()? as i16;
                    (hi * 256 + lo) as isize
                } else if *range == (0..16384) {
                    self.basic_use_gas(8);
                    let hi = (self.last_cmd() as i16) & 0x3F;
                    let lo = self.next_cmd()? as i16;
                    (hi * 256 + lo) as isize
                } else if *range == (0..256) {
                    self.basic_use_gas(8);
                    self.next_cmd()? as isize
                } else if *range == (0..15) {
                    self.basic_use_gas(0);
                    match self.last_cmd() & 0x0F {
                        15 => return err!(ExceptionCode::RangeCheckError),
                        value => value as isize
                    }
                } else if *range == (1..15) {
                    self.basic_use_gas(0);
                    match self.last_cmd() & 0x0F {
                        0 | 15 => return err!(ExceptionCode::RangeCheckError),
                        value => value as isize
                    }
                } else if *range == (-15..240) {
                    self.basic_use_gas(0);
                    match self.last_cmd() {
                        value @ 0..=240 => value as isize,
                        value @ 0xF1..=0xFF => value as isize - 256,
                    }
                } else {
                    return err!(ExceptionCode::RangeCheckError)
                };
                self.cmd.params.push(InstructionParameter::Integer(number))
            },
            Some(InstructionOptions::Length(ref range)) => {
                if *range == (0..16) {
                    self.cmd.params.push(
                        InstructionParameter::Length((self.last_cmd() & 0x0F) as usize)
                    )
                } else if *range == (0..4) {
                    let length = self.last_cmd() & 3;
                    self.cmd.params.push(InstructionParameter::Length(length as usize))
                } else if *range == (1..32) {
                    let length = self.last_cmd() & 0x1F;
                    self.cmd.params.push(InstructionParameter::Length(length as usize))
                }
                else {
                    return err!(ExceptionCode::RangeCheckError)
                }
                self.basic_use_gas(0);
            },
            Some(InstructionOptions::LengthAndIndex) => {
                self.basic_use_gas(0);
                // This is currently needed only for special-case BLKPUSH command and works the same way
                // as InstructionOptions::StackRegisterPair(WhereToGetParams::GetFromLastByte)
                let params = self.last_cmd();
                let (length, index) = (params >> 4, params & 0x0F);
                self.cmd.params.push(
                    InstructionParameter::LengthAndIndex(
                        LengthAndIndex {
                            length: length as usize,
                            index: index as usize
                        }
                    )
                )
            },
            Some(InstructionOptions::LengthMinusOne(ref range)) => {
                let len = if *range == (0..8) {
                    self.last_cmd() & 0x07
                } else if *range == (0..256) {
                    self.next_cmd()?
                } else {
                    return err!(ExceptionCode::RangeCheckError)
                } as usize + 1;
                self.cmd.params.push(
                    InstructionParameter::Length(len)
                );
                self.basic_use_gas(0);
            },
            Some(InstructionOptions::LengthMinusOneAndIndexMinusOne) => {
                let params = self.next_cmd()?;
                self.basic_use_gas(0);
                let (l_minus_1, i_minus_1) = (params >> 4, params & 0x0F);
                self.cmd.params.push(
                    InstructionParameter::LengthAndIndex(
                        LengthAndIndex {
                            length: (l_minus_1 + 1) as usize,
                            index: (i_minus_1 + 1) as usize
                        }
                    )
                )
            },
            Some(InstructionOptions::LengthMinusTwoAndIndex) => {
                let params = self.next_cmd()?;
                self.basic_use_gas(0);
                let (l_minus_2, i) = (params >> 4, params & 0x0F);
                self.cmd.params.push(
                    InstructionParameter::LengthAndIndex(
                        LengthAndIndex {
                            length: (l_minus_2 + 2) as usize,
                            index: i as usize
                        }
                    )
                )
            },
            Some(InstructionOptions::Pargs(ref range)) => {
                if *range == (0..16) {
                    self.cmd.params.push(
                        InstructionParameter::Pargs((self.last_cmd() & 0x0F) as usize)
                    )
                } else {
                    return err!(ExceptionCode::RangeCheckError)
                }
                self.basic_use_gas(0);
            },
            Some(InstructionOptions::Rargs(ref range)) => {
                if *range == (0..16) {
                    self.cmd.params.push(
                        InstructionParameter::Rargs((self.last_cmd() & 0x0F) as usize)
                    )
                } else {
                    return err!(ExceptionCode::RangeCheckError)
                }
                self.basic_use_gas(0);
            },
            Some(InstructionOptions::StackRegister(ref range)) => {
                if *range == (0..16) {
                    self.cmd.params.push(
                        InstructionParameter::StackRegister((self.last_cmd() & 0x0F) as usize)
                    )
                } else if *range == (0..256) {
                    let reg = self.next_cmd()? as usize;
                    self.cmd.params.push(
                        InstructionParameter::StackRegister(reg)
                    )
                } else {
                    return err!(ExceptionCode::RangeCheckError)
                }
                self.basic_use_gas(0);
            },
            Some(InstructionOptions::StackRegisterPair(ref place)) => {
                let (ra, rb) = match place {
                    WhereToGetParams::GetFromLastByte2Bits => {
                        let opcode_ra_rb = self.last_cmd();
                        ((opcode_ra_rb >> 2) & 0x03, opcode_ra_rb & 0x03)
                    }
                    WhereToGetParams::GetFromLastByte => {
                        let opcode_ra_rb = self.last_cmd();
                        ((opcode_ra_rb & 0xF0) >> 4, opcode_ra_rb & 0x0F)
                    }
                    WhereToGetParams::GetFromNextByte => {
                        let ra_rb = self.next_cmd()?;
                        ((ra_rb & 0xF0) >> 4, ra_rb & 0x0F)
                    }
                    WhereToGetParams::GetFromNextByteLong => {
                        let rb = self.next_cmd()?;
                        (0,rb)
                    }
                    _ => (0, 0)
                };
                self.basic_use_gas(0);
                self.cmd.params.push(
                    InstructionParameter::StackRegisterPair(
                        RegisterPair {
                            ra: ra as usize,
                            rb: rb as usize
                        }
                    )
                )
            },
            Some(InstructionOptions::StackRegisterTrio(ref place)) => {
                let last = self.last_cmd();
                let (ra, rb, rc) = match place {
                    WhereToGetParams::GetFromLastByte2Bits => {
                        // INDEX3 2 bits per index
                        ((last >> 4) & 0x03, (last >> 2) & 0x03, last & 0x03)
                    }
                    _ => {
                        // Three-arguments functions are 2-byte 4ijk XCHG3 instructions
                        // And 54[0-7]ijk long-form XCHG3 - PUSH3
                        // We assume that in the second case 0x54 byte is already consumed,
                        // and we have to deal with *ijk layout for arguments
                        let rb_rc = self.next_cmd()?;
                        (last & 0x0F, rb_rc >> 4, rb_rc & 0x0F)
                    }
                };
                self.basic_use_gas(0);
                self.cmd.params.push(
                    InstructionParameter::StackRegisterTrio(
                        RegisterTrio {
                            ra: ra as usize,
                            rb: rb as usize,
                            rc: rc as usize
                        }
                    )
                )
            }
            Some(InstructionOptions::Dictionary(offset, bits)) => {
                self.gas_consumer.gas_mut().use_gas(Gas::basic_gas_price(offset + 1 + bits, 0));
                let mut code = self.cmd_code()?;
                code.as_mut().advance(offset as u16, 0)?;
                // TODO: need to check this failure case
                let slice = get_dictionary_opt(&mut code).ok().flatten().unwrap_or(OwnedCellSlice::empty());
                self.cmd.params.push(InstructionParameter::Slice(slice));
                let length = code.as_mut().load_uint(bits as u16)? as usize;
                *self.cc.code_mut() = code;
                self.cmd.params.push(InstructionParameter::Length(length))
            }
            Some(InstructionOptions::Bytestring(offset, r, x, bytes)) => {
                self.gas_consumer.gas_mut().use_gas(Gas::basic_gas_price(offset + r + x, 0));
                let slice = self.extract_slice(offset, r, x, 0, bytes)?;
                if slice.as_ref().remaining_bits() % 8 != 0 {
                    return err!(ExceptionCode::InvalidOpcode)
                }
                self.cmd.params.push(InstructionParameter::Slice(slice))
            }
            Some(InstructionOptions::Bitstring(offset, r, x, refs)) => {
                self.gas_consumer.gas_mut().use_gas(Gas::basic_gas_price(offset + r + x, 0));
                let mut slice = self.extract_slice(offset, r, x, refs, 0)?;
                Self::rtrim_slice(&mut slice)?;
                self.cmd.params.push(InstructionParameter::Slice(slice));
            }
            None => { self.basic_use_gas(0); }
        }
        Ok(())
    }

    // raises the exception and tries to dispatch it via c(2).
    // If c(2) is not set, returns that exception, otherwise, returns None
    fn raise_exception(&mut self, err: anyhow::Error) -> Status {
        let exception = match tvm_exception_full(&err) {
            Some(exception) => exception,
            None => {
                log::trace!(target: "tvm", "BAD CODE: {}\n", self.cmd_code_string());
                return Err(err)
            }
        };
        if exception.exception_code().is_some() {
            self.step += 1;
        }
        if exception.exception_code() == Some(ExceptionCode::OutOfGas) {
            log::trace!(target: "tvm", "OUT OF GAS CODE: {}\n", self.cmd_code_string());
            return Err(err)
        }
        if let Err(err) = self.gas_consumer.gas_mut().try_use_gas(Gas::exception_price()) {
            self.step += 1;
            return Err(err);
        }
        let n = self.cmd.vars.len();
        // self.trace_info(EngineTraceInfoType::Exception, self.gas_used(), Some(format!("EXCEPTION: {}", err)));
        if let Some(c2) = self.ctrls.get_mut(2) {
            self.cc.stack.push(exception.value.clone());
            self.cc.stack.push(int!(exception.exception_or_custom_code()));
            c2.as_continuation_mut()?.nargs = 2;
            switch(self, ctrl!(2))?;
        } else if let Some(number) = exception.is_normal_termination() {
            let cont = ContinuationData::with_type(ContinuationType::Quit(number));
            self.cmd.push_var(StackItem::continuation(cont));
            self.cc.stack.push(exception.value);
            self.cmd.vars[n].as_continuation_mut()?.nargs = 1;
            switch(self, var!(n))?;
        } else {
            let log_string = Some(format!("UNHANDLED EXCEPTION: {}", err));
            self.trace_info(EngineTraceInfoType::Exception, self.gas_consumer.gas().used(), log_string);
            return Err(err)
        }
        Ok(())
    }

    // raises the exception and tries to dispatch it via c(2).
    // If c(2) is not set, returns that exception, otherwise, returns None
    fn raise_exception_bugfix0(&mut self, err: anyhow::Error) -> Result<Option<i32>> {
        let exception = match tvm_exception_full(&err) {
            Some(exception) => exception,
            None => {
                log::trace!(target: "tvm", "BAD CODE: {}\n", self.cmd_code_string());
                return Err(err)
            }
        };
        if exception.exception_code().is_some() {
            self.step += 1;
        }
        if exception.exception_code() == Some(ExceptionCode::OutOfGas) {
            log::trace!(target: "tvm", "OUT OF GAS CODE: {}\n", self.cmd_code_string());
            return Err(err)
        }
        if let Err(err) = self.gas_consumer.gas_mut().try_use_gas(Gas::exception_price()) {
            self.step += 1;
            return Err(err);
        }
        let n = self.cmd.vars.len();
        // self.trace_info(EngineTraceInfoType::Exception, self.gas_used(), Some(format!("EXCEPTION: {}", err)));
        let c2 = self.ctrls.remove(2).ok_or(err)?;
        if let Ok(c2) = c2.as_continuation() {
            if c2.type_of == ContinuationType::ExcQuit {
                if let Some(exit_code) = exception.is_normal_termination() {
                    let cont = ContinuationData::with_type(ContinuationType::Quit(exit_code));
                    self.cmd.push_var(StackItem::Continuation(Arc::new(cont)));
                    self.cc.stack.push(exception.value);
                    self.cmd.vars[n].as_continuation_mut()?.nargs = 1;
                    switch(self, var!(n))?;
                    return Ok(None)
                } else {
                    self.cc.stack = Stack::new();
                    self.cc.stack.push(exception.value.clone());
                    self.cc.stack.push(int!(exception.exception_or_custom_code()));
                    return Err(error!(TvmError::TvmExceptionFull(exception, String::new())))
                }
            }
        }
        self.cmd.push_var(c2);
        self.cc.stack.push(exception.value.clone());
        self.cc.stack.push(int!(exception.exception_or_custom_code()));
        let target = self.cmd.vars[n].as_continuation_mut()?;
        match target.type_of {
            ContinuationType::CatchRevert(_depth) => {
                // Pass the entire cc stack. CatchRevert cont will remove a range of slots
                // under the exception pair so that the final stack depth is _depth + 2.
            }
            _ => target.nargs = 2
        }
        switch(self, var!(n))?;
        Ok(None)
    }

    /// trim zeros from right to first one
    fn rtrim_slice(slice: &mut OwnedCellSlice) -> Result<()> {
        let s = slice.as_ref();
        let mut remaining_bits = s.remaining_bits();
        for offset in (0..remaining_bits).rev() {
            if s.get_bit(offset).ok() == Some(true) {
                remaining_bits = offset;
                break
            }
        }
        slice.as_mut().shrink(Some(remaining_bits), None)?;
        Ok(())
    }

    pub(in crate::executor) fn last_cmd(&self) -> u8 {
        self.last_cmd
    }

    pub(in crate::executor) fn next_cmd(&mut self) -> Result<u8> {
        match self.cc.code_mut().as_mut().load_u8() {
            Ok(cmd) => {
                self.last_cmd = cmd;
                Ok(cmd)
            }
            Err(_) => err!(
                ExceptionCode::InvalidOpcode,
                "remaining bits expected >= 8, but actual value is: {}",
                self.cc.code().as_ref().remaining_bits()
            )
        }
    }

    fn cmd_code_string(&self) -> String {
        match self.cmd_code() {
            Ok(code) => code.to_string(),
            Err(err) => err.to_string()
        }
    }
    fn cmd_code(&self) -> Result<OwnedCellSlice> {
        let mut code = OwnedCellSlice::new(self.cc.code().cell().clone())?;
        let data = &self.cmd_code.data_window;
        let refs = &self.cmd_code.references_window;
        code.as_mut().advance(data.start, refs.start)?;
        code.as_mut().shrink(Some(data.end - data.start), Some(refs.end - refs.start))?;
        Ok(code)
    }

    /// Set code page for interpret bytecode. now only code page 0 is supported
    pub(in crate::executor) fn code_page_mut(&mut self) -> &mut isize {
        &mut self.code_page
    }

    /// get smartcontract info param from ctrl(7) tuple index 0
    pub(in crate::executor) fn smci_param(&self, index: usize) -> ResultRef<StackItem> {
        let tuple = self.ctrl(7)?.as_tuple()?;
        let tuple = tuple.first()
            .ok_or_else(|| exception!(ExceptionCode::RangeCheckError, "tuple has no items"))?
            .as_tuple()?;
        tuple.get(index)
            .ok_or_else(|| exception!(ExceptionCode::RangeCheckError, "tuple has {} items, but want {}", tuple.len(), index))
    }

    pub(in crate::executor) fn rand(&self) -> ResultRef<IntegerData> {
        self.smci_param(6)?.as_integer()
    }

    pub(in crate::executor) fn set_rand(&mut self, rand: IntegerData) -> Status {
        let mut tuple = self.ctrl_mut(7)?.as_tuple_mut()?;
        let t1 = match tuple.first_mut() {
            Some(t1) => t1,
            None => return err!(ExceptionCode::RangeCheckError, "set tuple index is {} but length is {}", 0, tuple.len())
        };
        let mut t1_items = t1.as_tuple_mut()?;
        match t1_items.get_mut(6) {
            Some(v) => *v = StackItem::int(rand),
            None => return err!(ExceptionCode::RangeCheckError, "set tuple index is {} but length is {}", 6, t1_items.len())
        }
        self.gas_consumer.gas_mut().use_gas(Gas::tuple_gas_price(t1_items.len()));
        *t1 = StackItem::tuple(t1_items);
        self.gas_consumer.gas_mut().use_gas(Gas::tuple_gas_price(tuple.len()));
        *self.ctrl_mut(7)? = StackItem::tuple(tuple);
        Ok(())
    }

    pub(crate) fn get_config_param(&mut self, index: i32) -> ResultOpt<Cell> {
        let StackItem::Cell(ref data) = self.smci_param(9)?.clone() else {
            return Ok(None)
        };
        let mut builder = CellBuilder::new();
        builder.store_u32(index as u32)?;
        let Some(cell) = self.gas_consumer.ctx(|c| dict_get(Some(&data), 32, builder.as_data_slice(), c))? else {
            return Ok(None)
        };
        Ok(cell.get_reference_cloned(0).map(Some)?)
    }
}