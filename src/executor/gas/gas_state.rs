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

use crate::{error::TvmError, types::{Exception, Result, ExceptionCode}};
use std::cmp::min;

/// [everscale_types::models::transaction::ExecutedComputePhase]
/// induces strict limits on values per TLB schema
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Gas {
    gas_limit_max: u64, // limits gas_used => valuable 56 bits
    gas_limit: u64, // stored 56 bits
    gas_credit: u32, // stored 24 bits
    gas_used: u64, // stored 56 bits
    gas_price: u64,
    gas_base: u64, // limits gas_used => valuable 56 bits
}

const CELL_LOAD_GAS_PRICE: u64 = 100;
const CELL_RELOAD_GAS_PRICE: u64 = 25;
const CELL_CREATE_GAS_PRICE: u64 = 500;
const EXCEPTION_GAS_PRICE: u64 = 50;
const TUPLE_ENTRY_GAS_PRICE: u64 = 1;
const IMPLICIT_JMPREF_GAS_PRICE: u64 = 10;
const IMPLICIT_RET_GAS_PRICE: u64 = 5;
const FREE_STACK_DEPTH: usize = 32;
const STACK_ENTRY_GAS_PRICE: u64 = 1;
// const MAX_DATA_DEPTH: usize = 512;

impl Gas {
    /// Instance for release
    pub const fn new(gas_limit: u64, gas_credit: u32, gas_limit_max: u64, gas_price: u64) -> Gas {
        Gas {
            gas_price,
            gas_limit,
            gas_limit_max,
            gas_used: 0,
            gas_credit,
            gas_base: gas_limit + gas_credit as u64,
        }
    }
    /// Compute instruction cost
    pub const fn basic_gas_price(instruction_length: usize, _instruction_references_count: usize) -> u64 {
        // old formula from spec: (10 + instruction_length + 5 * instruction_references_count) as u64
        (10 + instruction_length) as u64
    }

    /// Compute exception cost
    pub const fn exception_price() -> u64 {
        EXCEPTION_GAS_PRICE
    }

    /// Compute exception cost
    pub const fn finalize_price() -> u64 {
        CELL_CREATE_GAS_PRICE
    }

    /// Implicit JMP cost
    pub const fn implicit_jmp_price() -> u64 {
        IMPLICIT_JMPREF_GAS_PRICE
    }

    /// Implicit RET cost
    pub const fn implicit_ret_price() -> u64 {
        IMPLICIT_RET_GAS_PRICE
    }

    /// Compute exception cost
    pub const fn load_cell_price(first: bool) -> u64 {
        if first {CELL_LOAD_GAS_PRICE} else {CELL_RELOAD_GAS_PRICE}
    }

    /// Stack cost
    pub const fn stack_price(stack_depth: usize) -> u64 {
        let depth = if stack_depth > FREE_STACK_DEPTH {
            stack_depth
        } else {
            FREE_STACK_DEPTH
        };
        STACK_ENTRY_GAS_PRICE * (depth - FREE_STACK_DEPTH) as u64
    }

    /// Compute tuple usage cost
    pub const fn tuple_gas_price(tuple_length: usize) -> u64 {
        TUPLE_ENTRY_GAS_PRICE * tuple_length as u64
    }

    /// Set input gas to gas limit
    pub fn new_gas_limit(&mut self, gas_limit: u64) {
        self.gas_limit = min(gas_limit, self.gas_limit_max);
        self.gas_credit = 0;
        self.gas_base = self.gas_limit;
    }

    /// Update remaining gas limit
    pub fn use_gas(&mut self, gas: u64) {
        self.gas_used += gas;
    }

    /// Try to consume gas then raise exception out of gas if needed
    pub fn try_use_gas(&mut self, gas: u64) -> Result<()> {
        self.gas_used += gas;
        self.check_gas_remaining()
    }

    /// Raise out of gas exception
    pub fn check_gas_remaining(&self) -> Result<()> {
        if self.gas_base >= self.gas_used {
            Ok(())
        } else {
            Err(exception!(ExceptionCode::OutOfGas, self.remaining(), "check_gas_remaining"))
        }
    }

    pub const fn limit(&self) -> u64 {
        self.gas_limit
    }
    pub const fn credit(&self) -> u32 {
        self.gas_credit
    }
    pub const fn price(&self) -> u64 {
        self.gas_price
    }
    pub const fn remaining(&self) -> i64 {
        if self.gas_base >= self.gas_used {
            (self.gas_base - self.gas_used) as i64
        } else {
            -((self.gas_used - self.gas_base) as i64)
        }
    }

    pub const fn used(&self) -> u64 {
        self.gas_used
    }

    pub const fn vm_total_used(&self) -> u64 {
        if self.gas_base >= self.gas_used {
            self.gas_used
        } else {
            self.gas_base
        }
    }
}
