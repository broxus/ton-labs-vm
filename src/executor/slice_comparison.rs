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

use everscale_types::cell::CellSlice;
use crate::types::Result;

use crate::{
    executor::{engine::{Engine, storage::fetch_stack}, types::Instruction},
    stack::{integer::IntegerData, StackItem}, types::Status,
};

fn unary<F>(engine: &mut Engine, name: &'static str, operation: F) -> Status
    where
        F: Fn(&CellSlice) -> StackItem
{
    engine.load_instruction(
        Instruction::new(name)
    )?;
    fetch_stack(engine, 1)?;
    let slice = engine.cmd.var(0).as_slice()?.clone();
    let r = operation(&slice.as_ref());
    engine.cc.stack.push(r);
    Ok(())
}

fn binary<F>(engine: &mut Engine, name: &'static str, operation: F) -> Status
    where
        F: Fn(&CellSlice, &CellSlice) -> Result<StackItem>
{
    engine.load_instruction(
        Instruction::new(name)
    )?;
    fetch_stack(engine, 2)?;
    let s0 = engine.cmd.var(0).as_slice()?;
    let s1 = engine.cmd.var(1).as_slice()?;
    let r = operation(s1.as_ref(), s0.as_ref());
    engine.cc.stack.push(r?);
    Ok(())
}

fn first_distinct_bit<F>(engine: &mut Engine, name: &'static str, operation: F) -> Status
    where
        F: Fn(Option<bool>, Option<bool>) -> StackItem
{
    engine.load_instruction(
        Instruction::new(name)
    )?;
    fetch_stack(engine, 2)?;
    let s0 = engine.cmd.var(0).as_slice()?.as_ref();
    let s1 = engine.cmd.var(1).as_slice()?.as_ref();
    let common_bits = s0.longest_common_data_prefix(s1).size_bits();
    let r = operation(s1.get_bit(common_bits).ok(), s0.get_bit(common_bits).ok());
    engine.cc.stack.push(r);
    Ok(())
}

/// SEMPTY (s – s = ∅), checks whether a Slice s is empty
/// (i.e., contains no bits of data and no cell references).
pub(super) fn execute_sempty(engine: &mut Engine) -> Status {
    unary(engine, "SEMPTY", |slice| boolean!(
        (slice.size_bits() == 0) && (slice.size_refs() == 0)
    ))
}

/// SDEMPTY (s – s ≈ ∅), checks whether Slice s has no bits of data.
pub(super) fn execute_sdempty(engine: &mut Engine) -> Status {
    unary(engine, "SDEMPTY", |slice| boolean!(slice.size_bits() == 0))
}

/// SREMPTY (s – r(s) = 0), checks whether Slice s has no refer- ences.
pub(super) fn execute_srempty(engine: &mut Engine) -> Status {
    unary(engine, "SREMPTY", |slice| boolean!(slice.size_refs() == 0))
}

/// SDFIRST (s – s0 = 1), checks whether the first bit of Slice s is a one.
pub(super) fn execute_sdfirst(engine: &mut Engine) -> Status {
    unary(engine, "SDFIRST", |slice| boolean!(
        (slice.size_bits() != 0) && (slice.get_bit(0) == Ok(true))
    ))
}

/// SDLEXCMP (s s′ – c), compares the data of s lexicographically
/// with the data of s′, returning −1, 0, or 1 depending on the result. s > s` => 1
pub(super) fn execute_sdlexcmp(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDLEXCMP", |r_s1, r_s0| int!(
        match (r_s0, r_s1) {
            (None, None) => 0,
            (Some(_), Some(true)) => 1,
            (Some(_), Some(false)) => -1,
            (None, Some(_)) => 1,
            (Some(_), None) => -1
        }
    ))
}

/// SDEQ(s s′ – s ≈ s′), checks whether the data parts of s and s′ coincide,
/// equivalent to SDLEXCMP; ISZERO.
pub(super) fn execute_sdeq(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDEQ", |r_s1, r_s0| boolean!(
        r_s0.is_none() && r_s1.is_none()
    ))
}

/// SDPFX (s s′ – ?), checks whether s is a prefix of s′.
pub(super) fn execute_sdpfx(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDPFX", |r_s1, _| boolean!(r_s1.is_none()))
}

/// SDPFXREV (s s′ – ?), checks whether s′ is a prefix of s, equivalent
/// to SWAP; SDPFX.
pub(super) fn execute_sdpfxrev(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDPFXREV", |_, r_s0| boolean!(r_s0.is_none()))
}

/// SDPPFX (s s′ – ?), checks whether s is a proper prefix of s′
/// (i.e., prefix distinct from s′).
pub(super) fn execute_sdppfx(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDPPFX", |r_s1, r_s0| boolean!(
        r_s0.is_some() && r_s1.is_none()
    ))
}

/// SDPPFXREV (s s′ – ?), checks whether s′ is a proper prefix of s.
pub(super) fn execute_sdppfxrev(engine: &mut Engine) -> Status {
    first_distinct_bit(engine, "SDPPFXREV", |r_s1, r_s0| boolean!(
        r_s0.is_none() && r_s1.is_some()
    ))
}

/// SDSFX(s s′ – ?), checks whether s is a suffix of s′.
pub(super) fn execute_sdsfx(engine: &mut Engine) -> Status {
    binary(engine, "SDSFX", |s1, s0| Ok(boolean!({
        let l0 = s0.size_bits();
        let l1 = s1.size_bits();
        if l1 <= l0 {
            let mut s0 = s0.clone();
            s0.skip_first(l0 - l1, 0)?;
            s0.longest_common_data_prefix(s1).size_bits() == l1
        } else {
            false
        }
    })))
}

/// SDSFXREV (s s′ – ?), checks whether s′ is a suffix of s.
pub(super) fn execute_sdsfxrev(engine: &mut Engine) -> Status {
    binary(engine, "SDSFXREV", |s1, s0| Ok(boolean!({
        let l0 = s0.size_bits();
        let l1 = s1.size_bits();
        if l0 <= l1 {
            let mut s1 = s1.clone();
            s1.skip_first(l1 - l0, 0)?;
            s1.longest_common_data_prefix(s0).size_bits() == l0
        } else {
            false
        }
    })))
}

///  SDPSFX (s s′ – ?), checks whether s is a proper suffix of s′.
pub(super) fn execute_sdpsfx(engine: &mut Engine) -> Status {
    binary(engine, "SDPSFX", |s1, s0| Ok(boolean!({
        let l0 = s0.size_bits();
        let l1 = s1.size_bits();
        if l1 < l0 {
            let mut s0 = s0.clone();
            s0.skip_first(l0 - l1, 0)?;
            s0.longest_common_data_prefix(s1).size_bits() == l1
        } else {
            false
        }
    })))
}

/// SDPSFXREV (s s′ – ?), checks whether s′ is a proper suffix of s.
pub(super) fn execute_sdpsfxrev(engine: &mut Engine) -> Status {
    binary(engine, "SDPSFXREV", |s1, s0| Ok(boolean!({
        let l0 = s0.size_bits();
        let l1 = s1.size_bits();
        if l0 < l1 {
            let mut s1 = s1.clone();
            s1.skip_first(l1 - l0, 0)?;
            s1.longest_common_data_prefix(s0).size_bits() == l0
        } else {
            false
        }
    })))
}

/// SDCNTLEAD0 (s – n), returns the number of leading zeroes in s.
pub(super) fn execute_sdcntlead0(engine: &mut Engine) -> Status {
    unary(engine, "SDCNTLEAD0", |slice| int!({
        let n = slice.size_bits();
        (0..n).position(|i| slice.get_bit(i) == Ok(true)).unwrap_or(n as usize)
    }))
}

/// SDCNTLEAD1 (s – n), returns the number of leading ones in s.
pub(super) fn execute_sdcntlead1(engine: &mut Engine) -> Status {
    unary(engine, "SDCNTLEAD1", |slice| int!({
        let n = slice.size_bits();
        (0..n).position(|i| slice.get_bit(i) == Ok(false)).unwrap_or(n as usize)
    }))
}

/// SDCNTTRAIL0 (s – n), returns the number of trailing zeroes in s.
pub(super) fn execute_sdcnttrail0(engine: &mut Engine) -> Status {
    unary(engine, "SDCNTTRAIL0", |slice| int!({
        let n = slice.size_bits();
        (0..n).position(|i| slice.get_bit(n - i - 1) == Ok(true)).unwrap_or(n as usize)
    }))
}

/// SDCNTTRAIL1 (s – n), returns the number of trailing ones in s.
pub(super) fn execute_sdcnttrail1(engine: &mut Engine) -> Status {
    unary(engine, "SDCNTTRAIL1", |slice| int!({
        let n = slice.size_bits();
        (0..n).position(|i| slice.get_bit(n - i - 1) == Ok(false)).unwrap_or(n as usize)
    }))
}

