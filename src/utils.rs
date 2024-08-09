/*
* Copyright (C) 2019-2022 TON Labs. All Rights Reserved.
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
use everscale_types::error::Error;

use crate::OwnedCellSlice;

pub fn get_dictionary_opt(
    slice: &mut OwnedCellSlice,
) -> crate::types::Result<Option<OwnedCellSlice>> {
    let mut root = slice.clone();
    if slice.as_mut().load_bit()? == false {
        root.as_mut().shrink(None, Some(0))?;
    } else if slice.as_ref().size_refs() == 0 {
        return Ok(None);
    } else {
        slice.as_mut().load_reference()?;
        root.as_mut().shrink(None, Some(1))?;
    }
    root.as_mut().shrink(Some(1), None)?;
    Ok(Some(root))
}

pub trait CellSliceExt {
    fn shrink(&mut self, bits: Option<u16>, refs: Option<u8>) -> Result<(), Error>;
}

impl CellSliceExt for CellSlice<'_> {
    fn shrink(&mut self, bits: Option<u16>, refs: Option<u8>) -> Result<(), Error> {
        let bits = bits.unwrap_or_else(|| self.size_bits());
        let refs = refs.unwrap_or_else(|| self.size_refs());
        self.only_first(bits, refs)
    }
}
