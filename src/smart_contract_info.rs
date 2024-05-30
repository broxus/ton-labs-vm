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

use everscale_types::cell::{Cell, HashBytes};
use everscale_types::models::{CurrencyCollection, GlobalCapabilities, GlobalCapability};
use crate::stack::{
    StackItem,
    integer::IntegerData,
};
use sha2::{Sha256, Digest};
use crate::OwnedCellSlice;

/*
The smart-contract information
structure SmartContractInfo, passed in the first reference of the cell contained
in control register c5, is serialized as follows:

smc_info#076ef1ea actions:uint16 msgs_sent:uint16
unixtime:uint32 block_lt:uint64 trans_lt:uint64
rand_seed:uint256 balance_remaining:CurrencyCollection
myself:MsgAddress = SmartContractInfo;
*/
// TODO drop deprecated
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartContractInfo {
    // deprecated?
    pub actions: u16,
    // deprecated?
    pub msgs_sent: u16,
    pub unix_time: u32,
    pub block_lt: u64,
    pub trans_lt: u64,
    pub rand_seed: IntegerData,
    pub balance: CurrencyCollection,
    pub myself: OwnedCellSlice,
    pub config_params: Option<Cell>, // config params from masterchain
    pub mycode: Cell,
    pub init_code_hash: HashBytes,
    pub storage_fee_collected: u128,
}

impl SmartContractInfo{
    /// The rand_seed field here is initialized deterministically starting from the
    /// rand_seed of the block, and the (addr_std) account address.
    pub fn calc_rand_seed(rand_seed_block: &HashBytes, account_id: &HashBytes) -> IntegerData {
        // combine all parameters to vec and calculate hash of them
        if rand_seed_block != &HashBytes::ZERO {
            let mut hasher = Sha256::new();
            hasher.update(rand_seed_block.0);
            hasher.update(account_id.0);

            let sha256 = hasher.finalize();
            IntegerData::from_unsigned_bytes_be(sha256)
        } else {
            // if the user forgot to set the rand_seed_block value, then this 0 will be clearly visible on tests
            tracing::warn!(target: "tvm", "Not set rand_seed_block");
            IntegerData::zero()
        }
    }

    pub fn into_temp_data_item(self, capabilities: GlobalCapabilities) -> StackItem {
        let mut params = vec![
            int!(0x076ef1ea),      // magic - should be changed because of structure change
            int!(self.actions),    // actions
            int!(self.msgs_sent),  // msgs
            int!(self.unix_time),  // unix time
            int!(self.block_lt),   // logical time
            int!(self.trans_lt),   // transaction time
            StackItem::int(self.rand_seed),
            StackItem::tuple(vec![
                int!(self.balance.tokens.into_inner()),
                self.balance.other.as_dict().root().clone().map_or(StackItem::None, StackItem::Cell)
            ]),
            StackItem::Slice(self.myself),
            self.config_params.map_or(StackItem::None, StackItem::Cell),
        ];
        let additional_params = [
            (GlobalCapability::CapMyCode, StackItem::cell(self.mycode.clone())),
            (GlobalCapability::CapInitCodeHash, StackItem::int(IntegerData::from_unsigned_bytes_be(self.init_code_hash.as_slice()))),
            (GlobalCapability::CapStorageFeeToTvm, StackItem::int(self.storage_fee_collected)),
        ];
        let add_params = &mut Vec::new();
        for (i, (caps, f)) in additional_params.into_iter().enumerate() {
            if capabilities.contains(caps) {
                for _ in add_params.len()..i {
                    add_params.push(StackItem::default());
                }
                add_params.push(f);
            }
        }
        params.append(add_params);
        debug_assert!(params.len() <= 14, "{:?} caps: {:X}", params, capabilities.into_inner());
        StackItem::tuple(vec![StackItem::tuple(params)])
    }

}
