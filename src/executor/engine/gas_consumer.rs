use std::{mem, result::Result as StdResult};

use ahash::HashSet;
use everscale_types::cell::{CellParts, LoadMode};
use everscale_types::dict::RawDict;
use everscale_types::error::Error as EtyError;
use everscale_types::models::{GlobalCapabilities, GlobalCapability, LibDescr, SimpleLib};
use everscale_types::prelude::{Cell, CellContext, CellFamily, CellType, Dict, DynCell, HashBytes, Load};

use crate::{error::TvmError, executor::gas::gas_state::Gas, types::{Exception, Status, ExceptionCode, Result}};

pub struct GasConsumer {
    libraries: Vec<RawDict<256>>,
    visited_cells: HashSet<HashBytes>,
    visited_exotic_cells: HashSet<HashBytes>,
    capabilities: GlobalCapabilities,
    gas: Gas,
}

struct InstrumentedCellContext<'a> {
    gas_consumer: &'a mut GasConsumer,
    cancel_error: Option<anyhow::Error>,
}

impl<'a> CellContext for InstrumentedCellContext<'a> {
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> StdResult<Cell, EtyError> {
        let result = self.gas_consumer.gas.try_use_gas(Gas::finalize_price());
        self.conceal(result)?;
        Ok(Cell::empty_context().finalize_cell(cell)?)
    }

    fn load_cell(
        &mut self,
        mut cell: Cell,
        opt: LoadMode,
    ) -> StdResult<Cell, EtyError> {
        loop {
            let result = self.gas_consumer
                .has_resolved_cell(cell.repr_hash(), cell.cell_type(), opt);
            if self.conceal(result)? {
                break;
            }
            let result = resolve_exotic_cell(
                &self.gas_consumer.libraries.clone(),
                &self.gas_consumer.capabilities.clone(),
                cell,
                self,
            );
            cell = self.conceal(result)?;
        }
        Ok(cell)
    }

    /// SAFETY: method can provide a reference to a library cell,
    /// it is safe while `self.libraries` remain immutable
    fn load_dyn_cell<'с>(
        &mut self,
        mut dyn_cell: &'с DynCell,
        opt: LoadMode,
    ) -> StdResult<&'с DynCell, EtyError> {
        loop {
            let result = self.gas_consumer
                .has_resolved_cell(dyn_cell.repr_hash(), dyn_cell.cell_type(), opt);
            if self.conceal(result)? {
                break;
            }
            let result = unsafe {
                resolve_exotic_dyn_cell(
                    &self.gas_consumer.libraries.clone(),
                    &self.gas_consumer.capabilities.clone(),
                    dyn_cell,
                    self,
                )
            };
            dyn_cell = self.conceal(result)?;
        }
        Ok(dyn_cell)
    }
}

impl<'a> InstrumentedCellContext<'a> {
    fn conceal<T>(&mut self, r: Result<T>) -> StdResult<T, EtyError> {
        match r {
            Err(e) => {
                self.cancel_error = Some(e);
                Err(EtyError::Cancelled)
            }
            Ok(x) => Ok(x),
        }
    }
    fn reveal<T>(self, r: StdResult<T, EtyError>) -> Result<T> {
        match self.cancel_error {
            Some(e) => Err(e),
            None => Ok(r?),
        }
    }
}

impl GasConsumer {
    pub(super) fn new(capabilities: GlobalCapabilities, gas: Gas) -> Self {
        Self {
            libraries: Vec::new(),
            visited_cells: HashSet::default(),
            visited_exotic_cells: HashSet::default(),
            gas,
            capabilities,
        }
    }

    pub fn ctx<T, F>(&mut self, f: F) -> Result<T>
        where F: FnOnce(&mut dyn CellContext) -> StdResult<T, EtyError> {
        let mut ctx = InstrumentedCellContext { gas_consumer: self, cancel_error: None };
        let concealed_result = f(&mut ctx);
        ctx.reveal(concealed_result)
    }

    pub(super) fn set_libraries(
        &mut self,
        account_libs: &Dict<HashBytes, SimpleLib>,
        shared_libs: &Dict<HashBytes, LibDescr>,
    ) -> StdResult<(), EtyError> {
        // search in account libs first
        // both dicts store library cells as zero reference of value cell
        for root in [account_libs.root(), shared_libs.root()] {
            if let Some(root) = root {
                self.libraries
                    .push(RawDict::<256>::load_from(root.as_slice()?.as_mut())?);
            }
        }
        Ok(())
    }

    pub(super) fn has_capability(&self, capability: GlobalCapability) -> bool {
        self.capabilities.contains(capability)
    }

    pub(super) fn check_capability(&self, capability: GlobalCapability) -> Status {
        check_capability(&self.capabilities, capability)
    }

    pub fn gas_mut(&mut self) -> &mut Gas {
        &mut self.gas
    }

    pub fn gas(&self) -> &Gas {
        &self.gas
    }

    fn has_resolved_cell(
        &mut self,
        cell_hash: &HashBytes,
        cell_type: CellType,
        opt: LoadMode,
    ) -> Result<bool> {
        if cell_type == CellType::Ordinary {
            if opt.use_gas() {
                if self.visited_cells.contains(cell_hash) {
                    self.gas.try_use_gas(Gas::load_cell_price(false))?;
                } else {
                    self.gas.try_use_gas(Gas::load_cell_price(true))?;
                    self.visited_cells.insert(cell_hash.clone());
                }
            }
            Ok(true)
        } else if !opt.resolve() {
            Ok(true)
        } else if self.visited_exotic_cells.contains(cell_hash) {
            if opt.use_gas() {
                self.gas.try_use_gas(Gas::load_cell_price(false))?;
            }
            Ok(true)
        } else {
            if opt.resolve() {
                self.gas.try_use_gas(Gas::load_cell_price(true))?;
                self.visited_exotic_cells.insert(cell_hash.clone());
            }
            Ok(false)
        }
    }
}

fn check_capability(capabilities: &GlobalCapabilities, capability: GlobalCapability) -> Status {
    if capabilities.contains(capability) {
        Ok(())
    } else {
        err!(ExceptionCode::InvalidOpcode, "{:?} is absent", capability)
    }
}

/// Moved out of Self in order not to mess `&self` into unsafe lifetimes
unsafe fn resolve_exotic_dyn_cell<'a>(
    libraries: &Vec<RawDict<256>>,
    capabilities: &GlobalCapabilities,
    mut cell: &'a DynCell,
    ctx: &mut dyn CellContext,
) -> Result<&'a DynCell> {
    match cell.cell_type() {
        CellType::LibraryReference => {
            check_capability(capabilities, GlobalCapability::CapSetLibCode)?;
            let dyn_cell = get_library_parent_cell(libraries, cell.as_ref(), ctx)?;
            library_result(dyn_cell.reference(0))
        }
        CellType::MerkleProof if capabilities.contains(GlobalCapability::CapResolveMerkleCell) => {
            let hash = get_hash_for_merkle_proof(cell)?;
            cell = cell
                .reference(0)
                .map(|a| a.virtualize())
                .ok_or(ExceptionCode::CellUnderflow)?;
            merkle_proof_result(*cell.repr_hash() == hash, cell)
        }
        CellType::MerkleUpdate if capabilities.contains(GlobalCapability::CapResolveMerkleCell) => {
            let hash = get_hash_for_merkle_update(cell)?;
            cell = cell
                .reference(1)
                .map(|a| a.virtualize())
                .ok_or(ExceptionCode::CellUnderflow)?;
            merkle_update_result(*cell.repr_hash() == hash, cell)
        }
        _ => unknown_cell_type_result(cell.cell_type()),
    }
}

/// Moved out of Self to accompany `resolve_exotic_dyn_cell`
fn resolve_exotic_cell(
    libraries: &Vec<RawDict<256>>,
    capabilities: &GlobalCapabilities,
    mut cell: Cell,
    ctx: &mut dyn CellContext,
) -> Result<Cell> {
    match cell.cell_type() {
        CellType::LibraryReference => {
            check_capability(capabilities, GlobalCapability::CapSetLibCode)?;
            // SAFETY: we clone the child ref, so safety is restored immediately.
            // we could have a safe method here (with reference_cloned() inside),
            // but avoid just some code duplication
            let dyn_cell =
                unsafe { get_library_parent_cell(libraries, cell.as_ref(), ctx)? };
            library_result(dyn_cell.reference_cloned(0))
        }
        CellType::MerkleProof if capabilities.contains(GlobalCapability::CapResolveMerkleCell) => {
            let hash = get_hash_for_merkle_proof(cell.as_ref())?;
            cell = cell
                .reference_cloned(0)
                .map(Cell::virtualize)
                .ok_or(ExceptionCode::CellUnderflow)?;
            merkle_proof_result(*cell.repr_hash() == hash, cell)
        }
        CellType::MerkleUpdate if capabilities.contains(GlobalCapability::CapResolveMerkleCell) => {
            let hash = get_hash_for_merkle_update(cell.as_ref())?;
            cell = cell
                .reference_cloned(1)
                .map(Cell::virtualize)
                .ok_or(ExceptionCode::CellUnderflow)?;
            merkle_update_result(*cell.repr_hash() == hash, cell)
        }
        _ => unknown_cell_type_result(cell.cell_type()),
    }
}

/// SAFETY: we are allowed to enlarge the lifetime `'s` of library dyn_cell
/// while libraries belong to the engine from its start to its end, ie libraries are not deleted.
/// Cloning the child of resulting dyn_cell allows us to obtain just a normal cell (with Arc inside) -
/// we will do it anyway to put the owned cell back on VM stack.
unsafe fn get_library_parent_cell<'s, 'c: 's>(
    libraries: &'s Vec<RawDict<256>>,
    mut cell: &'c DynCell,
    ctx: &mut dyn CellContext,
) -> Result<&'c DynCell> {
    let mut key = cell.as_slice()?;
    key.skip_first(8, 0)?;
    let hash = key.get_u256(0)?;
    for library in libraries {
        if let Some(lib) = library.get_ext(key, ctx)? {
            let lib_cell_hash = lib.get_reference(0)?.repr_hash();
            if hash != *lib_cell_hash {
                return err!(
                    ExceptionCode::DictionaryError,
                    "Library hash does not correspond to map key {}",
                    key.display_data()
                );
            }
            // we promise that library (parent) cell will not be removed from Dict,
            // and Dict will not be removed from Engine
            cell = unsafe { mem::transmute::<&'s DynCell, &'c DynCell>(lib.cell()) };
            return Ok(cell);
        }
    }
    err!(
        ExceptionCode::CellUnderflow,
        "Libraries do not contain code with hash {}",
        key.display_data()
    )
}

fn get_hash_for_merkle_proof(cell: &DynCell) -> Result<HashBytes> {
    let mut slice = cell.as_slice()?;
    slice.skip_first(8, 0)?;
    Ok(slice.load_u256()?)
}

fn get_hash_for_merkle_update(cell: &DynCell) -> Result<HashBytes> {
    let mut slice = cell.as_slice()?;
    slice.skip_first(8, 0)?;
    let hash = slice.load_u256()?;
    if cell
        .reference(0)
        .map(|a| a.virtualize())
        .map(|a| a.repr_hash())
        != Some(&hash)
    {
        return err!(
            ExceptionCode::CellUnderflow,
            "hash of merkle update cell is not corresponded to child cell"
        );
    }
    slice.skip_first(16, 0)?;
    Ok(slice.load_u256()?)
}

fn library_result<T>(cell: Option<T>) -> Result<T> {
    if let Some(cell) = cell {
        Ok(cell)
    } else {
        err!(
            ExceptionCode::FatalError,
            "failed to load same cell twice in a row"
        )
    }
}

fn merkle_proof_result<T>(hash_mathces: bool, cell: T) -> Result<T> {
    if hash_mathces {
        Ok(cell)
    } else {
        err!(
            ExceptionCode::CellUnderflow,
            "hash of merkle proof cell is not corresponded to child cell"
        )
    }
}

fn merkle_update_result<T>(hash_mathces: bool, cell: T) -> Result<T> {
    if hash_mathces {
        Ok(cell)
    } else {
        err!(
            ExceptionCode::CellUnderflow,
            "hash of merkle update cell is not corresponded to child cell"
        )
    }
}

fn unknown_cell_type_result<T>(cell_type: CellType) -> Result<T> {
    err!(
        ExceptionCode::CellUnderflow,
        "Wrong resolving cell type {:?}",
        cell_type
    )
}

#[test]
fn get_lib_unsafe() -> anyhow::Result<()> {
    use super::*;
    use everscale_types::prelude::{Boc, CellBuilder};
    use std::str::FromStr;

    fn new_dict() -> Result<RawDict<256>> {
        let dict_data = "te6ccgEBBAEARQABAcABAUOgEbsgqLYV1qI0TAn1wSekXqSfFyhQ5H0efAYtWJF+UeEQAgEAAwAubmV2ZXIgZ29ubmEgZ2l2ZSB5b3UgdXA=";
        Ok(Boc::decode_base64(dict_data)?.parse()?)
    }

    let lib_hash =
        HashBytes::from_str("8dd90545b0aeb511a2604fae093d22f524f8b9428723e8f3e0316ac48bf28f08")?;

    let mut builder = CellBuilder::new();
    builder.store_u8(0)?;
    builder.store_u256(&lib_hash)?;
    let key = builder.build()?;

    let mut gas_consumer = GasConsumer {
        libraries: vec![new_dict()?],
        visited_cells: Default::default(),
        visited_exotic_cells: Default::default(),
        capabilities: Default::default(),
        gas: Gas::new(1000000000, 0, 1000000000, 10),
    };

    // this is safe - libraries belong to `gas_consumer` from outer scope
    let found = {
        let libraries = gas_consumer.libraries.clone();
        gas_consumer.ctx(|c| unsafe {
            Ok(get_library_parent_cell(
                &libraries,
                key.as_ref(),
                c,
            ).unwrap())
        })?
    };
    assert_eq!(Some(&lib_hash), found.reference(0).map(|c| c.repr_hash()));

    // safety is broken if we read from scope that is gone
    let found = gas_consumer
        .ctx(|c| unsafe {
            Ok(new_dict().and_then(|d| get_library_parent_cell(&vec![d], key.as_ref(), c)).unwrap())
        })?;
    assert_ne!(Some(&lib_hash), found.reference(0).map(|c| c.repr_hash()));

    Ok(())
}
