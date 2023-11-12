use std::fmt::Formatter;

use everscale_types::cell::{CellBuilder, CellSlice};
use everscale_types::error::Error;
use everscale_types::prelude::{Cell, CellFamily, CellSliceParts};

use crate::Fmt;

/// An owned [`CellSlice`] container. Slice points to the owned Cell.
#[derive(Clone, Eq, PartialEq)]
pub struct OwnedCellSlice {
    cell: Cell,
    cell_slice: CellSlice<'static>,
}

impl std::fmt::Display for OwnedCellSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&Fmt(&self.cell_slice), f)
    }
}

impl std::fmt::Debug for OwnedCellSlice {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&Fmt(&self.cell_slice), f)
    }
}

impl TryFrom<Cell> for OwnedCellSlice {
    type Error = Error;

    fn try_from(cell: Cell) -> Result<Self, Self::Error> {
        Self::new(cell)
    }
}

impl TryFrom<CellSliceParts> for OwnedCellSlice {
    type Error = Error;

    fn try_from((cell, range): CellSliceParts) -> Result<Self, Self::Error> {
        let cell_slice = range.apply(&cell)?;
        Ok(Self {
            // SAFETY: cell reference points to the pinned location
            cell_slice: unsafe { std::mem::transmute::<_, CellSlice<'static>>(cell_slice) },
            cell,
        })
    }
}

impl Into<CellSliceParts> for OwnedCellSlice {
    fn into(self) -> CellSliceParts {
        (self.cell, self.cell_slice.range())
    }
}

impl OwnedCellSlice {
    pub fn empty() -> Self {
        // SAFETY: empty cell is ordinary thus not pruned
        unsafe { Self::new_unchecked(Cell::empty_cell()) }
    }

    /// Constructs a new cell slice from the specified cell.
    /// Returns an error if the cell is pruned.
    pub fn new(cell: Cell) -> Result<Self, Error> {
        let cell_slice = cell.as_slice()?;
        Ok(Self {
            // SAFETY: cell reference points to the pinned location
            cell_slice: unsafe { std::mem::transmute::<_, CellSlice<'static>>(cell_slice) },
            cell,
        })
    }

    /// Constructs a new cell slice from the specified cell.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - cell is not pruned
    unsafe fn new_unchecked(cell: Cell) -> Self {
        let cell_slice = cell.as_slice_unchecked();
        Self {
            // SAFETY: cell reference points to the pinned location
            cell_slice: unsafe { std::mem::transmute::<_, CellSlice<'static>>(cell_slice) },
            cell,
        }
    }

    /// Returns a reference to the underlying owned cell.
    pub fn cell(&self) -> &Cell {
        &self.cell
    }

    /// Returns an immutable reference to the underlying slice.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn as_ref(&'_ self) -> &'_ CellSlice<'_> {
        &self.cell_slice
    }

    /// Returns a mutable reference to the underlying slice.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn as_mut<'a>(&'a mut self) -> &'a mut CellSlice<'a> {
        // SAFETY: cell reference points to the pinned location
        unsafe { std::mem::transmute::<_, &'a mut CellSlice<'a>>(&mut self.cell_slice) }
    }

    pub fn withdraw(&mut self) -> OwnedCellSlice {
        std::mem::replace(self, OwnedCellSlice::empty())
    }

    pub fn into_cell(self) -> Result<Cell, Error> {
        let range = self.cell_slice.range();
        if range.bits_offset() == 0 && range.refs_offset() == 0
            && range.remaining_refs() == self.cell.reference_count()
            && range.remaining_bits() == self.cell.bit_len() {
            Ok(self.cell)
        } else {
            CellBuilder::build_from(&self.cell_slice)
        }
    }
}