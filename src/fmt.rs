use std::fmt::Formatter;

use everscale_types::prelude::{CellBuilder, CellSlice, CellSliceParts, CellSliceRange};

pub struct Fmt<'a, T>(pub &'a T);

impl std::fmt::Display for Fmt<'_, CellBuilder> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "bits: {}, refs: {}, data: {}", self.0.size_bits(), self.0.size_refs(), &self.0.display_data())
    }
}

impl std::fmt::Display for Fmt<'_, CellSlice<'_>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cell: {}, {}, data: {}",
            self.0.cell().repr_hash(),
            Fmt(&self.0.range()),
            self.0.display_data(),
        )
    }
}

impl std::fmt::Display for Fmt<'_, CellSliceParts> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let (cell, range) = self.0;
        match range.apply(cell) {
            Ok(slice) => std::fmt::Display::fmt(&Fmt(&slice), f),
            Err(e) => write!(
                f,
                "cell: {}, {}, with invalid range: {} ({e})",
                cell.repr_hash(),
                Fmt(&CellSliceRange::full(cell.as_ref())),
                Fmt(range),
            ),
        }
    }
}

impl std::fmt::Display for Fmt<'_, CellSliceRange> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "bits: {}..{}, refs: {}..{}",
               self.0.offset_bits(),
               self.0.offset_bits() + self.0.size_bits(),
               self.0.offset_refs(),
               self.0.offset_refs() + self.0.size_refs(),
        )
    }
}
