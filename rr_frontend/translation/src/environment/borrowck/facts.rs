// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::RefCell;
use std::rc::Rc;
use std::{cmp, fmt};

use rr_rustc_interface::borrowck;
use rr_rustc_interface::borrowck::consumers::{LocationTable, RichLocation, RustcFacts};
use rr_rustc_interface::middle::mir;
use rr_rustc_interface::polonius_engine::FactTypes;

pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

pub type AllInput = borrowck::consumers::PoloniusInput;
pub type AllOutput = borrowck::consumers::PoloniusOutput;

trait LocationTableExt {
    fn to_mir_location(self, point: PointIndex) -> mir::Location;
}

impl LocationTableExt for LocationTable {
    fn to_mir_location(self, point: PointIndex) -> mir::Location {
        match self.to_location(point) {
            RichLocation::Start(location) | RichLocation::Mid(location) => location,
        }
    }
}

pub struct Borrowck {
    /// Polonius input facts.
    pub input_facts: RefCell<Option<Box<AllInput>>>,
    /// Polonius output facts.
    pub output_facts: Rc<AllOutput>,
    /// The table that maps Polonius points to locations in the table.
    pub location_table: RefCell<Option<LocationTable>>,
}

/// The type of the point. Either the start of a statement or in the
/// middle of it.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum PointType {
    Start,
    Mid,
}

impl cmp::PartialOrd for PointType {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        let res = match (self, other) {
            (Self::Start, Self::Mid) => cmp::Ordering::Less,
            (Self::Mid, Self::Start) => cmp::Ordering::Greater,

            (Self::Start, Self::Start) | (Self::Mid, Self::Mid) => cmp::Ordering::Equal,
        };

        Some(res)
    }
}

impl cmp::Ord for PointType {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// A program point used in the borrow checker analysis.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Point {
    pub location: mir::Location,
    pub typ: PointType,
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}:{:?}:{:?}", self.location.block, self.location.statement_index, self.typ)
    }
}

pub struct Interner {
    pub(crate) location_table: LocationTable,
}

impl Interner {
    #[must_use]
    pub const fn new(location_table: LocationTable) -> Self {
        Self { location_table }
    }

    #[must_use]
    pub fn get_point_index(&self, point: &Point) -> PointIndex {
        // self.points.get_index(point)
        match point.typ {
            PointType::Start => self.location_table.start_index(point.location),
            PointType::Mid => self.location_table.mid_index(point.location),
        }
    }

    #[must_use]
    pub fn get_point(&self, index: PointIndex) -> Point {
        // self.points.get_element(index)
        match self.location_table.to_location(index) {
            RichLocation::Start(location) => Point {
                location,
                typ: PointType::Start,
            },
            RichLocation::Mid(location) => Point {
                location,
                typ: PointType::Mid,
            },
        }
    }

    #[must_use]
    pub fn get_location(&self, index: PointIndex) -> mir::Location {
        // self.points.get_element(index)
        match self.location_table.to_location(index) {
            RichLocation::Start(location) | RichLocation::Mid(location) => location,
        }
    }
}
