// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::PathBuf;

use log::{debug, trace};
use polonius_engine::{Algorithm, Output};
use rustc_data_structures::fx::FxHashMap;
use rustc_index::Idx;
use rustc_middle::ty::fold::TypeFolder;
use rustc_middle::{mir, ty};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use {datafrog, rrconfig as config};

use super::borrowck::{facts, regions};
use super::procedure::Procedure;
use super::{loops, Environment};
use crate::environment::borrowck::facts::PointType;
use crate::environment::borrowck::regions::{PlaceRegions, PlaceRegionsError};
use crate::environment::mir_utils::{
    AllPlaces, RealEdges, SplitAggregateAssignment, StatementAsAssign, StatementAt,
};
use crate::environment::polonius_info::facts::AllInputFacts;
use crate::utils;

/// This represents the assignment in which a loan was created. The `source`
/// will contain the creation of the loan, while the `dest` will store the
/// created reference.
#[derive(Clone, Debug)]
pub struct LoanPlaces<'tcx> {
    pub dest: mir::Place<'tcx>,
    pub source: mir::Rvalue<'tcx>,
    pub location: mir::Location,
}

/// This represents "rich" regions that are directly annotated with their `RegionKind`.
///
/// PlaceRegions are a bit special: in Polonius, they contain sets of loans, but in RR's
/// path-sensitive type system they also end up referencing one particular loan.
///
/// Loan regions can themselves be intersections of other loan regions and universal regions,
/// but they contain an "atomic" component (corresponding to an atomic lifetime).
#[derive(Clone, Debug)]
pub enum AtomicRegion {
    Loan(facts::Loan, facts::Region),
    Universal(UniversalRegionKind, facts::Region),
    PlaceRegion(facts::Region),
    Unknown(facts::Region),
}

impl AtomicRegion {
    pub fn get_region(&self) -> facts::Region {
        match self {
            Self::Loan(_, r) => *r,
            Self::Universal(_, r) => *r,
            Self::PlaceRegion(r) => *r,
            Self::Unknown(r) => *r,
        }
    }
}

/// for an overview fo universal regions, see also rustc_borrowck/src/universal_regions.rs
#[derive(Clone, Debug, PartialEq, Copy)]
pub enum UniversalRegionKind {
    /// the static region
    Static,
    /// the function-level region
    Function,
    /// a locally declared universal region (except for the function region)
    Local,
    /// an externally declared universal region (relevant for closures)
    External,
}

#[derive(Debug)]
pub enum RegionKind {
    /// this region belongs to a loan that is created
    Loan(facts::Loan),
    /// this is a universal region
    Universal(UniversalRegionKind),
    /// inference variable in the type of a local
    PlaceRegion,
    /// unknown region kind; for instance used for the inference variables introduced on a call to
    /// a function with lifetime parameters
    Unknown,
}

/*
pub struct RegionGraphNode {
    /// the kind of this node
    kind: RegionKind,
    /// the region
    region: facts::Region,
    /// the other regions this node is included in
    included_in: HashSet<facts::Region>,
}

/// a region graph, with the edges being the subset relation and nodes being regions.
pub struct RegionGraph {
    nodes: IndexVec<facts::Region, RegionGraphNode>,
}

impl RegionGraph {
    /// Create a new empty `RegionGraph`.
    pub fn new() -> RegionGraph {
        RegionGraph { nodes: IndexVec::new() }
    }

    /// Add a region with a specific `RegionNodeKind`. This will also automatically insert all not
    /// previously inserted regions with smaller index at a `Intersected` kind (so take care to do
    /// this in the right order!).
    pub fn insert_region(&mut self, region: facts::Region, kind: RegionKind) {
        let mut next_idx = self.nodes.len();
        while next_idx < region.index() {
            debug_assert!(self.nodes.next_index().index() == next_idx);
            let node = RegionGraphNode { kind: RegionKind::Intersected, region: ty::RegionVid::from_usize(next_idx), included_in: HashSet::new() };
            self.nodes.push(node);
            next_idx += 1;
        }
        let node = RegionGraphNode {kind, region, included_in: HashSet::new() };
        self.nodes.push(node);
    }

    /// Add a subset relation.
    pub fn add_subset_relation(&mut self, from: facts::Region, to: facts::Region) {
        let mut node_from = &mut self.nodes[from];
        //let node_to = self.nodes[to];
        node_from.included_in.insert(to);
    }
}
*/

#[derive(Clone, Debug)]
pub enum PoloniusInfoError {
    /// Loans depending on branches inside loops are not implemented yet
    UnsupportedLoanInLoop {
        loop_head: mir::BasicBlock,
        variable: mir::Local,
    },
    LoansInNestedLoops(mir::Location, mir::BasicBlock, mir::Location, mir::BasicBlock),
    ReborrowingDagHasNoMagicWands(mir::Location),
    /// We currently support only one reborrowing chain per loop
    MultipleMagicWandsPerLoop(mir::Location),
    MagicWandHasNoRepresentativeLoan(mir::Location),
    PlaceRegionsError(PlaceRegionsError, Span),
    LoanInUnsupportedStatement(String, mir::Location),
}

pub fn graphviz<'tcx>(
    _env: &Environment<'tcx>,
    def_path: &rustc_hir::definitions::DefPath,
    _def_id: DefId,
    info: &PoloniusInfo<'_, 'tcx>,
) -> std::io::Result<()> {
    macro_rules! to_html {
        ( $o:expr ) => {{
            format!("{:?}", $o)
                .replace("{", "\\{")
                .replace("}", "\\}")
                .replace("&", "&amp;")
                .replace(">", "&gt;")
                .replace("<", "&lt;")
                .replace("\n", "<br/>")
        }};
    }
    macro_rules! to_sorted_string {
        ( $o:expr ) => {{
            let mut vector = $o.iter().map(|x| to_html!(x)).collect::<Vec<String>>();
            vector.sort();
            vector.join(", ")
        }};
    }

    //let facts = env.local_mir_borrowck_facts(def_id.expect_local());
    //let location_table = facts.location_table.take().unwrap();
    //let interner = facts::Interner::new(location_table);
    let interner = &info.interner;

    let borrowck_in_facts = &info.borrowck_in_facts;
    //let borrowed_in_facts = facts.input_facts.borrow();
    //let borrowck_in_facts = borrowed_in_facts.as_ref().unwrap();
    let borrowck_out_facts = &info.borrowck_out_facts;
    //let borrowck_out_facts = Output::compute(&borrowck_in_facts, Algorithm::Naive, true);

    use std::io::Write;
    let graph_path = PathBuf::from(config::log_dir())
        .join("nll-facts")
        .join(def_path.to_filename_friendly_no_crate())
        .join("polonius.dot");
    let graph_file = std::fs::File::create(graph_path).expect("Unable to create file");
    let mut graph = std::io::BufWriter::new(graph_file);

    let mut blocks: HashMap<_, _> = HashMap::new();
    let mut block_edges = HashSet::new();
    for (from_index, to_index) in &borrowck_in_facts.cfg_edge {
        let from = interner.get_point(*from_index);
        let from_block = from.location.block;
        let to = interner.get_point(*to_index);
        let to_block = to.location.block;
        let from_points = blocks.entry(from_block).or_insert_with(HashSet::new);
        from_points.insert(*from_index);
        let to_points = blocks.entry(to_block).or_insert_with(HashSet::new);
        to_points.insert(*to_index);
        if from_block != to_block {
            block_edges.insert((from_block, to_block));
        }
    }

    writeln!(graph, "digraph G {{")?;
    write!(graph, "general [ shape=\"record\" ")?;
    writeln!(graph, "label =<<table>")?;
    writeln!(
        graph,
        "<tr><td>universal region:</td><td>{}</td></tr>",
        to_sorted_string!(borrowck_in_facts.universal_region)
    )?;
    writeln!(
        graph,
        "<tr><td>placeholder:</td><td>{}</td></tr>",
        to_sorted_string!(borrowck_in_facts.placeholder)
    )?;
    write!(graph, "</table>>];\n\n")?;
    for (block, point_indices) in blocks {
        write!(graph, "node_{:?} [ shape=\"record\" ", block)?;
        write!(graph, "label =<<table>")?;
        writeln!(graph, "<th><td>{:?}</td></th>", block)?;
        write!(graph, "<tr>")?;
        write!(graph, "<td>point</td>")?;
        write!(graph, "<td>loan_live_at</td>")?;
        writeln!(graph, "</tr>")?;
        let mut points: Vec<_> = point_indices.iter().map(|index| interner.get_point(*index)).collect();
        points.sort();
        for point in points {
            writeln!(graph, "<tr>")?;
            writeln!(graph, "<td>{}</td>", point)?;
            write!(graph, "<td>")?;
            let point_index = interner.get_point_index(&point);
            if let Some(a) = borrowck_out_facts.loan_live_at.get(&point_index) {
                for loan in a {
                    write!(graph, "{:?},", loan)?;
                }
            }
            write!(graph, "</td>")?;
            writeln!(graph, "</tr>")?;
        }
        write!(graph, "</table>>];\n\n")?;
    }
    for (from, to) in block_edges {
        writeln!(graph, "node_{:?} -> node_{:?};", from, to)?;
    }
    writeln!(graph, "}}")?;

    Ok(())
}

/// Compute the transitive closure of a vec of constraints between regions.
pub fn compute_transitive_closure(
    constraints: Vec<(facts::Region, facts::Region)>,
) -> Vec<(facts::Region, facts::Region)> {
    let mut iter = datafrog::Iteration::new();

    let incl = iter.variable::<(facts::Region, facts::Region)>("incl");
    incl.extend(constraints.into_iter());

    let incl1 = iter.variable_indistinct::<(facts::Region, facts::Region)>("incl1");

    while iter.changed() {
        incl1.from_map(&incl, |(r1, r2)| (*r2, *r1));
        incl.from_join(&incl1, &incl, |_r2, r1, r3| (*r1, *r3));
    }
    let incl = incl.complete();
    incl.elements
}

// Terminology: zombie loans are loans that are loan_killed_at.

pub struct PoloniusInfo<'a, 'tcx: 'a> {
    pub(crate) tcx: ty::TyCtxt<'tcx>,
    pub(crate) mir: &'a mir::Body<'tcx>,
    pub(crate) borrowck_in_facts: facts::AllInputFacts,
    pub(crate) borrowck_out_facts: facts::AllOutputFacts,
    pub(crate) interner: facts::Interner,
    /// Position at which a specific loan was created.
    pub(crate) loan_position: HashMap<facts::Loan, mir::Location>,
    pub(crate) loan_at_position: HashMap<mir::Location, facts::Loan>,
    pub place_regions: PlaceRegions,
    pub(crate) additional_facts: AdditionalFacts,
    /// Loans that are created inside loops. Loan → loop head.
    pub(crate) loops: loops::ProcedureLoops,
    /// Facts without back edges.
    pub(crate) additional_facts_no_back: AdditionalFacts,
    /// Two loans are conflicting if they borrow overlapping places and
    /// are alive at overlapping regions.
    pub(crate) loan_conflict_sets: HashMap<facts::Loan, HashSet<facts::Loan>>,
    /// The flipped `subset` relation for each point.
    pub(crate) superset: HashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Region>>>,
}

/// Remove back edges to make MIR uncyclic so that we can compute reborrowing dags at the end of
/// the loop body.
fn remove_back_edges(
    mut all_facts: facts::AllInputFacts,
    interner: &facts::Interner,
    back_edges: &HashSet<(mir::BasicBlock, mir::BasicBlock)>,
) -> facts::AllInputFacts {
    let cfg_edge = all_facts.cfg_edge;
    let cfg_edge = cfg_edge
        .into_iter()
        .filter(|(from, to)| {
            let from_block = interner.get_point(*from).location.block;
            let to_block = interner.get_point(*to).location.block;
            let remove = back_edges.contains(&(from_block, to_block));
            if remove {
                debug!("remove cfg_edge: {:?} → {:?}", from_block, to_block);
            }
            !remove
        })
        .collect();
    all_facts.cfg_edge = cfg_edge;
    all_facts
}

/// Returns the place that is borrowed by the assignment. We assume that
/// all shared references are created only via assignments and ignore
/// all other cases.
fn get_borrowed_places<'a, 'tcx: 'a>(
    mir: &'a mir::Body<'tcx>,
    loan_position: &HashMap<facts::Loan, mir::Location>,
    loan: facts::Loan,
) -> Result<Vec<&'a mir::Place<'tcx>>, PoloniusInfoError> {
    let location = if let Some(location) = loan_position.get(&loan) {
        location
    } else {
        // FIXME (Vytautas): This is likely to be wrong.
        debug!("Not found: {:?}", loan);
        return Ok(Vec::new());
    };
    let mir::BasicBlockData { ref statements, .. } = mir[location.block];
    if statements.len() == location.statement_index {
        Ok(Vec::new())
    } else {
        let statement = &statements[location.statement_index];
        match statement.kind {
            mir::StatementKind::Assign(box (ref _lhs, ref rhs)) => match rhs {
                &mir::Rvalue::Ref(_, _, ref place)
                | &mir::Rvalue::Discriminant(ref place)
                | &mir::Rvalue::Use(mir::Operand::Copy(ref place))
                | &mir::Rvalue::Use(mir::Operand::Move(ref place)) => Ok(vec![place]),
                &mir::Rvalue::Use(mir::Operand::Constant(_)) => Ok(Vec::new()),
                &mir::Rvalue::Aggregate(_, ref operands) => Ok(operands
                    .iter()
                    .flat_map(|operand| match operand {
                        mir::Operand::Copy(ref place) | mir::Operand::Move(ref place) => Some(place),
                        mir::Operand::Constant(_) => None,
                    })
                    .collect()),
                // slice creation involves an unsize pointer cast like [i32; 3] -> &[i32]
                &mir::Rvalue::Cast(
                    mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize),
                    ref operand,
                    ref ty,
                ) if ty.is_slice() && !ty.is_unsafe_ptr() => {
                    trace!("slice: operand={:?}, ty={:?}", operand, ty);
                    Ok(match operand {
                        mir::Operand::Copy(ref place) | mir::Operand::Move(ref place) => vec![place],
                        mir::Operand::Constant(_) => vec![],
                    })
                },

                &mir::Rvalue::Cast(..) => {
                    // all other loan-casts are unsupported
                    Err(PoloniusInfoError::LoanInUnsupportedStatement(
                        "cast statements that create loans are not supported".to_string(),
                        *location,
                    ))
                },
                x => unreachable!("{:?}", x),
            },
            ref x => unreachable!("{:?}", x),
        }
    }
}

fn compute_loan_conflict_sets(
    procedure: &Procedure,
    loan_position: &HashMap<facts::Loan, mir::Location>,
    borrowck_in_facts: &facts::AllInputFacts,
    borrowck_out_facts: &facts::AllOutputFacts,
) -> Result<HashMap<facts::Loan, HashSet<facts::Loan>>, PoloniusInfoError> {
    trace!("[enter] compute_loan_conflict_sets");

    let mut loan_conflict_sets = HashMap::new();

    let mir = procedure.get_mir();

    for &(_r, loan, _) in &borrowck_in_facts.loan_issued_at {
        loan_conflict_sets.insert(loan, HashSet::new());
    }

    for &(_r, loan_created, point) in &borrowck_in_facts.loan_issued_at {
        let location = loan_position[&loan_created];
        if !procedure.is_reachable_block(location.block)
        /* || procedure.is_spec_block(location.block) */
        {
            continue;
        }
        for borrowed_place in get_borrowed_places(mir, loan_position, loan_created)? {
            if let Some(live_borrows) = borrowck_out_facts.loan_live_at.get(&point) {
                for loan_alive in live_borrows {
                    if loan_created == *loan_alive {
                        continue;
                    }
                    for place in get_borrowed_places(mir, loan_position, *loan_alive)? {
                        if utils::is_prefix(borrowed_place, place) || utils::is_prefix(place, borrowed_place)
                        {
                            loan_conflict_sets.get_mut(&loan_created).unwrap().insert(*loan_alive);
                            loan_conflict_sets.get_mut(loan_alive).unwrap().insert(loan_created);
                        }
                    }
                }
            }
        }
    }

    trace!("[exit] compute_loan_conflict_sets = {:?}", loan_conflict_sets);

    Ok(loan_conflict_sets)
}

impl<'a, 'tcx: 'a> PoloniusInfo<'a, 'tcx> {
    pub fn new(
        env: &'a Environment<'tcx>,
        procedure: &'a Procedure<'tcx>,
    ) -> Result<Self, PoloniusInfoError> {
        let tcx = procedure.get_tcx();
        let def_id = procedure.get_id();
        let mir = procedure.get_mir();

        // Read Polonius facts.
        let facts = env.local_mir_borrowck_facts(def_id.expect_local());

        // // Read relations between region IDs and local variables.
        // let renumber_path = PathBuf::from(config::log_dir())
        //     .join("mir")
        //     .join(format!(
        //         "{}.{}.-------.renumber.0.mir",
        //         tcx.crate_name(LOCAL_CRATE),
        //         def_path.to_filename_friendly_no_crate()
        //     ));
        // debug!("Renumber path: {:?}", renumber_path);
        let place_regions = regions::load_place_regions(mir).unwrap();

        let interner = facts::Interner::new(facts.location_table.take().unwrap());
        let mut all_facts = facts.input_facts.take().unwrap();

        let real_edges = RealEdges::new(mir);
        let loop_info = loops::ProcedureLoops::new(mir, &real_edges);

        Self::disconnect_universal_regions(tcx, mir, &place_regions, &mut all_facts)
            .map_err(|(err, loc)| PoloniusInfoError::PlaceRegionsError(err, loc))?;

        let output = Output::compute(&all_facts, Algorithm::Naive, true);
        let all_facts_without_back_edges =
            remove_back_edges(*all_facts.clone(), &interner, &loop_info.back_edges);
        let output_without_back_edges =
            Output::compute(&all_facts_without_back_edges, Algorithm::Naive, true);

        let loan_position: HashMap<_, _> = all_facts
            .loan_issued_at
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (loan, point.location)
            })
            .collect();
        let loan_at_position: HashMap<_, _> = all_facts
            .loan_issued_at
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (point.location, loan)
            })
            .collect();

        let additional_facts = AdditionalFacts::new(&all_facts, &output);
        let additional_facts_without_back_edges =
            AdditionalFacts::new(&all_facts_without_back_edges, &output_without_back_edges);
        // FIXME: Check whether the new info in Polonius could be used for computing initialization.
        let loan_conflict_sets = compute_loan_conflict_sets(procedure, &loan_position, &all_facts, &output)?;

        let superset = Self::compute_superset(&output);

        let info = Self {
            tcx,
            mir,
            borrowck_in_facts: *all_facts,
            borrowck_out_facts: output,
            interner,
            loan_position,
            loan_at_position,
            place_regions,
            additional_facts,
            additional_facts_no_back: additional_facts_without_back_edges,
            loops: loop_info,
            loan_conflict_sets,
            superset,
        };
        Ok(info)
    }

    fn disconnect_universal_regions(
        tcx: ty::TyCtxt<'tcx>,
        mir: &mir::Body<'tcx>,
        place_regions: &PlaceRegions,
        all_facts: &mut AllInputFacts,
    ) -> Result<(), (PlaceRegionsError, Span)> {
        let mut return_regions = vec![];
        let return_span = mir.local_decls[mir::RETURN_PLACE].source_info.span;
        // find regions for all subplaces (e.g. fields of tuples)
        for place in mir::RETURN_PLACE.all_places(tcx, mir).into_iter() {
            if let Some(region) = place_regions.for_place(place).map_err(|err| (err, return_span))? {
                return_regions.push(region);
            }
        }

        // regions for arguments
        let input_regions = (1..=mir.arg_count)
            .map(mir::Local::new)
            .filter_map(|l| place_regions.for_local(l))
            .collect::<Vec<_>>();

        // Disconnect return regions from universal regions.
        let universal_region = &all_facts.universal_region;
        let is_universal = |r: &facts::Region| universal_region.contains(r);
        let is_input_region = |r: &facts::Region| input_regions.contains(r);
        all_facts
            .subset_base
            .retain(|(r1, r2, _)| (!is_universal(r1) || is_input_region(r2)) && (!is_universal(r2)));

        // Add return regions to universal regions.
        all_facts.universal_region.extend(return_regions);
        Ok(())
    }

    /*
    pub fn compute_region_graph(&self) -> RegionGraph {
        let g = RegionGraph::new();

        // TODO
        // add regions


        //self.borrowck_out_facts.subsets_at

        // how do we use this actually?
        // - compute the transitive closure on the region graph
        // - then just take the direct edges and filter out the ones that are intersected to get
        // the relevant universals and loans.
        //
        // Problem: does this really work in a location-independent way?
        //  - the main thing where we care about that are the subtyping annotations. they really
        //  need to be location-dependent and take into account the kills that happened before.
        //
        //  instead: directly use the computed location-dependent subset relation and filter out
        //  the loans + universals?

        g
    }
    */

    /// Gets the kind of a region: originating from a loan, a universal region, or none of these.
    pub fn get_region_kind(&self, region: facts::Region) -> RegionKind {
        // check if this region is induced by a loan
        let v: Vec<facts::Loan> = self
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter_map(|(r, loan, _)| if r == &region { Some(*loan) } else { None })
            .collect();
        if v.len() == 1 {
            return RegionKind::Loan(v[0]);
        } else if v.len() > 0 {
            unreachable!("A region should not be induced by multiple loans");
        }

        // check if this is a universal region
        if self.borrowck_in_facts.placeholder.iter().any(|(r, _)| r == &region) {
            // this is a universal region
            if region.index() == 0 {
                return RegionKind::Universal(UniversalRegionKind::Static);
            } else if region.index() + 1 == self.borrowck_in_facts.placeholder.len() {
                // TODO check if this does the right thing
                return RegionKind::Universal(UniversalRegionKind::Function);
            } else {
                return RegionKind::Universal(UniversalRegionKind::Local);
            }
        }

        // check if this is a place region
        let mut found_region = false;
        let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
            ty::RegionKind::ReVar(rv) if rv == region => {
                found_region = true;
                r
            },
            _ => r,
        };
        let mut folder = ty::fold::RegionFolder::new(self.tcx, &mut clos);
        for local in self.mir.local_decls.iter() {
            folder.fold_ty(local.ty);
        }

        if found_region { RegionKind::PlaceRegion } else { RegionKind::Unknown }
    }

    pub fn mk_atomic_region(&self, r: facts::Region) -> AtomicRegion {
        let kind = self.get_region_kind(r);
        match kind {
            RegionKind::Loan(l) => AtomicRegion::Loan(l, r),
            RegionKind::PlaceRegion => AtomicRegion::PlaceRegion(r),
            RegionKind::Universal(uk) => AtomicRegion::Universal(uk, r),
            RegionKind::Unknown => AtomicRegion::Unknown(r),
        }
    }

    /// Enumerate local universal regions (excluding the function lifetime).
    pub fn enumerate_local_universal_regions(&self) -> Vec<facts::Region> {
        let mut universals = Vec::new();
        for (r, _) in self.borrowck_in_facts.placeholder.iter() {
            if r.index() == 0 {
                //static
                continue;
            } else if r.index() + 1 == self.borrowck_in_facts.placeholder.len() {
                // function lft
                continue;
            } else {
                universals.push(*r);
            }
        }
        universals
    }

    /// Get new subset constraints generated at a point.
    pub fn get_new_subset_constraints_at_point(
        &self,
        point: facts::PointIndex,
    ) -> Vec<(facts::Region, facts::Region)> {
        let mut constraints = Vec::new();
        for (r1, r2, p) in self.borrowck_in_facts.subset_base.iter() {
            if *p == point {
                constraints.push((*r1, *r2));
            }
        }
        constraints
    }

    /// `r` is the region induced by the loan `l`.
    pub fn get_outliving_atomic_regions_for_loan(
        &self,
        r: facts::Region,
        l: facts::Loan,
        loc: facts::PointIndex,
    ) -> Vec<AtomicRegion> {
        // get set of superset regions
        let a = self.superset.get(&loc);
        if let None = a {
            return Vec::new();
        }
        let b = a.unwrap().get(&r);
        if let None = b {
            return Vec::new();
        }
        let b: &BTreeSet<facts::Region> = b.unwrap();

        let mut v = Vec::new();
        for &region in b.iter() {
            let kind = self.get_region_kind(region);
            match kind {
                RegionKind::Loan(l) => {
                    v.push(AtomicRegion::Loan(l, region));
                },
                RegionKind::Universal(k) => {
                    v.push(AtomicRegion::Universal(k, region));
                },
                _ => {
                    // TODO: this is likely to be incorrect
                },
            }
        }

        // add all loans contained in the region at the current point.
        // these all need to live at least as long as the region, by definition.
        // (they may be killed and become zombies later on, but that does not really change anything)

        // (TODO: handle universals here. I think however that universals that are
        // subset of this one should transitively be contained in the other one, since
        // they are always live??)
        let contained_loans = self.borrowck_out_facts.origin_contains_loan_at(loc);
        let contained_loans: &BTreeSet<facts::Loan> = contained_loans.get(&r).unwrap();
        for &loan in contained_loans.iter() {
            if loan == l {
                continue;
            }
            let r0 = self.get_loan_issued_at_for_loan(loan);
            v.push(AtomicRegion::Loan(loan, r0));
        }

        v
    }

    /// Get regions outliving `r` at point `loc`.
    pub fn get_outliving_atomic_regions(
        &self,
        r: facts::Region,
        loc: facts::PointIndex,
    ) -> Vec<AtomicRegion> {
        // get set of superset regions
        let a = self.superset.get(&loc);
        if let None = a {
            return Vec::new();
        }
        let b = a.unwrap().get(&r);
        if let None = b {
            return Vec::new();
        }
        let b: &BTreeSet<facts::Region> = b.unwrap();

        let mut v = Vec::new();
        for &region in b.iter() {
            let kind = self.get_region_kind(region);
            match kind {
                RegionKind::Loan(l) => {
                    v.push(AtomicRegion::Loan(l, region));
                },
                RegionKind::Universal(k) => {
                    v.push(AtomicRegion::Universal(k, region));
                },
                _ => {},
            }
        }
        // this is another region, essentially an intersection of loans/universals
        // so we try to get the loans that need to outlive it.
        // (TODO: handle universals here. I think however that universals that are
        // subset of this one should transitively be contained in the other one, since
        // they are always live??)
        let contained_loans = self.borrowck_out_facts.origin_contains_loan_at(loc);
        let contained_loans: &BTreeSet<facts::Loan> = contained_loans.get(&r).unwrap();
        for &loan in contained_loans.iter() {
            let r0 = self.get_loan_issued_at_for_loan(loan);
            v.push(AtomicRegion::Loan(loan, r0));
        }

        v
    }

    /// Flips the `subset` relation computed by Polonius for each point.
    pub fn compute_superset(
        output: &facts::AllOutputFacts,
    ) -> HashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Region>>> {
        let subset = &output.subset;
        let mut superset: HashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Region>>> =
            HashMap::new();

        for (&loc, map) in subset.iter() {
            let mut new_map: BTreeMap<facts::Region, BTreeSet<facts::Region>> = BTreeMap::new();
            for (&r1, set) in map.iter() {
                for &r2 in set.iter() {
                    if !new_map.contains_key(&r2) {
                        new_map.insert(r2, BTreeSet::new());
                    }
                    let new_set = new_map.get_mut(&r2).unwrap();
                    new_set.insert(r1);
                }
            }
            superset.insert(loc, new_map);
        }
        superset
    }

    pub fn get_point(&self, location: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let point = facts::Point {
            location,
            typ: point_type,
        };
        self.interner.get_point_index(&point)
    }

    pub fn get_all_loans_kept_alive_by(
        &self,
        point: facts::PointIndex,
        region: facts::Region,
    ) -> (Vec<facts::Loan>, Vec<facts::Loan>) {
        let mut loans =
            self.get_loans_kept_alive_by(point, region, &self.borrowck_out_facts.origin_contains_loan_at);
        let zombie_loans =
            self.get_loans_kept_alive_by(point, region, &self.additional_facts.zombie_requires);
        loans.extend(zombie_loans.iter().cloned());
        (loans, zombie_loans)
    }

    /// Get loans that are kept alive by the given region.
    fn get_loans_kept_alive_by(
        &self,
        point: facts::PointIndex,
        region: facts::Region,
        restricts_map: &FxHashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Loan>>>,
    ) -> Vec<facts::Loan> {
        restricts_map
            .get(&point)
            .as_ref()
            .and_then(|origin_contains_loan_at| origin_contains_loan_at.get(&region))
            .map(|loans| loans.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Get loans that die at the given location.
    pub(crate) fn get_dying_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        self.get_loans_dying_at(location, false)
    }

    /// Get loans that die at the given location.
    pub(crate) fn get_dying_zombie_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        self.get_loans_dying_at(location, true)
    }

    /// Get the atomic region corresponding to a loan.
    pub fn atomic_region_of_loan(&self, l: facts::Loan) -> AtomicRegion {
        let r = self.get_loan_issued_at_for_loan(l);
        AtomicRegion::Loan(l, r)
    }

    /// Get loans including the zombies ``(all_loans, zombie_loans)``.
    pub fn get_all_active_loans(&self, location: mir::Location) -> (Vec<facts::Loan>, Vec<facts::Loan>) {
        let mut loans = self.get_active_loans(location, false);
        let zombie_loans = self.get_active_loans(location, true);
        loans.extend(zombie_loans.iter().cloned());
        (loans, zombie_loans)
    }

    fn get_borrow_live_at(&self, zombie: bool) -> &FxHashMap<facts::PointIndex, Vec<facts::Loan>> {
        if zombie {
            &self.additional_facts.zombie_borrow_live_at
        } else {
            &self.borrowck_out_facts.loan_live_at
        }
    }

    /// Get loans that are active (including those that are about to die) at the given location.
    pub fn get_active_loans(&self, location: mir::Location, zombie: bool) -> Vec<facts::Loan> {
        let loan_live_at = self.get_borrow_live_at(zombie);
        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        let mut loans = if let Some(mid_loans) = loan_live_at.get(&mid_point) {
            let mut mid_loans = mid_loans.clone();
            mid_loans.sort();
            let default_vec = vec![];
            let start_loans = loan_live_at.get(&start_point).unwrap_or(&default_vec);
            let mut start_loans = start_loans.clone();
            start_loans.sort();
            debug!("start_loans = {:?}", start_loans);
            debug!("mid_loans = {:?}", mid_loans);
            // Loans are created in mid point, so mid_point may contain more loans than the start
            // point.
            assert!(start_loans.iter().all(|loan| mid_loans.contains(loan)));

            mid_loans
        } else {
            assert!(loan_live_at.get(&start_point).is_none());
            vec![]
        };
        if !zombie {
            for (_, loan, point) in self.borrowck_in_facts.loan_issued_at.iter() {
                if point == &mid_point && !loans.contains(loan) {
                    loans.push(*loan);
                }
            }
        }
        loans
    }

    /// Get loans including the zombies ``(all_loans, zombie_loans)``.
    pub fn get_all_loans_dying_at(&self, location: mir::Location) -> (Vec<facts::Loan>, Vec<facts::Loan>) {
        let mut loans = self.get_loans_dying_at(location, false);
        let zombie_loans = self.get_loans_dying_at(location, true);
        loans.extend(zombie_loans.iter().cloned());
        (loans, zombie_loans)
    }

    /// Get loans including the zombies ``(all_loans, zombie_loans)``.
    pub fn get_all_loans_dying_between(
        &self,
        initial_loc: mir::Location,
        final_loc: mir::Location,
    ) -> (Vec<facts::Loan>, Vec<facts::Loan>) {
        trace!("[enter] get_all_loans_dying_between initial_loc={:?} final_loc={:?}", initial_loc, final_loc);

        let mut loans = self.get_loans_dying_between(initial_loc, final_loc, false);
        let zombie_loans = self.get_loans_dying_between(initial_loc, final_loc, true);
        loans.extend(zombie_loans.iter().cloned());
        trace!(
            "[exit] get_all_loans_dying_between \
             initial_loc={:?} final_loc={:?} all={:?} zombie={:?}",
            initial_loc,
            final_loc,
            loans,
            zombie_loans
        );
        (loans, zombie_loans)
    }

    /// Get loans that die *at* (that is, exactly after) the given location.
    pub fn get_loans_dying_at(&self, location: mir::Location, zombie: bool) -> Vec<facts::Loan> {
        // TODO: this needs to change.
        // the problem is that we check explcitly that it is currently live, but not at the next
        // point.
        // there are loans dying where there might be no such point in case of branching flow.
        // what's a better rule?
        // maybe: check for loans which are not live now, but in one of the potential predecessors
        // maybe use loans_dying_between?
        // - I can't determine this in a forward-analysis way at a goto.
        // - instead: check predecessors in CFG.

        // loans live at point
        let loan_live_at = self.get_borrow_live_at(zombie);
        let successors = self.get_successors(location);
        let is_return = is_return(self.mir, location);
        let mid_point = self.get_point(location, facts::PointType::Mid);
        // get loans killed at point
        let becoming_zombie_loans =
            self.additional_facts.borrow_become_zombie_at.get(&mid_point).cloned().unwrap_or_default();
        self.get_active_loans(location, zombie)
            .into_iter()
            // active loans which are neither alive in the successor nor returned
            .filter(|loan| {
                // check if it is alive in successor
                let alive_in_successor = successors.iter().any(|successor_location| {
                    let point = self.get_point(*successor_location, facts::PointType::Start);
                    loan_live_at.get(&point).map_or(false, |successor_loans| successor_loans.contains(loan))
                });
                // alive in successor or returned
                !(alive_in_successor || (successors.is_empty() && is_return))
            })
            // filter out zombies (that are killed but where the loan is still ongoing)
            .filter(|loan| !becoming_zombie_loans.contains(loan))
            .collect()
    }

    /// Get loans that die between two consecutive locations.
    pub fn get_loans_dying_between(
        &self,
        initial_loc: mir::Location,
        final_loc: mir::Location,
        zombie: bool,
    ) -> Vec<facts::Loan> {
        trace!("[enter] get_loans_dying_between {:?}, {:?}, {}", initial_loc, final_loc, zombie);
        debug_assert!(self.get_successors(initial_loc).contains(&final_loc));
        let mid_point = self.get_point(initial_loc, facts::PointType::Mid);
        let becoming_zombie_loans =
            self.additional_facts.borrow_become_zombie_at.get(&mid_point).cloned().unwrap_or_default();
        trace!("becoming_zombie_loans={:?}", becoming_zombie_loans);
        let final_loc_point = self.get_point(final_loc, facts::PointType::Start);
        trace!("loan_live_at final {:?}", self.borrowck_out_facts.loan_live_at.get(&final_loc_point));
        let dying_loans = self
            .get_active_loans(initial_loc, zombie)
            .into_iter()
            .filter(|loan| {
                self.get_borrow_live_at(zombie)
                    .get(&final_loc_point)
                    .map_or(true, |successor_loans| !successor_loans.contains(loan))
            })
            .filter(|loan| !becoming_zombie_loans.contains(loan))
            .collect();
        trace!(
            "[exit] get_loans_dying_between {:?}, {:?}, {}, dying_loans={:?}",
            initial_loc,
            final_loc,
            zombie,
            dying_loans
        );
        dying_loans
    }

    //     /// Get loans including the zombies ``(all_loans, zombie_loans)``.
    //     pub fn get_all_loans_dying_before(
    //         &self,
    //         location: mir::Location,
    //     ) -> (Vec<facts::Loan>, Vec<facts::Loan>) { let mut loans = self.get_loans_dying_before(location,
    //       false); let zombie_loans = self.get_loans_dying_before(location, true);
    //       loans.extend(zombie_loans.iter().cloned()); (loans, zombie_loans)
    //     }

    //     /// Get loans that die exactly before the given location, but not *at* any of the predecessors.
    //     /// Note: we don't handle a loan that dies just in a subset of the incoming CFG edges.
    //     pub fn get_loans_dying_before(
    //         &self,
    //         location: mir::Location,
    //         zombie: bool,
    //     ) -> Vec<facts::Loan> { let mut predecessors = self.get_predecessors(location); let mut
    //       dying_before: Option<HashSet<facts::Loan>> = None; for predecessor in predecessors.drain(..) {
    //       let dying_at_predecessor: HashSet<_> = HashSet::from_iter(self.get_loans_dying_at(predecessor,
    //       zombie)); let dying_between: HashSet<_> =
    //       HashSet::from_iter(self.get_loans_dying_between(predecessor, location, zombie)); let
    //       dying_before_loc: HashSet<_> = dying_between .difference(&dying_at_predecessor) .cloned()
    //       .collect(); if let Some(ref dying_before_content) = dying_before { if dying_before_content !=
    //       &dying_before_loc { debug!("Incoming CFG edges have different expiring loans"); return vec![]; }
    //       } else { dying_before = Some(dying_before_loc); } } dying_before .map(|d|
    //       d.into_iter().collect()) .unwrap_or(vec![])
    //     }

    pub fn get_conflicting_loans(&self, loan: facts::Loan) -> Vec<facts::Loan> {
        self.loan_conflict_sets
            .get(&loan)
            .map(|set| set.iter().cloned().collect())
            .unwrap_or_default()
    }

    pub fn get_alive_conflicting_loans(
        &self,
        loan: facts::Loan,
        location: mir::Location,
    ) -> Vec<facts::Loan> {
        if let Some(all_conflicting_loans) = self.loan_conflict_sets.get(&loan) {
            let point = self.get_point(location, facts::PointType::Mid);
            if let Some(alive_loans) = self.borrowck_out_facts.loan_live_at.get(&point) {
                let alive_conflicting_loans =
                    all_conflicting_loans.iter().filter(|loan| alive_loans.contains(loan)).cloned().collect();
                trace!(
                    "get_alive_conflicting_loans({:?}, {:?}) = {:?}",
                    loan,
                    location,
                    alive_conflicting_loans
                );
                return alive_conflicting_loans;
            }
        }
        Vec::new()
    }

    /// Get the location at which a loan is created, if possible
    pub fn get_loan_location(&self, loan: &facts::Loan) -> Option<mir::Location> {
        self.loan_position.get(loan).map(|r| *r)
    }

    /// Get the loan that gets created at a location.
    /// TODO: for aggregates, this only finds one loan
    pub fn get_loan_at_location(&self, location: mir::Location) -> facts::Loan {
        self.loan_at_position[&location]
    }

    /// Get the loan that gets created at a location.
    /// TODO: for aggregates, this only finds one loan
    pub fn get_optional_loan_at_location(&self, location: mir::Location) -> Option<facts::Loan> {
        if self.loan_at_position.contains_key(&location) {
            Some(self.loan_at_position[&location])
        } else {
            None
        }
    }

    /// Get a map from loans to locations at which they were created.
    pub fn loan_locations(&self) -> HashMap<facts::Loan, mir::Location> {
        self.loan_position.iter().map(|(loan, location)| (*loan, *location)).collect()
    }

    /// Convert a facts::Loan to LoanPlaces<'tcx> (if possible)
    pub fn get_loan_places(&self, loan: &facts::Loan) -> Result<Option<LoanPlaces<'tcx>>, PlaceRegionsError> {
        // Implementing get_loan_places is a bit more complicated when there are tuples. This is
        // because an assignment like
        //   _3 = (move _4, move _5)
        // creates two loans on the same line (if both fields of _3 are references), let's call
        // them L0 and L1. This means we can't just inspect the assign statement to figure out the
        // loan places for L0 -- we also have to find out which field of _3 L0 is associated with.
        // This happens in get_assignment_for_loan, which returns an atomic assignment for a given
        // loan. For the example above, get_assignment_for_loan(L0) would be _3.0 = move _4 and
        // get_assignment_for_loan(L1) would be _3.1 = move _5. Using these atomic assignments, we
        // can simply read off the loan places as before.

        let assignment = if let Some(loan_assignment) = self.get_assignment_for_loan(*loan)? {
            loan_assignment
        } else {
            return Ok(None);
        };
        let (dest, source) = assignment.as_assign().unwrap();
        let dest = dest;
        let source = source.clone();
        let location = self.loan_position[loan];
        Ok(Some(LoanPlaces {
            dest,
            source,
            location,
        }))
    }

    /// Returns the atomic assignment that created a loan. Refer to the documentation of
    /// SplitAggregateAssignment for more information on what an atomic assignment is.
    pub fn get_assignment_for_loan(
        &self,
        loan: facts::Loan,
    ) -> Result<Option<mir::Statement<'tcx>>, PlaceRegionsError> {
        let &location = if let Some(loc) = self.loan_position.get(&loan) {
            loc
        } else {
            return Ok(None);
        };
        let stmt = if let Some(s) = self.mir.statement_at(location) {
            s.clone()
        } else {
            return Ok(None);
        };
        let mut assignments: Vec<_> = stmt.split_assignment(self.tcx, self.mir);

        // TODO: This is a workaround. It seems like some local variables don't have a local
        //  variable declaration in the MIR. One example of this can be observed in the
        //  implementation of the clone method in `prusti/tests/verify/pass/copy/generics.rs`. We
        //  don't have region information for these local variables, which is why the code below
        //  would drop all assignments and return `None`. So if there is only one possible
        //  assignment that may have created a loan, we return it directly without inspecting the
        //  region information. Of course once a local variable that is a tuple is not declared
        //  explicitly, this will fail again.
        if assignments.len() == 1 {
            return Ok(assignments.pop());
        }

        let region = self.get_loan_issued_at_for_loan(loan);

        // Drops all assignments where the LHS region isn't equal to the region of the loan we're
        // interested in. The reason this works is a bit subtle. First, if execution reaches this
        // point, the original assignment must have been an aggregate assignment, because in the
        // case of other assignments the function returns early in the `assignments.len() == 1`
        // check. For a reference moved into an aggregate via an aggregate assignment, the borrow
        // region immediately associated with the fake loan created for this reference move is the
        // region associated with the left-hand side place this reference is moved into. For
        // example, consider the following assignment:
        //     let _3 = (move _4, move _5);
        // The fake loan created for "move_4" is associated with the region of the place _3.0, and
        // for "move_5" the fake loan is associated with the region of the place _3.1. This
        // correspondence allows us to identify the correct atomic assignment by comparing the
        // region of the left-hand side with the borrow region of the loan. This is hacky, and a
        // solution that does not rely on such subtleties would be much better.
        let mut retained_assignments = vec![];
        for stmt in assignments.into_iter() {
            let (lhs, _) =
                stmt.as_assign().unwrap_or_else(|| unreachable!("Borrow starts at statement {:?}", stmt));
            if self.place_regions.for_place(lhs)? == Some(region) {
                retained_assignments.push(stmt);
            }
        }

        Ok(retained_assignments.pop())
    }

    /// Returns the borrow region that requires the terms of the given loan to be enforced. This
    /// does *not* return all regions that require the terms of the loan to be enforced. So for the
    /// following MIR code, it returns the region '2rv but not the region '1rv:
    ///
    /// ```ignore
    /// let _1: &'1rv u32;
    /// _1 = &'2rv 123;
    /// ```
    fn get_loan_issued_at_for_loan(&self, loan: facts::Loan) -> facts::Region {
        let location = self.get_loan_location(&loan).unwrap();
        let point = self.get_point(location, PointType::Mid);
        let regions = self
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter_map(|&(r, l, p)| if p == point && l == loan { Some(r) } else { None })
            .collect::<Vec<_>>();
        if regions.len() == 1 {
            regions[0]
        } else {
            unreachable!(
                "Cannot determine region for loan {:?}, because there is not exactly one possible option: {:?}",
                loan, regions
            )
        }
    }

    /// Find minimal elements that are the (reborrow) tree roots.
    fn find_loan_roots(&self, loans: &[facts::Loan]) -> Vec<facts::Loan> {
        let mut roots = Vec::new();
        for &loan in loans.iter() {
            let is_smallest = !loans
                .iter()
                .any(|&other_loan| self.additional_facts.reborrows.contains(&(other_loan, loan)));
            debug!("loan={:?} is_smallest={}", loan, is_smallest);
            if is_smallest {
                roots.push(loan);
            }
        }
        roots
    }

    /// Find a variable that has the given region in its type.
    pub fn find_variable(&self, _region: facts::Region) -> Option<mir::Local> {
        // TODO
        None
    }

    //     /// Find variable that was moved into the function.
    //     pub fn get_moved_variable(&self, kind: &ReborrowingKind) -> mir::Local {
    //         match kind {
    //             ReborrowingKind::ArgumentMove { ref loan } => {
    //                 let index = self
    //                     .borrowck_in_facts
    //                     .loan_issued_at
    //                     .iter()
    //                     .position(|(_, l, _)| l == loan)
    //                     .unwrap();
    //                 let (region, _, _) = self.borrowck_in_facts.loan_issued_at[index];
    //                 let variable = self.find_variable(region).unwrap();
    //                 variable
    //             }
    //             _ => panic!("This function can be called only with ReborrowingKind::ArgumentMove."),
    //         }
    //     }

    /// Get loops in which loans are defined (if any).
    pub fn get_loan_loops(
        &self,
        loans: &[facts::Loan],
    ) -> Result<Vec<(facts::Loan, mir::BasicBlock)>, PoloniusInfoError> {
        let pairs: Vec<_> = loans
            .iter()
            .flat_map(|loan| {
                let loan_location = if let Some(location) = self.loan_position.get(loan) {
                    location
                } else {
                    // FIXME (Vytautas): This is likely to be wrong.
                    debug!("ERROR: not found for loan: {:?}", loan);
                    return None;
                };
                self.loops.get_loop_head(loan_location.block).map(|loop_head| (*loan, loop_head))
            })
            .collect();
        for (loan1, loop1) in pairs.iter() {
            let location1 = self.loan_position[loan1];
            for (loan2, loop2) in pairs.iter() {
                let location2 = self.loan_position[loan2];
                if loop1 != loop2 {
                    return Err(PoloniusInfoError::LoansInNestedLoops(location1, *loop1, location2, *loop2));
                }
            }
        }
        Ok(pairs)
    }

    fn get_successors(&self, location: mir::Location) -> Vec<mir::Location> {
        let statements_len = self.mir[location.block].statements.len();
        if location.statement_index < statements_len {
            vec![mir::Location {
                statement_index: location.statement_index + 1,
                ..location
            }]
        } else {
            let mut successors = Vec::new();
            for successor in self.mir[location.block].terminator.as_ref().unwrap().successors() {
                successors.push(mir::Location {
                    block: successor,
                    statement_index: 0,
                });
            }
            successors
        }
    }

    //     fn get_predecessors(&self, location: mir::Location) -> Vec<mir::Location> {
    //         if location.statement_index > 0 {
    //             vec![mir::Location {
    //                 statement_index: location.statement_index - 1,
    //                 ..location
    //             }]
    //         } else {
    //             debug_assert_eq!(location.statement_index, 0);
    //             let mut predecessors = HashSet::new();
    //             for (bbi, bb_data) in self.mir.basic_blocks().iter_enumerated() {
    //                 for &bb_successor in bb_data.terminator().successors() {
    //                     if bb_successor == location.block {
    //                         predecessors.insert(mir::Location {
    //                             block: bbi,
    //                             statement_index: bb_data.statements.len(),
    //                         });
    //                     }
    //                 }
    //             }
    //             predecessors.into_iter().collect()
    //         }
    //     }
}

/// Check if the statement is assignment.
fn is_assignment(mir: &mir::Body<'_>, location: mir::Location) -> bool {
    let mir::BasicBlockData { ref statements, .. } = mir[location.block];
    if statements.len() == location.statement_index {
        return false;
    }
    matches!(statements[location.statement_index].kind, mir::StatementKind::Assign { .. })
}

/// Check if the terminator is return.
fn is_return(mir: &mir::Body<'_>, location: mir::Location) -> bool {
    let mir::BasicBlockData {
        ref statements,
        ref terminator,
        ..
    } = mir[location.block];
    if statements.len() != location.statement_index {
        return false;
    }
    matches!(terminator.as_ref().unwrap().kind, mir::TerminatorKind::Return)
}

fn is_call(mir: &mir::Body<'_>, location: mir::Location) -> bool {
    let mir::BasicBlockData {
        ref statements,
        ref terminator,
        ..
    } = mir[location.block];
    if statements.len() != location.statement_index {
        return false;
    }
    matches!(terminator.as_ref().unwrap().kind, mir::TerminatorKind::Call { .. })
}

/// Extract the call terminator at the location. Otherwise return None.
fn get_call_destination<'tcx>(mir: &mir::Body<'tcx>, location: mir::Location) -> Option<mir::Place<'tcx>> {
    let mir::BasicBlockData {
        ref statements,
        ref terminator,
        ..
    } = mir[location.block];
    if statements.len() != location.statement_index {
        return None;
    }
    match terminator.as_ref().unwrap().kind {
        mir::TerminatorKind::Call {
            ref destination, ..
        } => Some(*destination),
        ref x => {
            panic!("Expected call, got {:?} at {:?}", x, location);
        },
    }
}

/// Extract reference-typed arguments of the call at the given location.
fn get_call_arguments(mir: &mir::Body<'_>, location: mir::Location) -> Vec<mir::Local> {
    let mir::BasicBlockData {
        ref statements,
        ref terminator,
        ..
    } = mir[location.block];
    assert!(statements.len() == location.statement_index);
    match terminator.as_ref().unwrap().kind {
        mir::TerminatorKind::Call { ref args, .. } => {
            let mut reference_args = Vec::new();
            for arg in args {
                match arg {
                    mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                        if place.projection.len() == 0 {
                            reference_args.push(place.local);
                        }
                    },
                    mir::Operand::Constant(_) => {},
                }
            }
            reference_args
        },
        ref x => {
            panic!("Expected call, got {:?} at {:?}", x, location);
        },
    }
}

/// Additional facts derived from the borrow checker facts.
pub struct AdditionalFacts {
    /// A list of loans sorted by id.
    pub loans: Vec<facts::Loan>,
    /// The ``reborrows`` facts are needed for removing “fake” loans: at
    /// a specific program point there are often more than one loan active,
    /// but we are interested in only one of them, which is the original one.
    /// Therefore, we find all loans that are reborrows of the original loan
    /// and remove them. Reborrowing is defined as follows:
    ///
    /// ```datalog
    /// reborrows(Loan, Loan);
    /// reborrows(L1, L2) :-
    ///     loan_issued_at(R, L1, P),
    ///     origin_contains_loan_at(R, P, L2).
    /// reborrows(L1, L3) :-
    ///     reborrows(L1, L2),
    ///     reborrows(L2, L3).
    /// ```
    pub reborrows: Vec<(facts::Loan, facts::Loan)>,
    /// Non-transitive `reborrows`.
    pub reborrows_direct: Vec<(facts::Loan, facts::Loan)>,
    /// The ``zombie_requires`` facts are ``requires`` facts for the loans
    /// that were loan_killed_at.
    ///
    /// ```datalog
    /// zombie_requires(Region, Loan, Point);
    /// zombie_requires(R, L, Q) :-
    ///     requires(R, L, P),
    ///     loan_killed_at(L, P),
    ///     cfg_edge(P, Q),
    ///     origin_live_on_entry(R, Q).
    /// zombie_requires(R2, L, P) :-
    ///     zombie_requires(R1, L, P),
    ///     subset(R1, R2, P).
    /// zombie_requires(R, L, Q) :-
    ///     zombie_requires(R, L, P),
    ///     cfg_edge(P, Q),
    ///     origin_live_on_entry(R, Q).
    /// ```
    pub zombie_requires: FxHashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Loan>>>,
    /// The ``zombie_borrow_live_at`` facts are ``loan_live_at`` facts
    /// for the loans that were loan_killed_at.
    ///
    /// ```datalog
    /// zombie_borrow_live_at(L, P) :-
    ///     zombie_requires(R, L, P),
    ///     origin_live_on_entry(R, P).
    /// ```
    pub zombie_borrow_live_at: FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
    /// Which loans were loan_killed_at (become zombies) at a given point.
    pub borrow_become_zombie_at: FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
}

impl AdditionalFacts {
    /// Derive ``zombie_requires``.
    #[allow(clippy::type_complexity)]
    fn derive_zombie_requires(
        all_facts: &facts::AllInputFacts,
        output: &facts::AllOutputFacts,
    ) -> (
        FxHashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Loan>>>,
        FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
        FxHashMap<facts::PointIndex, Vec<facts::Loan>>,
    ) {
        use datafrog::{Iteration, Relation};

        use self::facts::{Loan, PointIndex as Point, Region};

        let mut iteration = Iteration::new();

        // Variables that are outputs of our computation.
        let zombie_requires = iteration.variable::<(Region, Loan, Point)>("zombie_requires");
        let zombie_borrow_live_at = iteration.variable::<(Loan, Point)>("zombie_borrow_live_at");
        let borrow_become_zombie_at = iteration.variable::<(Loan, Point)>("borrow_become_zombie_at");

        // Variables for initial data.
        let requires_lp = iteration.variable::<((Loan, Point), Region)>("requires_lp");
        let loan_killed_at = iteration.variable::<((Loan, Point), ())>("loan_killed_at");
        let cfg_edge_p = iteration.variable::<(Point, Point)>("cfg_edge_p");
        let origin_live_on_entry = iteration.variable::<((Region, Point), ())>("origin_live_on_entry");
        let subset_r1p = iteration.variable::<((Region, Point), Region)>("subset_r1p");

        // Temporaries as we perform a multi-way join.
        let zombie_requires_rp = iteration.variable_indistinct("zombie_requires_rp");
        let zombie_requires_p = iteration.variable_indistinct("zombie_requires_p");
        let zombie_requires_1 = iteration.variable_indistinct("zombie_requires_1");
        let zombie_requires_2 = iteration.variable_indistinct("zombie_requires_2");
        let zombie_requires_3 = iteration.variable_indistinct("zombie_requires_3");
        let zombie_requires_4 = iteration.variable_indistinct("zombie_requires_4");

        // Load initial facts.
        requires_lp.insert(Relation::from_iter(output.origin_contains_loan_at.iter().flat_map(
            |(&point, region_map)| {
                region_map
                    .iter()
                    .flat_map(move |(&region, loans)| loans.iter().map(move |&loan| ((loan, point), region)))
            },
        )));
        loan_killed_at.insert(Relation::from_iter(
            all_facts.loan_killed_at.iter().map(|&(loan, point)| ((loan, point), ())),
        ));
        cfg_edge_p.insert(all_facts.cfg_edge.clone().into());

        let origin_live_on_entry_vec = {
            output.origin_live_on_entry.iter().flat_map(|(point, origins)| {
                let points: Vec<_> = origins.iter().cloned().map(|origin| (origin, *point)).collect();
                points
            })
            // let mut origin_live_on_entry = output.origin_live_on_entry.clone();
            // let all_points: BTreeSet<Point> = all_facts
            //     .cfg_edge
            //     .iter()
            //     .map(|&(p, _)| p)
            //     .chain(all_facts.cfg_edge.iter().map(|&(_, q)| q))
            //     .collect();

            // for &r in &all_facts.universal_region {
            //     for &p in &all_points {
            //          FIXME: Check if already added.
            //         origin_live_on_entry.push((r, p));
            //     }
            // }
            // origin_live_on_entry
        };
        origin_live_on_entry.insert(Relation::from_iter(origin_live_on_entry_vec.map(|(r, p)| ((r, p), ()))));
        subset_r1p.insert(Relation::from_iter(output.subset.iter().flat_map(|(&point, subset_map)| {
            subset_map.iter().flat_map(move |(&region1, regions)| {
                regions.iter().map(move |&region2| ((region1, point), region2))
            })
        })));

        while iteration.changed() {
            zombie_requires_rp.from_map(&zombie_requires, |&(r, l, p)| ((r, p), l));
            zombie_requires_p.from_map(&zombie_requires, |&(r, l, p)| (p, (l, r)));

            // zombie_requires(R, L, Q) :-
            //     requires(R, L, P),
            //     loan_killed_at(L, P),
            //     cfg_edge(P, Q),
            //     origin_live_on_entry(R, Q).
            zombie_requires_1.from_join(&requires_lp, &loan_killed_at, |&(l, p), &r, _| (p, (l, r)));
            zombie_requires_2.from_join(&zombie_requires_1, &cfg_edge_p, |&_p, &(l, r), &q| ((r, q), l));
            zombie_requires
                .from_join(&zombie_requires_2, &origin_live_on_entry, |&(r, q), &l, &()| (r, l, q));
            zombie_requires_4.from_join(&zombie_requires_1, &cfg_edge_p, |&p, &(l, r), &q| ((r, q), (p, l)));
            borrow_become_zombie_at.from_join(
                &zombie_requires_4,
                &origin_live_on_entry,
                |_, &(p, l), &()| (l, p),
            );

            // zombie_requires(R2, L, P) :-
            //     zombie_requires(R1, L, P),
            //     subset(R1, R2, P).
            zombie_requires.from_join(&zombie_requires_rp, &subset_r1p, |&(_r1, p), &b, &r2| (r2, b, p));

            // zombie_requires(R, L, Q) :-
            //     zombie_requires(R, L, P),
            //     cfg_edge(P, Q),
            //     origin_live_on_entry(R, Q).
            zombie_requires_3.from_join(&zombie_requires_p, &cfg_edge_p, |&_p, &(l, r), &q| ((r, q), l));
            zombie_requires
                .from_join(&zombie_requires_3, &origin_live_on_entry, |&(r, q), &l, &()| (r, l, q));

            // zombie_borrow_live_at(L, P) :-
            //     zombie_requires(R, L, P),
            //     origin_live_on_entry(R, P).
            zombie_borrow_live_at.from_join(
                &zombie_requires_rp,
                &origin_live_on_entry,
                |&(_r, p), &l, &()| (l, p),
            );
        }

        let zombie_requires = zombie_requires.complete();
        let mut zombie_requires_map = FxHashMap::default();
        for (region, loan, point) in &zombie_requires.elements {
            zombie_requires_map
                .entry(*point)
                .or_insert_with(BTreeMap::default)
                .entry(*region)
                .or_insert_with(BTreeSet::new)
                .insert(*loan);
        }

        let zombie_borrow_live_at = zombie_borrow_live_at.complete();
        let mut zombie_borrow_live_at_map = FxHashMap::default();
        for (loan, point) in &zombie_borrow_live_at.elements {
            zombie_borrow_live_at_map.entry(*point).or_insert_with(Vec::new).push(*loan);
        }

        let borrow_become_zombie_at = borrow_become_zombie_at.complete();
        let mut borrow_become_zombie_at_map = FxHashMap::default();
        for (loan, point) in &borrow_become_zombie_at.elements {
            borrow_become_zombie_at_map.entry(*point).or_insert_with(Vec::new).push(*loan);
        }

        (zombie_requires_map, zombie_borrow_live_at_map, borrow_become_zombie_at_map)
    }

    /// Derive additional facts from the borrow checker facts.
    pub fn new(all_facts: &facts::AllInputFacts, output: &facts::AllOutputFacts) -> AdditionalFacts {
        let (zombie_requires, zombie_borrow_live_at, borrow_become_zombie_at) =
            Self::derive_zombie_requires(all_facts, output);

        let origin_contains_loan_at = output.origin_contains_loan_at.iter().chain(zombie_requires.iter());
        let loan_issued_ats = all_facts.loan_issued_at.iter();
        let reborrows = Self::load_reborrows(origin_contains_loan_at, loan_issued_ats);

        let mut reborrows = Self::transitive_closure(reborrows);

        // Remove reflexive edges.
        reborrows.retain(|(l1, l2)| l1 != l2);

        // A non-transitive version of reborrows.
        let reborrows_direct = Self::derive_nontransitive(&reborrows);

        // Compute the sorted list of all loans.
        let mut loans: Vec<_> = all_facts.loan_issued_at.iter().map(|&(_, l, _)| l).collect();
        loans.sort();

        AdditionalFacts {
            loans,
            reborrows,
            reborrows_direct,
            zombie_requires,
            zombie_borrow_live_at,
            borrow_become_zombie_at,
        }
    }

    fn load_reborrows<'a>(
        origin_contains_loan_at: impl Iterator<
            Item = (&'a facts::PointIndex, &'a BTreeMap<facts::Region, BTreeSet<facts::Loan>>),
        >,
        loan_issued_ats: impl Iterator<Item = &'a (facts::Region, facts::Loan, facts::PointIndex)>,
    ) -> Vec<(facts::Loan, facts::Loan)> {
        use self::facts::{Loan, PointIndex as Point, Region};

        let mut iteration = datafrog::Iteration::new();

        // Variables that are outputs of our computation.
        let v_reborrows = iteration.variable::<(Loan, Loan)>("reborrows");

        // Variables for initial data.
        let v_restricts = iteration.variable::<((Point, Region), Loan)>("origin_contains_loan_at");
        let v_loan_issued_at = iteration.variable::<((Point, Region), Loan)>("loan_issued_at");

        // Load initial data.
        let restricts_items = origin_contains_loan_at.flat_map(|(&point, region_map)| {
            region_map
                .iter()
                .flat_map(move |(&region, loans)| loans.iter().map(move |&loan| ((point, region), loan)))
        });
        v_restricts.insert(datafrog::Relation::from_iter(restricts_items));

        let loan_issued_at_items = loan_issued_ats.map(|&(r, l, p)| ((p, r), l));
        v_loan_issued_at.insert(datafrog::Relation::from_iter(loan_issued_at_items));

        while iteration.changed() {
            // reborrows(L1, L2) :-
            //   loan_issued_at(R, L1, P),
            //   origin_contains_loan_at(R, P, L2).
            v_reborrows.from_join(&v_loan_issued_at, &v_restricts, |_, &l1, &l2| (l1, l2));
        }

        let reborrows = v_reborrows.complete().elements;

        reborrows
    }

    fn transitive_closure(reborrows: Vec<(facts::Loan, facts::Loan)>) -> Vec<(facts::Loan, facts::Loan)> {
        let mut iteration = datafrog::Iteration::new();

        let v_reborrows = iteration.variable("reborrows");
        v_reborrows.insert(reborrows.into());

        let v_reborrows_1 = iteration.variable_indistinct("reborrows_1");
        let v_reborrows_2 = iteration.variable_indistinct("reborrows_2");

        // Compute transitive closure of reborrows:
        // reborrows(L1, L3) :-
        //   reborrows(L1, L2),
        //   reborrows(L2, L3).
        while iteration.changed() {
            v_reborrows_1.from_map(&v_reborrows, |&(l1, l2)| (l2, l1));
            v_reborrows_2.from_map(&v_reborrows, |&(l2, l3)| (l2, l3));
            v_reborrows.from_join(&v_reborrows_1, &v_reborrows_2, |_, &l1, &l3| (l1, l3));
        }

        v_reborrows.complete().elements
    }

    fn derive_nontransitive(reborrows: &[(facts::Loan, facts::Loan)]) -> Vec<(facts::Loan, facts::Loan)> {
        reborrows
            .iter()
            .cloned()
            .filter(|&(l1, l2)| !reborrows.iter().any(|&(l3, l4)| l4 == l2 && reborrows.contains(&(l1, l3))))
            .collect()
    }
}
