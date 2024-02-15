// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use datafrog as df;

pub use crate::base::*;
/// The InclusionTracker maintains a set of dynamic lifetime inclusions holding in the RefinedRust
/// type system at given program points.
/// This is used for the lifetime annotation generation.
use crate::environment::polonius_info::PoloniusInfo;
/// Track inclusions between regions that are known to hold at the current point of the translation.
/// Distinguishes static and dynamic inclusions for the purpose of the translation.
pub struct InclusionTracker<'a, 'tcx: 'a> {
    info: &'a PoloniusInfo<'a, 'tcx>,

    // base facts about static inclusion
    static_incl_base: Vec<(Region, Region, PointIndex)>,
    // base facts about dynamic inclusion
    dynamic_incl_base: Vec<(Region, Region, PointIndex)>,
    // transitive closure of static inclusion facts
    static_incl: Option<Vec<(Region, Region, PointIndex)>>,
    // transitive closure of both static and dynamic inclusion
    full_incl: Option<Vec<(Region, Region, PointIndex)>>,

    // barriers (r, p) where strong writes in our type system are happening.
    // constraints on region r will not propagate past p.
    // Assumption: we will put barriers on mid-points.
    barriers: Vec<(Region, PointIndex)>,
    // set after a new barrier is pushed to signify that all previous computations are now invalidated
    fully_invalidated: bool,
    // set after a new constraint is added
    invalidated: bool,
}

impl<'a, 'tcx: 'a> InclusionTracker<'a, 'tcx> {
    pub fn new(info: &'a PoloniusInfo<'a, 'tcx>) -> Self {
        InclusionTracker {
            info,
            static_incl_base: Vec::new(),
            dynamic_incl_base: Vec::new(),
            static_incl: None,
            full_incl: None,
            barriers: Vec::new(),
            fully_invalidated: true,
            invalidated: true,
        }
    }

    /// Add a basic static inclusion fact.
    pub fn add_static_inclusion(&mut self, a: Region, b: Region, p: PointIndex) {
        self.static_incl_base.push((a, b, p));
        self.invalidated = true;
    }

    /// Add a basic dynamic inclusion fact.
    pub fn add_dynamic_inclusion(&mut self, a: Region, b: Region, p: PointIndex) {
        self.dynamic_incl_base.push((a, b, p));
        self.invalidated = true;
    }

    /// Add a barrier for propagation of constraints on r at p.
    /// Use for points where strong writes happen in our type system.
    pub fn add_barrier(&mut self, r: Region, p: PointIndex) {
        self.barriers.push((r, p));
        self.invalidated = true;
        self.fully_invalidated = true;
    }

    /// Recompute static inclusion constraints.
    fn recompute_static_incl(&mut self) {
        let mut iteration = df::Iteration::new();

        // static_incl(r1, r2, p) :- static_incl_base(r1, r2, p)
        let static_incl = iteration.variable::<(Region, Region, PointIndex)>("static_incl");
        static_incl.extend(self.static_incl_base.clone());
        if !self.fully_invalidated && self.static_incl.is_some() {
            static_incl.extend(self.static_incl.take().unwrap().into_iter());
        }

        self.compute_transitive_closure(&mut iteration, &static_incl);

        let static_incl = static_incl.complete();
        self.static_incl = Some(static_incl.elements);
        self.fully_invalidated = false;
        self.invalidated = false;
    }

    fn compute_transitive_closure(
        &self,
        iteration: &mut df::Iteration,
        base: &df::Variable<(Region, Region, PointIndex)>,
    ) {
        let incl1 = iteration.variable_indistinct::<(PointIndex, (Region, Region))>("incl1");
        let incl2 = iteration.variable_indistinct::<((Region, PointIndex), Region)>("incl2");
        let incl3 = iteration.variable_indistinct::<((Region, PointIndex), Region)>("incl3");

        let incl4 = iteration.variable_indistinct::<((Region, PointIndex), Region)>("incl4");
        let incl5 = iteration.variable_indistinct::<((Region, PointIndex), Region)>("incl5");
        //let incl2 = iteration.variable_indistinct::<((Region, PointIndex), Region)>("incl4");

        let barriers = df::Relation::from_iter(self.barriers.iter().map(|(r, p)| (*r, *p)));

        let cfg_edge = iteration.variable::<(PointIndex, PointIndex)>("cfg_edge");
        cfg_edge.extend(self.info.borrowck_in_facts.cfg_edge.iter());

        while iteration.changed() {
            incl4.from_map(&base, |(r1, r2, p)| ((*r2, *p), *r1));
            incl5.from_map(&base, |(r2, r3, p)| ((*r2, *p), *r3));

            // incl(r1, r2, p2) :- incl(r1, r2, p1), cfg_edge(p1, p2), !barrier(r1, p2), !barrier(r2, p2)
            // realized by:
            // incl1(p, (r1, r2)) := incl(r1, r2, p)
            // incl2((r1, p2), r2) :- incl1(p1, (r1, r2)), cfg_edge(p1, p2)
            // incl3((r2, p2), r1) :- incl2((r1, p2), r2), !barrier(r1, p2)
            // incl(r1, r2, p2) :- incl3((r2, p2), r1), !barrier(r2, p2)
            incl1.from_map(&base, |(r1, r2, p)| (*p, (*r1, *r2)));
            incl2.from_join(&cfg_edge, &incl1, |_p1, p2, (r1, r2)| ((*r1, *p2), *r2));
            incl3.from_antijoin(&incl2, &barriers, |(r1, p2), r2| ((*r2, *p2), *r1));
            base.from_antijoin(&incl3, &barriers, |(r2, p2), r1| (*r1, *r2, *p2));

            // incl(r1, r3, p) :- incl(r1, r2, p), incl(r2, r3, p)
            // realized by:
            // incl4((r2, p), r1) :- incl(r1, r2, p)
            // incl5((r2, p), r3) :- incl(r2, r3, p)
            // incl(r1, r3, p) :- incl4((r2, p), r1), incl5((r2, p), r3)
            base.from_join(&incl4, &incl5, |(_r2, p), r1, r3| (*r1, *r3, *p));
        }
    }

    /// Recompute all inclusion constraints.
    pub fn recompute(&mut self) {
        self.recompute_static_incl();

        let mut iteration = df::Iteration::new();

        // incl(r1, r2, p) :- static_incl_base(r1, r2, p)
        // incl(r1, r2, p) :- dynamic_incl_base(r1, r2, p)
        let incl = iteration.variable::<(Region, Region, PointIndex)>("incl");
        if !self.fully_invalidated && self.full_incl.is_some() {
            incl.extend(self.full_incl.take().unwrap().into_iter());
        }
        incl.extend(self.static_incl.as_ref().unwrap().clone());
        incl.extend(self.dynamic_incl_base.clone());

        self.compute_transitive_closure(&mut iteration, &incl);

        let incl = incl.complete();
        self.full_incl = Some(incl.elements);
        self.fully_invalidated = false;
        self.invalidated = false;
    }

    /// Check if an inclusion (r1, r2, p) holds in the current context.
    pub fn check_inclusion(&mut self, r1: Region, r2: Region, p: PointIndex) -> bool {
        if self.invalidated || self.full_incl.is_none() {
            self.recompute();
        }
        self.full_incl.as_ref().unwrap().contains(&(r1, r2, p)) || r1 == r2
    }

    /// Check if an inclusion (r1, r2, p) holds via static inclusion in the current context.
    pub fn check_static_inclusion(&mut self, r1: Region, r2: Region, p: PointIndex) -> bool {
        if self.invalidated || self.static_incl.is_none() {
            self.recompute_static_incl();
        }
        self.static_incl.as_ref().unwrap().contains(&(r1, r2, p)) || r1 == r2
    }
}
