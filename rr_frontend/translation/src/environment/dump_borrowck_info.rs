// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;

use log::{debug, trace};
use rustc_hash::FxHashMap;
use rustc_index::Idx;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use {rrconfig as config, rustc_hir as hir};

use super::borrowck::facts;
use super::mir_analyses::initialization::{
    compute_definitely_initialized, DefinitelyInitializedAnalysisResult,
};
use super::polonius_info::PoloniusInfo;
use super::procedure::Procedure;
use super::{loops, Environment};
use crate::data::ProcedureDefId;
use crate::environment::mir_utils::RealEdges;

/*
pub fn dump_borrowck_info(env: &Environment<'_>, procedures: &[ProcedureDefId]) {
    trace!("[dump_borrowck_info] enter");

    let printer = InfoPrinter { env, tcx: env.tcx() };
    //intravisit::walk_crate(&mut printer, tcx.hir.krate());
    //tcx.hir.krate().visit_all_item_likes(&mut printer);

    for def_id in procedures {
        printer.print_info(*def_id);
    }

    trace!("[dump_borrowck_info] exit");
}
*/

pub fn dump_borrowck_info<'a, 'tcx>(
    env: &'a Environment<'tcx>,
    procedure: &ProcedureDefId,
    info: &'a PoloniusInfo<'a, 'tcx>,
) {
    trace!("[dump_borrowck_info] enter");

    let printer = InfoPrinter {
        env,
        tcx: env.tcx(),
    };
    //intravisit::walk_crate(&mut printer, tcx.hir.krate());
    //tcx.hir.krate().visit_all_item_likes(&mut printer);

    printer.print_info(*procedure, info);

    trace!("[dump_borrowck_info] exit");
}

struct InfoPrinter<'a, 'tcx: 'a> {
    env: &'a Environment<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> InfoPrinter<'a, 'tcx> {
    fn dump_borrowck_facts(
        &self,
        info: &'a PoloniusInfo<'a, 'tcx>,
        writer: &mut BufWriter<File>,
    ) -> std::io::Result<()> {
        let input_facts = &info.borrowck_in_facts;
        let interner = &info.interner;
        write!(writer, "======== Borrowck facts ========\n\n")?;

        write!(writer, "Loans issued at: \n")?;
        for issued in &input_facts.loan_issued_at {
            let loc = interner.get_point(issued.2);
            write!(writer, "({:?}, {:?}, {:?})\n", issued.0, issued.1, loc)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Use of var derefs origin: \n")?;
        write!(writer, "{:?}", input_facts.use_of_var_derefs_origin)?;
        //for fact in &input_facts.use_of_var_derefs_origin {
        //write!(writer, "({:?}, {:?}) ",  fact.0, fact.1);
        //}
        write!(writer, "\n\n")?;

        write!(writer, "Loans killed at: \n")?;
        for fact in &input_facts.loan_killed_at {
            let loc = interner.get_point(fact.1);
            write!(writer, "({:?}, {:?})\n", fact.0, loc)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Loans invalidated at: \n")?;
        for fact in &input_facts.loan_invalidated_at {
            let loc = interner.get_point(fact.0);
            write!(writer, "({:?}, {:?})\n", loc, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Known placeholders:\n")?;
        for fact in &input_facts.placeholder {
            write!(writer, "({:?}, {:?})\n", fact.0, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "known placeholder subset: \n")?;
        for fact in &input_facts.known_placeholder_subset {
            write!(writer, "({:?}, {:?})\n", fact.0, fact.1)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Subset (base, take transitive closure): \n")?;
        for fact in &input_facts.subset_base {
            write!(writer, "({:?} ⊑ {:?}, {:?})\n", fact.0, fact.1, interner.get_point(fact.2))?;
        }
        write!(writer, "\n\n")?;

        //let output_facts = &self.body.output_facts;
        //let output_facts = Output::compute(&body.input_facts, Algorithm::DatafrogOpt, true);
        let output_facts = &info.borrowck_out_facts;

        // TODO: why doesn't this contain anything???
        write!(writer, "Subset anywhere: \n")?;
        for fact in &output_facts.subset_anywhere {
            write!(writer, "({:?}, {:?})\n", fact.0, fact.1)?;
        }
        write!(writer, "\n\n")?;

        // TODO: find out how to do the subset computation properly to make our analysis work...
        write!(writer, "Superset:\n")?;
        let mut v: Vec<_> = info.superset.iter().map(|(i, m)| (*i, m)).collect();
        v.sort_by(|(l1, _), (l2, _)| l1.cmp(l2));
        for (l, m) in v {
            write!(writer, "({:?}, {:?})\n", interner.get_point(l).location, m)?;
        }
        write!(writer, "\n\n")?;

        write!(writer, "Origin contains loan at: \n")?;
        let mut sorted_origin_contains: Vec<_> = output_facts.origin_contains_loan_at.iter().collect();
        sorted_origin_contains.sort_by(|(&l1, _), (&l2, _)| l1.cmp(&l2));

        for (&loc, region_map) in sorted_origin_contains.iter() {
            write!(writer, "\t {:?} -> {:?}\n", interner.get_point(loc), *region_map)?;
        }
        write!(writer, "\n\n")?;

        // TODO: these things seem really useless, why is that?
        //println!("Origin live on entry: ");
        //for (loc, origin) in output_facts.origin_live_on_entry.iter() {
        //println!("\t {:?} -> {:?}", table.to_location(*loc), origin);
        //}

        write!(writer, "Dump enabled: {:?}\n", output_facts.dump_enabled)?;
        //output_facts.origins_live_at()
        //println!("Origins live at: {:?}", );

        Ok(())
    }

    fn print_info(&self, def_id: ProcedureDefId, info: &'a PoloniusInfo<'a, 'tcx>) {
        trace!("[print_info] enter {:?}", def_id);

        /*match env::var_os("PRUSTI_DUMP_PROC").and_then(|value| value.into_string().ok()) {
            Some(value) => {
                if name != value {
                    return;
                }
            },
            _ => {},
        };*/

        let procedure = Procedure::new(self.env, def_id);

        let local_def_id = def_id.expect_local();
        //let _ = self.tcx.mir_borrowck(local_def_id);

        // Read Polonius facts.
        let def_path = self.tcx.hir().def_path(local_def_id);

        let mir = procedure.get_mir();

        // write raw dump
        let raw_path = PathBuf::from(config::log_dir())
            .join("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("polonius_info.txt");
        debug!("Writing raw polonius info to {:?}", raw_path);
        let prefix = raw_path.parent().expect("Unable to determine parent dir");
        std::fs::create_dir_all(prefix).expect("Unable to create parent dir");
        let raw_file = File::create(raw_path).expect("Unable to create file");
        let mut raw = BufWriter::new(raw_file);
        self.dump_borrowck_facts(info, &mut raw).unwrap();

        // write graphs
        let real_edges = RealEdges::new(mir);
        let loop_info = loops::ProcedureLoops::new(mir, &real_edges);

        let graph_path = PathBuf::from(config::log_dir())
            .join("nll-facts")
            .join(def_path.to_filename_friendly_no_crate())
            .join("graph.dot");
        debug!("Writing graph to {:?}", graph_path);
        let prefix = graph_path.parent().expect("Unable to determine parent dir");
        std::fs::create_dir_all(prefix).expect("Unable to create parent dir");
        let graph_file = File::create(graph_path).expect("Unable to create file");
        let graph = BufWriter::new(graph_file);

        let initialization = compute_definitely_initialized(def_id, &mir, self.tcx);

        // FIXME: this computes the wrong loop invariant permission
        //let loop_invariant_block = HashMap::new();

        // print polonius.dot
        super::polonius_info::graphviz(self.env, &def_path, def_id, info).unwrap();

        // print graph.dot
        let mir_info_printer = MirInfoPrinter {
            def_path,
            tcx: self.tcx,
            mir,
            graph: cell::RefCell::new(graph),
            loops: loop_info,
            initialization,
            polonius_info: info,
        };
        mir_info_printer.print_info().unwrap();

        trace!("[print_info] exit");
    }
}

struct MirInfoPrinter<'a, 'tcx: 'a> {
    #[allow(dead_code)]
    pub def_path: hir::definitions::DefPath,
    pub tcx: TyCtxt<'tcx>,
    pub mir: &'a mir::Body<'tcx>,
    pub graph: cell::RefCell<BufWriter<File>>,
    pub loops: loops::ProcedureLoops,
    pub initialization: DefinitelyInitializedAnalysisResult<'tcx>,
    //pub liveness: LivenessAnalysisResult,
    pub polonius_info: &'a PoloniusInfo<'a, 'tcx>,
}

macro_rules! write_graph {
    ( $self:ident, $( $x:expr ),* ) => {
        writeln!($self.graph.borrow_mut(), $( $x ),*)?;
    }
}

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

macro_rules! write_edge {
    ( $self:ident, $source:ident, str $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{}\"\n", $source, stringify!($target));
    }};
    ( $self:ident, $source:ident, unwind $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\" [color=red]\n", $source, $target);
    }};
    ( $self:ident, $source:ident, imaginary $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\" [style=\"dashed\"]\n", $source, $target);
    }};
    ( $self:ident, $source:ident, $target:ident ) => {{
        write_graph!($self, "\"{:?}\" -> \"{:?}\"\n", $source, $target);
    }};
}

macro_rules! to_sorted_string {
    ( $o:expr ) => {{
        let mut vector = $o.iter().map(|x| to_html!(x)).collect::<Vec<String>>();
        vector.sort();
        vector.join(", ")
    }};
}

impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {
    pub fn print_info(mut self) -> Result<(), io::Error> {
        //self.dump_to_file("/tmp/requires",
        //&self.polonius_info.borrowck_out_facts.origin_contains_loan_at);
        //self.dump_to_file("/tmp/zrequires",
        //&self.polonius_info.additional_facts.zombie_requires);

        write_graph!(self, "digraph G {{\n");
        for bb in self.mir.basic_blocks.indices() {
            self.visit_basic_block(bb)?;
        }
        self.print_temp_variables()?;
        self.print_blocked(mir::RETURN_PLACE, mir::Location {
            block: mir::BasicBlock::new(0),
            statement_index: 0,
        })?;
        self.print_subset_at_start(mir::Location {
            block: mir::BasicBlock::new(0),
            statement_index: 0,
        })?;
        self.print_borrow_regions()?;
        self.print_restricts()?;
        write_graph!(self, "}}\n");

        // flush
        self.graph.into_inner().into_inner().unwrap();

        Ok(())
    }

    fn print_temp_variables(&self) -> Result<(), io::Error> {
        if self.show_temp_variables() {
            write_graph!(self, "Variables [ style=filled shape = \"record\"");
            write_graph!(self, "label =<<table>");
            write_graph!(self, "<tr><td>VARIABLES</td></tr>");
            write_graph!(self, "<tr><td>Name</td><td>Temporary</td><td>Type</td><td>Region</td></tr>");
            let mut var_names = HashMap::new();
            for info in &self.mir.var_debug_info {
                if let mir::VarDebugInfoContents::Place(place) = info.value {
                    if let Some(local) = place.as_local() {
                        var_names.insert(local, info.name);
                    } else {
                        unimplemented!();
                    }
                } else {
                    unimplemented!();
                }
            }
            for (temp, var) in self.mir.local_decls.iter_enumerated() {
                let name = var_names.get(&temp).map(|s| s.to_string()).unwrap_or_else(|| String::from(""));
                let region = self
                    .polonius_info
                    .place_regions
                    .for_local(temp)
                    .map(|region| format!("{:?}", region))
                    .unwrap_or_else(|| String::from(""));
                let typ = to_html!(var.ty);
                write_graph!(
                    self,
                    "<tr><td>{}</td><td>{:?}</td><td>{}</td><td>{}</td></tr>",
                    name,
                    temp,
                    typ,
                    region
                );
            }
            write_graph!(self, "</table>>];");
        }
        Ok(())
    }

    /// Print the origin_contains_loan_at relation as a tree of loans.
    fn print_restricts(&self) -> Result<(), io::Error> {
        if !self.show_restricts() {
            return Ok(());
        }
        write_graph!(self, "subgraph cluster_restricts {{");
        let mut interesting_restricts = Vec::new();
        let mut loans = Vec::new();
        for &(region, loan, point) in self.polonius_info.borrowck_in_facts.loan_issued_at.iter() {
            write_graph!(self, "\"region_live_at_{:?}_{:?}_{:?}\" [ ", region, loan, point);
            write_graph!(self, "label=\"region_live_at({:?}, {:?}, {:?})\" ];", region, loan, point);
            write_graph!(
                self,
                "{:?} -> \"region_live_at_{:?}_{:?}_{:?}\" -> {:?}_{:?}",
                loan,
                region,
                loan,
                point,
                region,
                point
            );
            interesting_restricts.push((region, point));
            loans.push(loan);
        }
        loans.sort();
        loans.dedup();
        for &loan in loans.iter() {
            let position = self.polonius_info.additional_facts.reborrows.iter().position(|&(_, l)| loan == l);
            if position.is_some() {
                write_graph!(self, "_{:?} [shape=box color=green]", loan);
            } else {
                write_graph!(self, "_{:?} [shape=box]", loan);
            }
        }
        for (region, point) in interesting_restricts.iter() {
            if let Some(restricts_map) =
                self.polonius_info.borrowck_out_facts.origin_contains_loan_at.get(point)
            {
                if let Some(loans) = restricts_map.get(region) {
                    for loan in loans.iter() {
                        write_graph!(self, "\"restricts_{:?}_{:?}_{:?}\" [ ", point, region, loan);
                        write_graph!(
                            self,
                            "label=\"origin_contains_loan_at({:?}, {:?}, {:?})\" ];",
                            point,
                            region,
                            loan
                        );
                        write_graph!(
                            self,
                            "{:?}_{:?} -> \"restricts_{:?}_{:?}_{:?}\" -> {:?}",
                            region,
                            point,
                            point,
                            region,
                            loan,
                            loan
                        );
                    }
                }
            }
        }
        for &(loan1, loan2) in self.polonius_info.additional_facts.reborrows.iter() {
            write_graph!(self, "_{:?} -> _{:?} [color=green]", loan1, loan2);
            // TODO: Compute strongly connected components.
        }
        write_graph!(self, "}}");
        Ok(())
    }

    /// Print the subset relation at the beginning of the given location.
    fn print_subsets(&self, location: mir::Location) -> Result<(), io::Error> {
        let bb = location.block;
        let stmt = location.statement_index;
        let start_point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.polonius_info.borrowck_out_facts.subset;
        write_graph!(self, "subgraph cluster_{:?}_{:?} {{", bb, stmt);
        write_graph!(self, "cluster_title_{:?}_{:?} [label=\"subset at {:?}\"]", bb, stmt, location);
        let mut used_regions = HashSet::new();
        if let Some(subset) = subset_map.get(&start_point).as_ref() {
            for (source_region, regions) in subset.iter() {
                used_regions.insert(source_region);
                for target_region in regions.iter() {
                    write_graph!(
                        self,
                        "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                        bb,
                        stmt,
                        source_region,
                        bb,
                        stmt,
                        target_region
                    );
                    used_regions.insert(target_region);
                }
            }
        }
        for region in used_regions {
            write_graph!(
                self,
                "{:?}_{:?}_{:?} [shape=box label=\"{:?} (region)\"]",
                bb,
                stmt,
                region,
                region
            );
        }
        // FIXME
        // for (region, point) in self.polonius_info.borrowck_in_facts.region_live_at.iter() {
        //     if *point == start_point {
        //         write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, stmt, region);
        //     }
        // }
        write_graph!(self, "}}");
        Ok(())
    }

    fn print_borrow_regions(&self) -> Result<(), io::Error> {
        if !self.show_borrow_regions() {
            return Ok(());
        }
        write_graph!(self, "subgraph cluster_Loans {{");
        for (region, loan, point) in self.polonius_info.borrowck_in_facts.loan_issued_at.iter() {
            write_graph!(self, "subgraph cluster_{:?} {{", loan);
            let subset_map = &self.polonius_info.borrowck_out_facts.subset;
            if let Some(subset) = subset_map.get(point).as_ref() {
                for (source_region, regions) in subset.iter() {
                    if let Some(local) = self.polonius_info.find_variable(*source_region) {
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}", loan, local, loan, source_region);
                    }
                    for target_region in regions.iter() {
                        write_graph!(
                            self,
                            "{:?}_{:?} -> {:?}_{:?}",
                            loan,
                            source_region,
                            loan,
                            target_region
                        );
                        if let Some(local) = self.polonius_info.find_variable(*target_region) {
                            write_graph!(self, "{:?}_{:?} -> {:?}_{:?}", loan, local, loan, target_region);
                        }
                    }
                }
            }
            write_graph!(self, "{:?} -> {:?}_{:?}", loan, loan, region);
            write_graph!(self, "}}");
        }
        write_graph!(self, "}}");
        Ok(())
    }

    fn visit_basic_block(&mut self, bb: mir::BasicBlock) -> Result<(), io::Error> {
        write_graph!(self, "\"{:?}\" [ shape = \"record\"", bb);
        if self.loops.loop_heads.contains(&bb) {
            write_graph!(self, "color=green");
        }
        write_graph!(self, "label =<<table>");
        write_graph!(self, "<th>");
        write_graph!(self, "<td>{:?}</td>", bb);
        write_graph!(self, "<td colspan=\"7\"></td>");
        write_graph!(self, "<td>Definitely Initialized</td>");
        write_graph!(self, "</th>");

        write_graph!(self, "<th>");
        if self.show_statement_indices() {
            write_graph!(self, "<td>Nr</td>");
        }
        write_graph!(self, "<td>statement</td>");
        write_graph!(self, "<td colspan=\"2\">Loans</td>");
        write_graph!(self, "<td colspan=\"2\">Borrow Regions</td>");
        write_graph!(self, "<td colspan=\"2\">Regions</td>");
        write_graph!(self, "<td>{}</td>", self.get_definitely_initialized_before_block(bb));
        write_graph!(self, "</th>");

        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = self.mir[bb];
        let mut location = mir::Location {
            block: bb,
            statement_index: 0,
        };
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index])?;
            location.statement_index += 1;
        }
        let terminator = terminator.clone();
        let term_str = if let Some(ref term) = &terminator { to_html!(term.kind) } else { String::from("") };
        write_graph!(self, "<tr>");
        if self.show_statement_indices() {
            write_graph!(self, "<td></td>");
        }
        write_graph!(self, "<td>{}</td>", term_str);
        write_graph!(self, "<td></td>");
        self.write_mid_point_blas(location)?;
        write_graph!(self, "<td colspan=\"4\"></td>");
        write_graph!(self, "<td>{}</td>", self.get_definitely_initialized_after_statement(location));
        write_graph!(self, "</tr>");
        write_graph!(self, "</table>> ];");

        if let Some(ref terminator) = &terminator {
            self.visit_terminator(bb, terminator)?;
        }

        if self.loops.loop_heads.contains(&bb) {
            let start_location = mir::Location {
                block: bb,
                statement_index: 0,
            };
            let start_point = self.get_point(start_location, facts::PointType::Start);
            let restricts_map = &self.polonius_info.borrowck_out_facts.origin_contains_loan_at;
            if let Some(restricts_relation) = restricts_map.get(&start_point).as_ref() {
                for (region, all_loans) in restricts_relation.iter() {
                    // Filter out reborrows.
                    let loans: Vec<_> = all_loans
                        .iter()
                        .filter(|l2| {
                            !all_loans
                                .iter()
                                .map(move |&l1| (**l2, l1))
                                .any(|r| self.polonius_info.additional_facts.reborrows.contains(&r))
                        })
                        .cloned()
                        .collect();

                    // This assertion would fail if instead of reborrow we happen to have a move
                    // like `let mut current = head;`. See issue #18.
                    // TODO: display if we reborrowing an argument.
                    // assert!(all_loans.is_empty() || !loans.is_empty());
                    write_graph!(self, "{:?}_{:?} [shape=box color=green]", bb, region);
                    write_graph!(self, "{:?}_0_{:?} -> {:?}_{:?} [dir=none]", bb, region, bb, region);
                    for loan in loans.iter() {
                        // The set of regions used in edges. We need to
                        // create nodes for these regions.
                        let mut used_regions = HashSet::new();

                        // Write out all loans that are kept alive by ``region``.
                        write_graph!(self, "{:?}_{:?} -> {:?}_{:?}", bb, region, bb, loan);

                        write_graph!(self, "subgraph cluster_{:?}_{:?} {{", bb, loan);
                        let loan_issued_at = &self.polonius_info.borrowck_in_facts.loan_issued_at;
                        for (region, l, point) in loan_issued_at.iter() {
                            if loan == l {
                                // Write the original loan's region.
                                write_graph!(self, "{:?}_{:?} -> {:?}_{:?}_{:?}", bb, loan, bb, loan, region);
                                used_regions.insert(region);

                                // Write out the subset relation at ``point``.
                                let subset_map = &self.polonius_info.borrowck_out_facts.subset;
                                if let Some(subset) = subset_map.get(point).as_ref() {
                                    for (source_region, regions) in subset.iter() {
                                        used_regions.insert(source_region);
                                        for target_region in regions.iter() {
                                            if source_region == target_region {
                                                continue;
                                            }
                                            used_regions.insert(target_region);
                                            write_graph!(
                                                self,
                                                "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                                bb,
                                                loan,
                                                source_region,
                                                bb,
                                                loan,
                                                target_region
                                            );
                                        }
                                    }
                                }
                            }
                        }

                        for region in used_regions {
                            write_graph!(
                                self,
                                "{:?}_{:?}_{:?} [shape=box label=\"{:?}\n(region)\"]",
                                bb,
                                loan,
                                region,
                                region
                            );
                            if let Some(local) = self.polonius_info.find_variable(*region) {
                                write_graph!(
                                    self,
                                    "{:?}_{:?}_{:?} [label=\"{:?}\n(var)\"]",
                                    bb,
                                    loan,
                                    local,
                                    local
                                );
                                write_graph!(
                                    self,
                                    "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                    bb,
                                    loan,
                                    local,
                                    bb,
                                    loan,
                                    region
                                );
                            }
                        }
                        write_graph!(self, "}}");
                    }
                }
            }

            // FIXME
            // for (region, point) in self.polonius_info.borrowck_in_facts.region_live_at.iter() {
            //     if *point == start_point {
            //         // TODO: the unwrap_or is a temporary workaround
            //         // See issue prusti-internal/issues/14
            //         let variable = self
            //             .polonius_info
            //             .find_variable(*region)
            //             .unwrap_or(mir::Local::new(1000));
            //         self.print_blocked(variable, start_location)?;
            //     }
            // }

            self.print_subsets(start_location)?;
        }

        Ok(())
    }

    fn visit_statement(&self, location: mir::Location, statement: &mir::Statement) -> Result<(), io::Error> {
        write_graph!(self, "<tr>");
        if self.show_statement_indices() {
            write_graph!(self, "<td>{}</td>", location.statement_index);
        }
        write_graph!(self, "<td>{}</td>", to_html!(statement));

        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        // Loans.
        if let Some(blas) = self.polonius_info.borrowck_out_facts.loan_live_at.get(&start_point).as_ref() {
            write_graph!(self, "<td>{}</td>", to_sorted_string!(blas));
        } else {
            write_graph!(self, "<td></td>");
        }
        self.write_mid_point_blas(location)?;

        // Borrow regions (loan start points).
        let borrow_regions: Vec<_> = self
            .polonius_info
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter(|(_, _, point)| *point == start_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));
        let borrow_regions: Vec<_> = self
            .polonius_info
            .borrowck_in_facts
            .loan_issued_at
            .iter()
            .filter(|(_, _, point)| *point == mid_point)
            .cloned()
            .map(|(region, loan, _)| (region, loan))
            .collect();
        write_graph!(self, "<td>{}</td>", to_sorted_string!(borrow_regions));

        // FIXME
        // // Regions alive at this program point.
        // let regions: Vec<_> = self
        //     .polonius_info
        //     .borrowck_in_facts
        //     .region_live_at
        //     .iter()
        //     .filter(|(_, point)| *point == start_point)
        //     .cloned()
        //     // TODO: Understand why we cannot unwrap here:
        //     .map(|(region, _)| (region, self.polonius_info.find_variable(region)))
        //     .collect();
        // write_graph!(self, "<td>{}</td>", to_sorted_string!(regions));
        // let regions: Vec<_> = self
        //     .polonius_info
        //     .borrowck_in_facts
        //     .region_live_at
        //     .iter()
        //     .filter(|(_, point)| *point == mid_point)
        //     .cloned()
        //     // TODO: Understand why we cannot unwrap here:
        //     .map(|(region, _)| (region, self.polonius_info.find_variable(region)))
        //     .collect();
        // write_graph!(self, "<td>{}</td>", to_sorted_string!(regions));

        write_graph!(self, "<td>{}</td>", self.get_definitely_initialized_after_statement(location));

        write_graph!(self, "</tr>");
        Ok(())
    }

    fn get_point(&self, location: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let point = facts::Point {
            location,
            typ: point_type,
        };
        self.polonius_info.interner.get_point_index(&point)
    }

    fn visit_terminator(&self, bb: mir::BasicBlock, terminator: &mir::Terminator) -> Result<(), io::Error> {
        use rustc_middle::mir::TerminatorKind;
        match terminator.kind {
            TerminatorKind::Goto { target } => {
                write_edge!(self, bb, target);
            },
            TerminatorKind::SwitchInt { ref targets, .. } => {
                for target in targets.all_targets() {
                    write_edge!(self, bb, target);
                }
            },
            TerminatorKind::Return => {
                write_edge!(self, bb, str return);
            },
            TerminatorKind::Unreachable => {},
            TerminatorKind::UnwindResume => {
                write_edge!(self, bb, str resume);
            },
            TerminatorKind::UnwindTerminate(_) => {
                write_edge!(self, bb, str terminate);
            },
            TerminatorKind::Drop {
                ref target, ..
            } => {
                write_edge!(self, bb, target);
                //if let Some(target) = unwind {
                //write_edge!(self, bb, unwind target);
                //}
            },
            TerminatorKind::Call {
                ref target, ..
            } => {
                if let Some(target) = *target {
                    write_edge!(self, bb, target);
                }
                //if let Some(target) = unwind {
                //write_edge!(self, bb, unwind target);
                //}
            },
            TerminatorKind::Assert { target, .. } => {
                write_edge!(self, bb, target);
                //if let Some(target) = unwind {
                //write_edge!(self, bb, unwind target);
                //}
            },
            TerminatorKind::Yield { .. } => unimplemented!(),
            TerminatorKind::GeneratorDrop => unimplemented!(),
            TerminatorKind::FalseEdge {
                ref real_target,
                ref imaginary_target,
            } => {
                write_edge!(self, bb, real_target);
                write_edge!(self, bb, imaginary_target);
            },
            TerminatorKind::FalseUnwind {
                real_target,
                .. 
            } => {
                write_edge!(self, bb, real_target);
                //if let Some(target) = unwind {
                //write_edge!(self, bb, imaginary target);
                //}
            },
            TerminatorKind::InlineAsm { .. } => unimplemented!(),
        };
        Ok(())
    }

    fn show_statement_indices(&self) -> bool {
        true
        //unimplemented!("Should use SETTINGS.");
        // get_config_option("PRUSTI_DUMP_SHOW_STATEMENT_INDICES", true)
    }

    fn show_temp_variables(&self) -> bool {
        true
        //unimplemented!("Should use SETTINGS.");
        // get_config_option("PRUSTI_DUMP_SHOW_TEMP_VARIABLES", true)
    }

    fn show_borrow_regions(&self) -> bool {
        //true
        false
        //unimplemented!("Should use SETTINGS.");
        // get_config_option("PRUSTI_DUMP_SHOW_BORROW_REGIONS", false)
    }

    fn show_restricts(&self) -> bool {
        //true
        false
        //unimplemented!("Should use SETTINGS.");
        // get_config_option("PRUSTI_DUMP_SHOW_RESTRICTS", false)
    }
}

/// Definitely initialized analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {
    fn get_definitely_initialized_before_block(&self, bb: mir::BasicBlock) -> String {
        let place_set = self.initialization.get_before_block(bb);
        to_sorted_string!(place_set)
    }

    fn get_definitely_initialized_after_statement(&self, location: mir::Location) -> String {
        let place_set = self.initialization.get_after_statement(location);
        to_sorted_string!(place_set)
    }
}

/// Maybe blocking analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {
    /// Print the subset relation at a given program point.
    fn print_subset_at_start(&self, location: mir::Location) -> Result<(), io::Error> {
        let point = self.get_point(location, facts::PointType::Start);
        let subset_map = &self.polonius_info.borrowck_out_facts.subset;
        if let Some(_subset) = subset_map.get(&point).as_ref() {
            return Ok(());
            /*
                write_graph!(self, "subgraph cluster_{:?} {{", point);
                let mut used_regions = HashSet::new();
                for (from_region, to_regions) in subset.iter() {
                    used_regions.insert(*from_region);
                    for to_region in to_regions.iter() {
                        used_regions.insert(*to_region);
                        write_graph!(
                            self,
                            "{:?}_{:?} -> {:?}_{:?}",
                            point,
                            from_region,
                            point,
                            to_region
                        );
                    }
                }
                for region in used_regions {
                    if let Some(local) = self.polonius_info.find_variable(region) {
                        write_graph!(
                            self,
                            "{:?}_{:?} [shape=box label=\"{:?}:{:?}\"]",
                            point,
                            region,
                            local,
                            region
                        );
                    } else {
                        write_graph!(
                            self,
                            "{:?}_{:?} [shape=box label=\"{:?}\"]",
                            point,
                            region,
                            region
                        );
                    }
                }
                write_graph!(self, "}}");
            */
        }
        Ok(())
    }

    /// Print variables that are maybe blocked by the given variable at
    /// the start of the given location.
    fn print_blocked(&self, blocker: mir::Local, location: mir::Location) -> Result<(), io::Error> {
        let bb = location.block;
        let start_point = self.get_point(location, facts::PointType::Start);
        if let Some(region) = self.polonius_info.place_regions.for_local(blocker) {
            write_graph!(self, "{:?} -> {:?}_{:?}_{:?}", bb, bb, blocker, region);
            write_graph!(
                self,
                "{:?}_{:?}_{:?} [label=\"{:?}:{:?}\n(blocking variable)\"]",
                bb,
                blocker,
                region,
                blocker,
                region
            );
            write_graph!(self, "subgraph cluster_{:?} {{", bb);
            let subset_map = &self.polonius_info.borrowck_out_facts.subset;
            if let Some(subset) = subset_map.get(&start_point).as_ref() {
                if let Some(blocked_regions) = subset.get(&region) {
                    for blocked_region in blocked_regions.iter() {
                        if *blocked_region == region {
                            continue;
                        }
                        if let Some(blocked) = self.polonius_info.find_variable(*blocked_region) {
                            write_graph!(
                                self,
                                "{:?}_{:?}_{:?} -> {:?}_{:?}_{:?}",
                                bb,
                                blocker,
                                region,
                                bb,
                                blocked,
                                blocked_region
                            );
                        }
                    }
                }
            }
            write_graph!(self, "}}");
        }
        Ok(())
    }
}

/// Debug printing.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {
    fn _dump_to_file(
        &self,
        file: &str,
        requires: &FxHashMap<facts::PointIndex, BTreeMap<facts::Region, BTreeSet<facts::Loan>>>,
    ) {
        use csv::WriterBuilder;

        let mut file = String::from(file);
        file.push_str(&self.def_path.to_filename_friendly_no_crate());
        file.push_str(".csv");

        let mut writer = WriterBuilder::new().from_path(file).unwrap();
        for (point_index, map) in requires.iter() {
            for (region, loans) in map.iter() {
                for loan in loans.iter() {
                    let point = self.polonius_info.interner.get_point(*point_index);
                    writer
                        .write_record(&[
                            format!("{:?}", point_index),
                            format!("{:?}", point),
                            format!("{:?}", region),
                            format!("{:?}", loan),
                        ])
                        .unwrap();
                }
            }
        }
        writer.flush().unwrap();
    }
}

/// Loan end analysis.
impl<'a, 'tcx> MirInfoPrinter<'a, 'tcx> {
    /// Print the HTML cell with loans at given location.
    fn write_mid_point_blas(&self, location: mir::Location) -> Result<(), io::Error> {
        let mid_point = self.get_point(location, facts::PointType::Mid);
        let borrow_live_at_map = &self.polonius_info.borrowck_out_facts.loan_live_at;
        let mut blas = if let Some(blas) = borrow_live_at_map.get(&mid_point).as_ref() {
            (*blas).clone()
        } else {
            Vec::new()
        };
        let zombie_borrow_live_at_map = &self.polonius_info.additional_facts.zombie_borrow_live_at;
        let mut zombie_blas = if let Some(zombie_blas) = zombie_borrow_live_at_map.get(&mid_point).as_ref() {
            (*zombie_blas).clone()
        } else {
            Vec::new()
        };

        // Get the loans that die in this statement.
        let dying_loans = self.polonius_info.get_dying_loans(location);
        let dying_zombie_loans = self.polonius_info.get_dying_zombie_loans(location);
        let becoming_zombie_loans = self
            .polonius_info
            .additional_facts
            .borrow_become_zombie_at
            .get(&mid_point)
            .cloned()
            .unwrap_or_default();

        // Format the loans and mark the dying ones.
        blas.sort();
        let mut blas: Vec<_> = blas
            .into_iter()
            .map(|loan| {
                if becoming_zombie_loans.contains(&loan) {
                    format!("<b><font color=\"orchid\">{:?}</font></b>", loan)
                } else if dying_loans.contains(&loan) {
                    format!("<b><font color=\"red\">{:?}</font></b>", loan)
                } else {
                    format!("{:?}", loan)
                }
            })
            .collect();
        zombie_blas.sort();
        blas.extend(zombie_blas.iter().map(|loan| {
            if dying_zombie_loans.contains(loan) {
                format!("<b><font color=\"brown\">{:?}</font></b>", loan)
            } else {
                format!("<b><font color=\"forestgreen\">{:?}</font></b>", loan)
            }
        }));

        write_graph!(self, "<td>{}", blas.join(", "));
        let mut all_dying_loans: Vec<_> =
            dying_loans.iter().filter(|loan| !becoming_zombie_loans.contains(loan)).cloned().collect();
        debug!(
            "all_dying_loans={:?} dying_zombie_loans={:?} location={:?}",
            all_dying_loans, dying_zombie_loans, location
        );
        all_dying_loans.extend(dying_zombie_loans.iter().cloned());
        write_graph!(self, "</td>");

        Ok(())
    }
}
