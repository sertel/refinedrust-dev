// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

// TODO: remove this
#![allow(dead_code)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_attr;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

extern crate polonius_engine;

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

use log::{info, warn};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
use typed_arena::Arena;

mod arg_folder;
mod base;
mod checked_op_analysis;
mod data;
pub mod environment;
mod force_matches_macro;
mod function_body;
mod inclusion_tracker;
mod shim_registry;
mod spec_parsers;
mod type_translator;
mod tyvars;
mod utils;

use std::fs::File;

use crate_parser::CrateAttrParser;
use environment::Environment;
use function_body::{FunctionTranslator, ProcedureMode, ProcedureScope};
use mod_parser::ModuleAttrParser;
use spec_parsers::verbose_function_spec_parser::{get_export_as_attr, get_shim_attrs};
use spec_parsers::{crate_attr_parser as crate_parser, module_attr_parser as mod_parser};
use topological_sort::TopologicalSort;
use type_translator::TypeTranslator;
use rrconfig;

/// Order ADT definitions topologically.
fn order_adt_defs<'tcx>(deps: HashMap<DefId, HashSet<DefId>>) -> Vec<DefId> {
    let mut topo = TopologicalSort::new();
    let mut defs = HashSet::new();

    for (did, referenced_dids) in deps.iter() {
        defs.insert(did);
        topo.insert(*did);
        for did2 in referenced_dids.iter() {
            topo.add_dependency(*did2, *did);
        }
    }

    let mut defn_order = Vec::new();
    while !topo.is_empty() {
        let mut next = topo.pop_all();
        // sort these by lexicographic order
        next.sort();
        if next.is_empty() {
            // dependency cycle detected
            panic!("RefinedRust does not currently support mutually recursive types");
        }
        // only track actual definitions
        defn_order.extend(next.into_iter().filter(|x| defs.contains(&x)));
    }

    defn_order
}

pub struct VerificationCtxt<'tcx, 'rcx> {
    env: &'rcx Environment<'tcx>,
    procedure_registry: ProcedureScope<'rcx>,
    type_translator: &'rcx TypeTranslator<'rcx, 'tcx>,
    functions: &'rcx [LocalDefId],
    /// the second component determines whether to include it in the code file as well
    extra_imports: HashSet<(radium::CoqPath, bool)>,
    coq_path_prefix: String,
    shim_registry: shim_registry::ShimRegistry<'rcx>,
}

impl<'tcx, 'rcx> VerificationCtxt<'tcx, 'rcx> {
    fn extract_def_path(path: rustc_hir::definitions::DefPath) -> Vec<String> {
        let mut components = Vec::new();
        for p in path.data.iter() {
            if let Some(name) = p.data.get_opt_name() {
                components.push(name.as_str().to_string());
            }
        }
        components
    }

    fn get_path_for_shim(&self, did: DefId) -> Vec<&str> {
        let attrs = self.env.get_attributes(did);
        //info!("get_path_for_shim has attrs {:?}", attrs);

        let mut path = None;
        if crate::utils::has_tool_attr(attrs, "export_as") {
            let filtered_attrs = crate::utils::filter_tool_attrs(attrs);
            path = Some(get_export_as_attr(filtered_attrs.as_slice()).unwrap());
        } else {
            // Check for an annotation on the surrounding impl
            if let Some(impl_did) = self.env.tcx().impl_of_method(did) {
                let attrs = self.env.get_attributes(impl_did);
                if crate::utils::has_tool_attr(attrs, "export_as") {
                    let filtered_attrs = crate::utils::filter_tool_attrs(attrs);
                    let mut path_prefix = get_export_as_attr(filtered_attrs.as_slice()).unwrap();

                    // push the last component of this path
                    let def_path = self.env.tcx().def_path(did);
                    let mut this_path = Self::extract_def_path(def_path);
                    path_prefix.push(this_path.pop().unwrap());
                    path = Some(path_prefix)
                }
            }
        }
        if path.is_none() {
            let def_path = self.env.tcx().def_path(did);
            path = Some(Self::extract_def_path(def_path));
        }

        let path = path.unwrap();
        let interned_path = self.shim_registry.intern_path(path);
        interned_path
    }

    fn make_shim_function_entry(&self, did: DefId, spec_name: &str) -> Option<shim_registry::FunctionShim> {
        let mut is_method = false;
        if let Some(mode) = self.procedure_registry.lookup_function_mode(&did) {
            if mode == ProcedureMode::Prove
                || mode == ProcedureMode::OnlySpec
                || mode == ProcedureMode::TrustMe
            {
                match self.env.tcx().visibility(did) {
                    // only export public items
                    ty::Visibility::Public => {
                        if self.env.tcx().impl_of_method(did).is_some() {
                            is_method = true;
                        }

                        let interned_path = self.get_path_for_shim(did);

                        let name = type_translator::strip_coq_ident(&self.env.get_item_name(did));
                        info!(
                            "Found function path {:?} for did {:?} with name {:?}",
                            interned_path, did, name
                        );

                        let a = shim_registry::FunctionShim {
                            path: interned_path,
                            is_method,
                            name,
                            spec_name: spec_name.to_string(),
                        };
                        return Some(a);
                    },
                    ty::Visibility::Restricted(_) => {
                        // don't  export
                    },
                }
            }
        }
        None
    }

    fn make_adt_shim_entry(
        &self,
        did: DefId,
        syntype: &str,
        reftype: &str,
        semtype: &str,
    ) -> Option<shim_registry::AdtShim> {
        info!("making shim entry for {:?}", did);
        if did.is_local() {
            match self.env.tcx().visibility(did) {
                // only export public items
                ty::Visibility::Public => {
                    let interned_path = self.get_path_for_shim(did);
                    let name = type_translator::strip_coq_ident(&self.env.get_item_name(did));

                    info!("Found adt path {:?} for did {:?} with name {:?}", interned_path, did, name);

                    let a = shim_registry::AdtShim {
                        path: interned_path,
                        refinement_type: reftype.to_string(),
                        syn_type: syntype.to_string(),
                        sem_type: semtype.to_string(),
                    };
                    return Some(a);
                },
                ty::Visibility::Restricted(_) => {
                    // don't  export
                },
            }
        }

        None
    }

    fn generate_module_summary(&self, module_path: &str, module: &str, name: &str, path: &Path) {
        let mut function_shims = Vec::new();
        let mut adt_shims = Vec::new();

        let variant_defs = self.type_translator.get_variant_defs();
        let enum_defs = self.type_translator.get_enum_defs();

        for (did, entry) in variant_defs.iter() {
            let entry = entry.borrow();
            if let Some(entry) = entry.as_ref() {
                if let Some(shim) = self.make_adt_shim_entry(
                    *did,
                    entry.st_def_name(),
                    &entry.public_rt_def_name(),
                    entry.public_type_name(),
                ) {
                    adt_shims.push(shim);
                }
            }
        }
        for (did, entry) in enum_defs.iter() {
            let entry = entry.borrow();
            if let Some(entry) = entry.as_ref() {
                if let Some(shim) = self.make_adt_shim_entry(
                    *did,
                    entry.st_def_name(),
                    &entry.public_rt_def_name(),
                    entry.public_type_name(),
                ) {
                    adt_shims.push(shim);
                }
            }
        }

        for (did, fun) in self.procedure_registry.iter_code() {
            if let Some(shim) = self.make_shim_function_entry(*did, &fun.spec.spec_name) {
                function_shims.push(shim);
            }
        }

        for (did, fun) in self.procedure_registry.iter_only_spec() {
            if let Some(shim) = self.make_shim_function_entry(*did, &fun.spec_name) {
                function_shims.push(shim);
            }
        }

        info!("Generated module summary ADTs: {:?}", adt_shims);
        info!("Generated module summary functions: {:?}", function_shims);

        let interface_file = File::create(path).unwrap();
        shim_registry::write_shims(interface_file, module_path, module, name, adt_shims, function_shims);
    }

    /// Write specifications of a verification unit.
    fn write_specifications(&self, spec_path: &Path, code_path: &Path, stem: &str) {
        let mut spec_file = io::BufWriter::new(fs::File::create(spec_path).unwrap());
        let mut code_file = io::BufWriter::new(fs::File::create(code_path).unwrap());

        spec_file
            .write(
                format!(
                    "\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\
            From {}.{} Require Export generated_code_{}.\n",
                    self.coq_path_prefix, stem, stem
                )
                .as_bytes(),
            )
            .unwrap();
        self.extra_imports
            .iter()
            .map(|(path, _)| spec_file.write(format!("{}", path).as_bytes()).unwrap())
            .count();
        spec_file.write("\n".as_bytes()).unwrap();

        code_file
            .write(
                "\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\
            "
                .as_bytes(),
            )
            .unwrap();
        self.extra_imports
            .iter()
            .map(|(path, include)| {
                if *include {
                    code_file.write(format!("{}", path).as_bytes()).unwrap();
                }
            })
            .count();

        // write structs and enums
        // we need to do a bit of work to order them right
        let struct_defs = self.type_translator.get_struct_defs();
        let enum_defs = self.type_translator.get_enum_defs();
        let adt_deps = self.type_translator.get_adt_deps();

        let ordered = order_adt_defs(adt_deps);
        info!("ordered ADT defns: {:?}", ordered);

        for did in ordered.iter() {
            if let Some(su_ref) = struct_defs.get(did) {
                let su_ref = su_ref.borrow();
                info!("writing struct {:?}, {:?}", did, su_ref);
                let su = su_ref.as_ref().unwrap();

                // layout specs
                code_file.write(su.generate_coq_sls_def().as_bytes()).unwrap();
                code_file.write("\n".as_bytes()).unwrap();

                // type aliases
                spec_file.write(su.generate_coq_type_def().as_bytes()).unwrap();
                spec_file.write("\n".as_bytes()).unwrap();

                // abstracted type
                if let Some(inv_spec) = su.generate_optional_invariant_def() {
                    spec_file.write(inv_spec.as_bytes()).unwrap();
                    spec_file.write("\n".as_bytes()).unwrap();
                }
            } else {
                let eu_ref = enum_defs.get(did).unwrap().borrow();
                info!("writing enum {:?}, {:?}", did, eu_ref);
                let eu = eu_ref.as_ref().unwrap();

                // layout specs
                code_file.write(eu.generate_coq_els_def().as_bytes()).unwrap();
                code_file.write("\n".as_bytes()).unwrap();

                // type definition
                spec_file.write(eu.generate_coq_type_def().as_bytes()).unwrap();
                spec_file.write("\n".as_bytes()).unwrap();
            }
        }

        // write tuples up to the necessary size
        // TODO

        // write translated source code of functions
        code_file
            .write(
                "Section code.\n\
            Context `{!typeGS Σ}.\n\
            Open Scope printing_sugar.\n\n"
                    .as_bytes(),
            )
            .unwrap();

        for (_, fun) in self.procedure_registry.iter_code() {
            code_file.write(fun.code.caesium_fmt().as_bytes()).unwrap();
            code_file.write("\n\n".as_bytes()).unwrap();
        }

        code_file.write("End code.".as_bytes()).unwrap();

        // write function specs
        spec_file
            .write(
                "\
            Section specs.\n\
            Context `{!typeGS Σ}.\n\n"
                    .as_bytes(),
            )
            .unwrap();
        for (_, fun) in self.procedure_registry.iter_code() {
            if fun.spec.has_spec() {
                if fun.spec.args.len() != fun.code.get_argument_count() {
                    warn!("Function specification for {} is missing arguments", fun.name());
                }
                spec_file.write(format!("{}", fun.spec).as_bytes()).unwrap();
                spec_file.write("\n\n".as_bytes()).unwrap();
            } else {
                warn!("No specification for {}", fun.name());
                spec_file
                    .write(format!("(* No specification provided for {} *)\n\n", fun.name()).as_bytes())
                    .unwrap();
            }
        }

        // also write only-spec functions specs
        for (_, spec) in self.procedure_registry.iter_only_spec() {
            if spec.has_spec() {
                spec_file.write(format!("{}", spec).as_bytes()).unwrap();
                spec_file.write("\n\n".as_bytes()).unwrap();
            } else {
                spec_file
                    .write(
                        format!("(* No specification provided for {} *)\n\n", spec.function_name).as_bytes(),
                    )
                    .unwrap();
            }
        }

        // Include extra specs
        if let Some(extra_specs_path) = rrconfig::extra_specs_file() {
            writeln!(spec_file, "(* Included specifications from configured file {:?} *)", extra_specs_path)
                .unwrap();
            let mut extra_specs_file = io::BufReader::new(fs::File::open(extra_specs_path).unwrap());

            let mut extra_specs_string = String::new();
            extra_specs_file.read_to_string(&mut extra_specs_string).unwrap();

            write!(spec_file, "{}", extra_specs_string).unwrap();
        }

        spec_file.write("End specs.".as_bytes()).unwrap();
    }

    /// Write proof templates for a verification unit.
    fn write_templates<F>(&self, file_path: F, stem: &str)
    where
        F: Fn(&str) -> std::path::PathBuf,
    {
        // write templates
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(&fun.name());
            let mut template_file = io::BufWriter::new(fs::File::create(path.as_path()).unwrap());

            let mode = self.procedure_registry.lookup_function_mode(did).unwrap();

            if fun.spec.has_spec() && mode.needs_proof() {
                template_file
                    .write(
                        format!(
                            "\
                    From caesium Require Import lang notation.\n\
                    From refinedrust Require Import typing shims.\n\
                    From {}.{stem} Require Import generated_code_{stem} generated_specs_{stem}.\n",
                            self.coq_path_prefix
                        )
                        .as_bytes(),
                    )
                    .unwrap();
                self.extra_imports
                    .iter()
                    .map(|(path, _)| template_file.write(format!("{}", path).as_bytes()).unwrap())
                    .count();
                template_file.write("\n".as_bytes()).unwrap();

                template_file.write("Set Default Proof Using \"Type\".\n\n".as_bytes()).unwrap();

                template_file
                    .write(
                        "\
                    Section proof.\n\
                    Context `{!typeGS Σ}.\n"
                            .as_bytes(),
                    )
                    .unwrap();

                fun.generate_lemma_statement(&mut template_file).unwrap();

                write!(template_file, "End proof.\n\n").unwrap();

                fun.generate_proof_prelude(&mut template_file).unwrap();
            } else if !fun.spec.has_spec() {
                write!(template_file, "(* No specification provided *)").unwrap();
            } else {
                write!(template_file, "(* Function is trusted *)").unwrap();
            }
        }
    }

    fn check_function_needs_proof(&self, did: DefId, fun: &radium::Function) -> bool {
        let mode = self.procedure_registry.lookup_function_mode(&did).unwrap();
        fun.spec.has_spec() && mode.needs_proof()
    }

    /// Write proofs for a verification unit.
    fn write_proofs<F>(&self, file_path: F, stem: &str)
    where
        F: Fn(&str) -> std::path::PathBuf,
    {
        // write proofs
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(&fun.name());

            if path.exists() {
                info!("Proof file for function {} already exists, skipping creation", fun.name());
                continue;
            } else if self.check_function_needs_proof(*did, fun) {
                info!("Proof file for function {} does not yet exist, creating", fun.name());

                let mut proof_file = io::BufWriter::new(fs::File::create(path.as_path()).unwrap());

                write!(
                    proof_file,
                    "\
                    From caesium Require Import lang notation.\n\
                    From refinedrust Require Import typing shims.\n\
                    From {}.{stem}.generated Require Import generated_code_{stem} generated_specs_{stem}.\n\
                    From {}.{stem}.generated Require Import generated_template_{}.\n",
                    self.coq_path_prefix,
                    self.coq_path_prefix,
                    fun.name()
                )
                .unwrap();
                // Note: we do not import the self.extra_imports explicitly, as we rely on them
                // being re-exported from the template -- we want to be stable under changes of the
                // extras
                proof_file.write("\n".as_bytes()).unwrap();

                proof_file.write("Set Default Proof Using \"Type\".\n\n".as_bytes()).unwrap();

                proof_file
                    .write(
                        "\
                    Section proof.\n\
                    Context `{!typeGS Σ}.\n"
                            .as_bytes(),
                    )
                    .unwrap();

                fun.generate_proof(&mut proof_file).unwrap();

                proof_file.write("End proof.".as_bytes()).unwrap();
            }
        }
    }

    /// Write Coq files for this verification unit.
    pub fn write_coq_files(&self) {
        // use the crate_name for naming
        let crate_name: rustc_span::symbol::Symbol =
            self.env.tcx().crate_name(rustc_span::def_id::LOCAL_CRATE);
        let stem = crate_name.as_str();

        // create output directory
        let output_dir_path: std::path::PathBuf = if let Some(output) = rrconfig::output_dir() {
            output
        } else {
            info!("No output directory specified, not writing files");
            return;
        };

        let mut base_dir_path = output_dir_path.clone();
        base_dir_path.push(&stem);

        if let Err(_) = fs::read_dir(base_dir_path.as_path()) {
            warn!("Output directory {:?} does not exist, creating directory", base_dir_path);
            fs::create_dir_all(base_dir_path.as_path()).unwrap();
        }

        let coq_module_path = format!("{}.{}", self.coq_path_prefix, stem);
        let generated_module_path = format!("{}.generated", coq_module_path);
        let proof_module_path = format!("{}.proofs", coq_module_path);

        // write gitignore file
        let gitignore_path = base_dir_path.as_path().join(format!(".gitignore"));
        if !gitignore_path.exists() {
            let mut gitignore_file = io::BufWriter::new(fs::File::create(gitignore_path.as_path()).unwrap());
            write!(
                gitignore_file,
                "\
                generated\n\
                proofs/dune"
            )
            .unwrap();
        }

        // build the path for generated files
        base_dir_path.push("generated");
        let generated_dir_path = base_dir_path.clone();
        let generated_dir_path = generated_dir_path.as_path();

        // build the path for proof files
        base_dir_path.pop();
        base_dir_path.push("proofs");
        let proof_dir_path = base_dir_path.clone();
        let proof_dir_path = proof_dir_path.as_path();

        // build the path for the interface file
        base_dir_path.pop();
        base_dir_path.push("interface.rrlib");
        self.generate_module_summary(
            &generated_module_path,
            &format!("generated_specs_{}", stem),
            stem,
            base_dir_path.as_path(),
        );

        // write generated (subdirectory "generated")
        info!("outputting generated code to {}", generated_dir_path.to_str().unwrap());
        if let Err(_) = fs::read_dir(generated_dir_path) {
            warn!("Output directory {:?} does not exist, creating directory", generated_dir_path);
            fs::create_dir_all(generated_dir_path).unwrap();
        } else {
            // purge contents
            info!("Removing the contents of the generated directory");
            fs::remove_dir_all(generated_dir_path).unwrap();
            fs::create_dir(generated_dir_path).unwrap();
        }

        let code_path = generated_dir_path.join(format!("generated_code_{}.v", stem));
        let spec_path = generated_dir_path.join(format!("generated_specs_{}.v", stem));
        let generated_dune_path = generated_dir_path.join("dune");

        // write specs
        self.write_specifications(spec_path.as_path(), code_path.as_path(), &stem);

        // write templates
        self.write_templates(|name| generated_dir_path.join(format!("generated_template_{}.v", name)), &stem);

        // write dune meta file
        let mut dune_file = io::BufWriter::new(fs::File::create(generated_dune_path.as_path()).unwrap());
        let extra_theories: Vec<_> =
            self.extra_imports.iter().filter_map(|(path, _)| path.path.clone()).collect();
        write!(
            dune_file,
            "\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n\
             (name {generated_module_path})\n\
             (theories stdpp iris Ltac2 Equations RecordUpdate lrust caesium lithium refinedrust {}))",
            extra_theories.join(" ")
        )
        .unwrap();

        // write proofs (subdirectory "proofs")
        let make_proof_file_name = |name| format!("proof_{}.v", name);

        info!("using {} as proof directory", proof_dir_path.to_str().unwrap());
        if let Ok(read) = fs::read_dir(proof_dir_path) {
            // directory already exists, we want to check if there are any stale proof files and
            // issue a warning in that case

            // build the set of proof files we are going to expect
            let mut proof_files_to_generate = HashSet::new();
            for (did, fun) in self.procedure_registry.iter_code() {
                if self.check_function_needs_proof(*did, fun) {
                    proof_files_to_generate.insert(make_proof_file_name(fun.name()));
                }
            }

            for file in read {
                if let Ok(file) = file {
                    // check if the file name is okay
                    let filename = file.file_name();
                    if let Some(filename) = filename.to_str() {
                        if filename == "dune" {
                            continue;
                        } else if proof_files_to_generate.contains(filename) {
                            continue;
                        } else {
                            println!(
                                "Warning: Proof file {filename} does not have a matching Rust function to verify."
                            );
                        }
                    }
                }
            }
        } else {
            warn!("Output directory {:?} does not exist, creating directory", proof_dir_path);
            fs::create_dir_all(proof_dir_path).unwrap();
        }

        self.write_proofs(|name| proof_dir_path.join(format!("proof_{}.v", name)), &stem);

        // explicitly spell out the proof modules we want to compile so we don't choke on stale
        // proof files
        let mut proof_modules = Vec::new();
        for (did, fun) in self.procedure_registry.iter_code() {
            if self.check_function_needs_proof(*did, fun) {
                proof_modules.push(format!("proof_{}", fun.name()));
            }
        }

        // write proof dune file
        let proof_dune_path = proof_dir_path.join("dune");
        let mut dune_file = io::BufWriter::new(fs::File::create(proof_dune_path.as_path()).unwrap());
        write!(dune_file, "\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n\
             (name {proof_module_path})\n\
             (modules {})\n\
             (theories stdpp iris Ltac2 Equations RecordUpdate lrust caesium lithium refinedrust {} {}.{}.generated))",
            proof_modules.join(" "), extra_theories.join(" "), self.coq_path_prefix, stem).unwrap();
    }
}

/// Register shims in the procedure registry.
fn register_shims<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) -> Result<(), String> {
    for shim in vcx.shim_registry.get_function_shims().iter() {
        let did;
        if shim.is_method {
            did = utils::try_resolve_method_did(vcx.env.tcx(), &shim.path);
        } else {
            did = utils::try_resolve_did(vcx.env.tcx(), &shim.path);
        };

        match did {
            Some(did) => {
                // register as usual in the procedure registry
                info!("registering shim for {:?}", shim.path);
                let meta = function_body::ProcedureMeta::new(
                    shim.spec_name.to_string(),
                    shim.name.to_string(),
                    function_body::ProcedureMode::Shim,
                );
                vcx.procedure_registry.register_function(&did, meta);
            },
            _ => {
                println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
            },
        }
    }

    for shim in vcx.shim_registry.get_adt_shims().iter() {
        if let Some(did) = utils::try_resolve_did(vcx.env.tcx(), &shim.path) {
            let lit = radium::LiteralType {
                rust_name: None,
                type_term: shim.sem_type.clone(),
                syn_type: radium::SynType::Literal(shim.syn_type.clone()),
                refinement_type: radium::CoqType::Literal(shim.refinement_type.clone()),
            };
            if let Err(e) = vcx.type_translator.register_adt_shim(did, lit) {
                println!("Warning: {}", e);
            }
            info!("Resolved ADT shim {:?} as {:?} did", shim, did);
        } else {
            println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
        }
    }

    // add the extra imports
    vcx.extra_imports
        .extend(vcx.shim_registry.get_extra_imports().iter().map(|x| (x.clone(), true)));

    Ok(())
}

fn get_most_restrictive_function_mode<'tcx, 'rcx>(
    vcx: &VerificationCtxt<'tcx, 'rcx>,
    did: DefId,
) -> function_body::ProcedureMode {
    let mut mode = function_body::ProcedureMode::Prove;

    let attrs = vcx.env.get_attributes(did);

    // check if this is a purely spec function; if so, skip.
    if crate::utils::has_tool_attr(attrs, "shim") {
        mode = function_body::ProcedureMode::Shim;
    }

    if crate::utils::has_tool_attr(attrs, "trust_me") {
        mode = function_body::ProcedureMode::TrustMe;
    } else if crate::utils::has_tool_attr(attrs, "only_spec") {
        mode = function_body::ProcedureMode::OnlySpec;
    } else if crate::utils::has_tool_attr(attrs, "ignore") {
        info!("Function {:?} will be ignored", did);
        mode = function_body::ProcedureMode::Ignore;
    }

    mode
}

/// Register functions of the crate in the procedure registry.
fn register_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let mut mode = get_most_restrictive_function_mode(vcx, f.to_def_id());

        if mode == function_body::ProcedureMode::Shim {
            // TODO better error message
            let attrs = vcx.env.get_attributes(f.to_def_id());
            let v = crate::utils::filter_tool_attrs(attrs);
            let annot = get_shim_attrs(v.as_slice()).unwrap();

            info!(
                "Registering shim: {:?} as spec: {}, code: {}",
                f.to_def_id(),
                annot.spec_name,
                annot.code_name
            );
            let meta = function_body::ProcedureMeta::new(
                annot.spec_name,
                annot.code_name,
                function_body::ProcedureMode::Shim,
            );
            vcx.procedure_registry.register_function(&f.to_def_id(), meta);

            continue;
        }

        if mode == function_body::ProcedureMode::Prove && let Some(impl_did) = vcx.env.tcx().impl_of_method(f.to_def_id()) {
            mode = get_most_restrictive_function_mode(vcx, impl_did);
        }

        if mode == function_body::ProcedureMode::Shim {
            warn!("Nonsensical shim attribute on impl; ignoring");
            mode = function_body::ProcedureMode::Prove;
        }

        let fname = type_translator::strip_coq_ident(&vcx.env.get_item_name(f.to_def_id()));
        let spec_name = format!("type_of_{}", fname);

        let meta = function_body::ProcedureMeta::new(spec_name, fname, mode);

        vcx.procedure_registry.register_function(&f.to_def_id(), meta);
    }
}

fn propagate_attr_from_impl(it: &rustc_ast::ast::AttrItem) -> bool {
    if let Some(ident) = it.path.segments.get(1) {
        match ident.ident.as_str() {
            "context" => true,
            _ => false,
        }
    } else {
        false
    }
}

/// Translate functions of the crate, assuming they were previously registered.
fn translate_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let proc = vcx.env.get_procedure(f.to_def_id());
        let fname = vcx.env.get_item_name(f.to_def_id());
        let meta = vcx.procedure_registry.lookup_function(&f.to_def_id()).unwrap();

        let attrs = vcx.env.get_attributes(f.to_def_id());
        let mut filtered_attrs = crate::utils::filter_tool_attrs(attrs);
        // also add selected attributes from the surrounding impl
        if let Some(impl_did) = vcx.env.tcx().impl_of_method(f.to_def_id()) {
            let impl_attrs = vcx.env.get_attributes(impl_did);
            let filtered_impl_attrs = crate::utils::filter_tool_attrs(impl_attrs);
            filtered_attrs.extend(filtered_impl_attrs.into_iter().filter(|x| propagate_attr_from_impl(x)));
        }

        let mode = meta.get_mode();
        if mode.is_shim() {
            continue;
        }
        if mode.is_ignore() {
            continue;
        }

        info!("Translating function {}", fname);

        let translator = FunctionTranslator::new(
            &vcx.env,
            meta,
            proc,
            &filtered_attrs,
            &vcx.type_translator,
            &vcx.procedure_registry,
        );

        if mode.is_only_spec() {
            // Only generate a spec
            match translator.and_then(|t| t.generate_spec()) {
                Ok(spec) => {
                    println!("Successfully generated spec for {}", fname);
                    vcx.procedure_registry.provide_specced_function(&f.to_def_id(), spec);
                },
                Err(function_body::TranslationError::FatalError(err)) => {
                    println!("Encountered fatal cross-function error in translation: {:?}", err);
                    println!("Aborting...");
                    return;
                },
                Err(err) => {
                    println!("Encountered error: {:?}", err);
                    println!("Skipping function {}", fname);
                    if !rrconfig::skip_unsupported_features() {
                        exit_with_error(&format!(
                            "Encountered error when translating function {}, stopping...",
                            fname
                        ));
                    }
                },
            }
        } else {
            // Fully translate the function
            match translator.and_then(|t| t.translate()) {
                Ok(fun) => {
                    println!("Successfully translated {}", fname);
                    vcx.procedure_registry.provide_translated_function(&f.to_def_id(), fun);
                },
                Err(function_body::TranslationError::FatalError(err)) => {
                    println!("Encountered fatal cross-function error in translation: {:?}", err);
                    println!("Aborting...");
                    return;
                },
                Err(err) => {
                    println!("Encountered error: {:?}", err);
                    println!("Skipping function {}", fname);
                    if !rrconfig::skip_unsupported_features() {
                        exit_with_error(&format!(
                            "Encountered error when translating function {}, stopping...",
                            fname
                        ));
                    }
                },
            }
        }
    }
}

fn exit_with_error(s: &str) {
    eprintln!("{s}");
    std::process::exit(-1);
}

/// Get all functions and closures in the current crate that have attributes on them and are not
/// skipped due to rr::skip attributes.
pub fn get_filtered_functions<'tcx>(env: &Environment<'tcx>) -> Vec<LocalDefId> {
    let mut functions = env.get_procedures();
    let closures = env.get_closures();
    info!("Found {} function(s) and {} closure(s)", functions.len(), closures.len());
    functions.extend(closures);

    let functions_with_spec: Vec<_> = functions
        .into_iter()
        .filter(|id| {
            let mut prove = false;
            if env.has_any_tool_attribute(id.to_def_id()) {
                prove = true;
                if env.has_tool_attribute(id.to_def_id(), "skip") {
                    warn!("Function {:?} will be skipped due to a rr::skip annotation", id);
                    prove = false;
                } else {
                    if let Some(impl_did) = env.tcx().impl_of_method(id.to_def_id()) {
                        if env.has_tool_attribute(impl_did, "skip") {
                            warn!("Function {:?} will be skipped due to a rr::skip annotation on impl", id);
                            prove = false;
                        }
                    }
                }
            }
            prove
        })
        .collect();

    for f in functions_with_spec.iter() {
        info!("Function {:?} has a spec and will be processed", f);
    }
    functions_with_spec
}

/// Get and parse all module attributes.
pub fn get_module_attributes<'tcx>(
    env: &Environment<'tcx>,
) -> Result<HashMap<LocalDefId, mod_parser::ModuleAttrs>, String> {
    let modules = env.get_modules();
    let mut attrs = HashMap::new();
    info!("collected modules: {:?}", modules);

    for m in modules.iter() {
        let module_attrs = utils::filter_tool_attrs(env.get_attributes(m.to_def_id()));
        let mut module_parser = mod_parser::VerboseModuleAttrParser::new();
        let module_spec = module_parser.parse_module_attrs(*m, &module_attrs)?;
        attrs.insert(*m, module_spec);
    }

    Ok(attrs)
}

/// Find RefinedRust modules in the given loadpath.
fn scan_loadpath(path: &Path, storage: &mut HashMap<String, std::path::PathBuf>) -> io::Result<()> {
    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                scan_loadpath(path.as_path(), storage)?;
            } else if path.is_file() {
                if let Some(ext) = path.extension() {
                    if Some("rrlib") == ext.to_str() {
                        // try to open this rrlib file
                        let f = File::open(path.clone())?;
                        if let Some(name) = shim_registry::is_valid_refinedrust_module(f) {
                            storage.insert(name, path);
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

/// Find RefinedRust modules in the given loadpaths.
fn scan_loadpaths(paths: &[std::path::PathBuf]) -> io::Result<HashMap<String, std::path::PathBuf>> {
    let mut found_lib_files: HashMap<String, std::path::PathBuf> = HashMap::new();

    for path in paths.iter() {
        scan_loadpath(path, &mut found_lib_files)?;
    }

    Ok(found_lib_files)
}

/// Translate a crate, creating a `VerificationCtxt` in the process.
pub fn generate_coq_code<'tcx, F>(tcx: TyCtxt<'tcx>, continuation: F) -> Result<(), String>
where
    F: Fn(VerificationCtxt<'tcx, '_>) -> (),
{
    let env = Environment::new(tcx);
    let env: &Environment = &*Box::leak(Box::new(env));

    // get crate attributes
    let crate_attrs = tcx.hir().krate_attrs();
    let crate_attrs = utils::filter_tool_attrs(crate_attrs);
    info!("Found crate attributes: {:?}", crate_attrs);
    // parse crate attributes
    let mut crate_parser = crate_parser::VerboseCrateAttrParser::new();
    let crate_spec = crate_parser.parse_crate_attrs(&crate_attrs)?;

    let path_prefix = crate_spec.prefix.unwrap_or("refinedrust.examples".to_string());
    info!("Setting Coq path prefix: {:?}", path_prefix);

    // get module attributes
    let module_attrs = get_module_attributes(&env)?;

    // process imports
    let mut imports: HashSet<radium::CoqPath> = HashSet::new();
    crate_spec.imports.into_iter().map(|path| imports.insert(path)).count();
    module_attrs
        .values()
        .map(|attrs| attrs.imports.iter().map(|path| imports.insert(path.clone())).count())
        .count();
    info!("Importing extra Coq files: {:?}", imports);

    // process includes
    let mut includes: HashSet<String> = HashSet::new();
    crate_spec.includes.into_iter().map(|name| includes.insert(name)).count();
    module_attrs
        .into_values()
        .into_iter()
        .map(|attrs| attrs.includes.into_iter().map(|name| includes.insert(name)).count())
        .count();
    info!("Including RefinedRust modules: {:?}", includes);

    let functions = get_filtered_functions(&env);

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let shim_arena = Arena::new();
    let type_translator = TypeTranslator::new(env, &struct_arena, &enum_arena, &shim_arena);
    let procedure_registry = ProcedureScope::new();
    let shim_string_arena = Arena::new();
    let mut shim_registry = shim_registry::ShimRegistry::empty(&shim_string_arena);

    // add includes to the shim registry
    let library_load_paths = rrconfig::lib_load_paths();
    let found_libs = scan_loadpaths(&library_load_paths).map_err(|e| e.to_string())?;
    info!("Found the following RefinedRust libraries in the loadpath: {:?}", found_libs);
    for incl in includes.iter() {
        if let Some(p) = found_libs.get(incl) {
            let f = File::open(p).map_err(|e| e.to_string())?;
            shim_registry.add_source(f)?;
        } else {
            println!("Warning: did not find library {} in loadpath", incl);
        }
    }

    // register shims from the shim config
    match rrconfig::shim_file() {
        None => (),
        Some(file) => {
            let f = File::open(file).map_err(|a| a.to_string())?;
            shim_registry.add_source(f)?;
        },
    }

    // first register names for all the procedures, to resolve mutual dependencies
    let mut vcx = VerificationCtxt {
        env,
        functions: functions.as_slice(),
        type_translator: &type_translator,
        procedure_registry,
        extra_imports: imports.into_iter().map(|x| (x, false)).collect(),
        coq_path_prefix: path_prefix,
        shim_registry,
    };

    register_functions(&mut vcx);

    register_shims(&mut vcx)?;

    translate_functions(&mut vcx);

    continuation(vcx);

    Ok(())
}
