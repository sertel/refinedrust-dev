// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

// TODO: remove this
#![allow(dead_code)]


#![feature(box_patterns)]
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_session;
extern crate rustc_attr;
extern crate rustc_target;
extern crate rustc_type_ir;

extern crate polonius_engine;

use log::{info, warn, error};

use rustc_hir::{def_id::DefId, def_id::LocalDefId};
use rustc_middle::ty as ty;
use rustc_middle::ty::TyCtxt;

use std::fs;
use std::io::{self, Write};
use std::path::Path;

use typed_arena::Arena;

use std::collections::{HashSet, HashMap};

use std::env;

mod spec_parsers;
mod utils;
pub mod environment;
mod force_matches_macro;
mod data;
mod function_body;
mod shim_registry;
mod checked_op_analysis;
mod tyvars;
mod base;
mod type_translator;
mod inclusion_tracker;
mod arg_folder;

use environment::Environment;
use function_body::BodyTranslator;
use type_translator::TypeTranslator;
use function_body::ProcedureScope;

use spec_parsers::verbose_function_spec_parser::get_shim_attrs;


/// Order struct defs in the order in which we should emit them for respecting dependencies.
/// Complexity O(n^2), it's currently rather inefficient, but due to small numbers it should be fine.
// TODO: we should also take into account enums here (e.g. if a struct refers to an enum)
fn order_struct_defs<'tcx>(env: &Environment<'tcx>, defs: &[DefId]) -> Vec<DefId> {
    let mut out = Vec::new();
    let mut altered = true;
    let need_to_visit: HashSet<DefId> = defs.iter().cloned().collect();


    // compute dependencies
    let mut dependencies: HashMap<DefId, HashSet<DefId>> = HashMap::new();
    for did in defs.iter() {
        let mut deps = HashSet::new();
        let ty: ty::Ty<'tcx> = env.tcx().type_of(*did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::Adt(adt, _) => {
                let variants = &adt.variants();
                for v in variants.iter() {
                    if v.def_id != *did {
                        // skip if this is not the variant we were actually looking for
                        continue;
                    }
                    for f in v.fields.iter() {
                        let field_ty = env.tcx().type_of(f.did).instantiate_identity();
                        // check if the field_ty is also an ADT -- if so, add it to the dependencies
                        match field_ty.kind() {
                            ty::TyKind::Adt(adt2, _) => {
                                // TODO depending on how we handle enums, this may need to change
                                if need_to_visit.contains(&adt2.did()) {
                                    deps.insert(adt2.did());
                                }
                                // also check the variants
                                for v2 in adt2.variants().iter() {
                                    if need_to_visit.contains(&v2.def_id) {
                                        deps.insert(v2.def_id);
                                    }
                                }
                            },
                            // fine
                            _ => (),
                        }
                    }

                }
            }
            _ => {
                //let adt = env.tcx().adt_def(did);
                panic!("unexpected ty for {:?} : {:?}", did, ty.kind());
            },
        }
        dependencies.insert(*did, deps);
    }

    let mut visited: HashSet<DefId> = HashSet::new();
    while altered {
        altered = false;

        for did in defs.iter() {
            if visited.contains(did) {
                continue;
            }
            // check that all dependencies are already there
            let deps = dependencies.get(did).unwrap();
            let need_dep = deps.iter().any(|did2| !visited.contains(did2));
            if !need_dep {
                out.push(*did);
                visited.insert(*did);
                altered = true;
            }
        }
    }

    out
}

pub struct VerificationCtxt<'tcx, 'rcx> {
    env: &'rcx Environment<'tcx>,
    procedure_registry: ProcedureScope<'rcx>,
    spec_fn_ids: HashSet<DefId>,
    type_translator: &'rcx TypeTranslator<'rcx, 'tcx>,
    functions: &'rcx [LocalDefId],
}

impl<'tcx, 'rcx> VerificationCtxt<'tcx, 'rcx> {

    /// Write specifications of a verification unit.
    fn write_specifications(&self, spec_path: &Path, code_path: &Path, stem: &str) {
        let mut spec_file = io::BufWriter::new(fs::File::create(spec_path).unwrap());
        let mut code_file = io::BufWriter::new(fs::File::create(code_path).unwrap());

        spec_file.write(format!("\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\
            From refinedrust.examples.{} Require Import generated_code_{} extra_proofs_{}.\n\n", stem, stem, stem).as_bytes()).unwrap();

        code_file.write("\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\n\
            ".as_bytes()).unwrap();

        // write structs and enums
        // we need to do a bit of work to order them right
        let struct_defs = self.type_translator.get_struct_defs();
        let enum_defs = self.type_translator.get_enum_defs();

        let mut dids: Vec<_> = struct_defs.iter().map(|(did, _)| *did).collect();
        for did in enum_defs.iter().map(|(did, _)| *did) {
            dids.push(did);
        }
        let ordered = order_struct_defs(&self.env, &dids);

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
            }
            else {
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
        code_file.write("Section code.\n\
            Context `{!typeGS Σ}.\n\
            Open Scope printing_sugar.\n\n".as_bytes()).unwrap();

        for (_, fun) in self.procedure_registry.iter_code() {
            code_file.write(fun.code.caesium_fmt().as_bytes()).unwrap();
            code_file.write("\n\n".as_bytes()).unwrap();
        }

        code_file.write("End code.".as_bytes()).unwrap();

        // write function specs
        spec_file.write("\
            Section specs.\n\
            Context `{!typeGS Σ}.\n\n".as_bytes()).unwrap();
        for (_, fun) in self.procedure_registry.iter_code() {
            if fun.spec.has_spec() {
                if fun.spec.args.len() != fun.code.get_argument_count() {
                    warn!("Function specification for {} is missing arguments",  fun.name());
                }
                spec_file.write(format!("{}", fun.spec).as_bytes()).unwrap();
                spec_file.write("\n\n".as_bytes()).unwrap();
            }
            else {
                warn!("No specification for {}", fun.name());
                spec_file.write(format!("(* No specification provided for {} *)\n\n", fun.name()).as_bytes()).unwrap();
            }
        }

        spec_file.write("End specs.".as_bytes()).unwrap();
    }

    /// Write proofs for a verification unit.
    fn write_proofs<F>(&self, file_path: F, stem: &str) where F : Fn(&str) -> std::path::PathBuf {
        // write proofs
        // each function gets a separate file in order to parallelize
        for (_, fun) in self.procedure_registry.iter_code() {
            let path = file_path(&fun.name());
            let mut proof_file = io::BufWriter::new(fs::File::create(path.as_path()).unwrap());

            if fun.spec.has_spec() {
                proof_file.write(format!("\
                    From caesium Require Import lang notation.\n\
                    From refinedrust Require Import typing shims.\n\
                    From refinedrust.examples.{} Require Import generated_code_{} generated_specs_{} extra_proofs_{}.\n\
                    Set Default Proof Using \"Type\".\n\n",
                    stem, stem, stem, stem).as_bytes()).unwrap();

                proof_file.write("\
                    Section proof.\n\
                    Context `{!typeGS Σ}.\n".as_bytes()).unwrap();

                proof_file.write(fun.generate_proof().as_bytes()).unwrap();

                proof_file.write("End proof.".as_bytes()).unwrap();
            }
            else {
                proof_file.write(format!("(* No specification provided *)").as_bytes()).unwrap();
            }
        }
    }

    /// Write Coq files for this verification unit.
    pub fn write_coq_files(&self) {
        // get file stem for naming
        let stem;
        let filepath = &self.env.tcx().sess.local_crate_source_file();
        if let Some(path) = filepath {
            if let Some (file_stem) = path.file_stem() {
                info!("file stem: {:?}", file_stem);
                stem = file_stem.to_str().unwrap().to_string();
            }
            else {
                stem = "mod".to_string();
            }
        }
        else {
            stem = "mod".to_string();
        }

        // create output directory
        let dir_str: String = if let Some(output) = rrconfig::output_dir() {
            output
        } else {
            info!("No output directory specified, not writing files");
            return;
        };

        let mut dir_path = std::path::PathBuf::from(&dir_str);
        dir_path.push(&stem);
        let dir_path = dir_path.as_path();
        info!("outputting generated code to {}", dir_path.to_str().unwrap());
        if let Err(_) = fs::read_dir(dir_path) {
            warn!("Output directory {} does not exist, creating directory", dir_str);
            fs::create_dir_all(dir_path).unwrap();
        }

        let code_path = dir_path.join(format!("generated_code_{}.v", stem));
        let spec_path = dir_path.join(format!("generated_specs_{}.v", stem));
        let dune_path = dir_path.join("dune");
        let extra_path = dir_path.join(format!("extra_proofs_{}.v", stem));

        // write specs
        self.write_specifications(spec_path.as_path(), code_path.as_path(), &stem);
        // write proofs
        self.write_proofs(|name| { dir_path.join(format!("generated_proof_{}.v", name)) }, &stem);


        // write extra file, if it does not already exist
        if !extra_path.exists() {
            let mut extra_file = io::BufWriter::new(fs::File::create(extra_path.as_path()).unwrap());
            extra_file.write(format!("(* Your extra proofs go here *)\n").as_bytes()).unwrap();
        }

        // write dune meta file
        let mut dune_file = io::BufWriter::new(fs::File::create(dune_path.as_path()).unwrap());
        dune_file.write(format!("\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n\
             (name refinedrust.examples.{})\n\
             (theories stdpp iris Ltac2 Equations RecordUpdate lrust caesium lithium refinedrust))", stem).as_bytes()).unwrap();
    }
}

/// Register shims in the procedure registry.
fn register_shims<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    // register shims
    let arena = Arena::new();
    let shim_registry = shim_registry::ShimRegistry::new(&arena).unwrap();
    for (path, kind, name, spec) in shim_registry.get_shims().iter() {
        let did;
        match kind {
            shim_registry::ShimKind::Function => {
                did = utils::try_resolve_did(vcx.env.tcx(), &path)
            },
            shim_registry::ShimKind::Method => {
                did = utils::try_resolve_method_did(vcx.env.tcx(), &path)
            },
        };

        match did {
            Some(did) => {
                // register as usual in the procedure registry
                info!("registering shim for {:?}", path);
                vcx.procedure_registry.register_function(&did, spec, name);
            },
            _ => {
                panic!("cannot find defid for shim {:?}", path);
            }
        }
    }
}

/// Register functions of the crate in the procedure registry.
fn register_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let attrs = vcx.env.get_attributes(f.to_def_id());
        let v = crate::utils::filter_tool_attrs(attrs);
        // check if this is a purely spec function; if so, skip.
        if crate::utils::has_tool_attr(attrs, "only_spec") {
            vcx.spec_fn_ids.insert(f.to_def_id());
            continue;
        }
        if crate::utils::has_tool_attr(attrs, "shim") {
            // TODO better error message
            let annot = get_shim_attrs(v.as_slice()).unwrap();
            info!("Registering shim: {:?} as spec: {}, code: {}", f.to_def_id(), annot.spec_name, annot.code_name);
            vcx.procedure_registry.register_function(&f.to_def_id(), &annot.spec_name, &annot.code_name);
            continue;
        }

        let fname = type_translator::strip_coq_ident(&vcx.env.get_item_name(f.to_def_id()));

        let spec_name = format!("type_of_{}", fname);
        vcx.procedure_registry.register_function(&f.to_def_id(), &spec_name, &fname);
    }
}

/// Translate functions of the crate, assuming they were previously registered.
fn translate_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let attrs = vcx.env.get_attributes(f.to_def_id());
        if crate::utils::has_tool_attr(attrs, "shim") {
            continue;
        }
        if crate::utils::has_tool_attr(attrs, "only_spec") {
            continue;
        }

        let proc = vcx.env.get_procedure(f.to_def_id());

        let fname = vcx.env.get_item_name(f.to_def_id());
        info!("Translating function {}", fname);

        let translate = || {
            let translator = BodyTranslator::new(&vcx.env, &fname, proc, attrs, &vcx.type_translator, &vcx.procedure_registry, &vcx.spec_fn_ids)?;
            translator.translate()
        };
        match translate() {
            Ok(fun) => {
                info!("Successfully translated {}", fname);
                vcx.procedure_registry.provide_translated_function(&f.to_def_id(), fun);
            },
            Err(function_body::TranslationError::FatalError(err)) => {
                error!("Encountered fatal cross-function error in translation: {:?}", err);
                error!("Aborting...");
                return;
            },
            Err(err) => {
                warn!("Encountered error: {:?}", err);
                warn!("Skipping function {}", fname);
            }
        }
    }
}


/// Translate a crate, creating a `VerificationCtxt` in the process.
pub fn generate_coq_code<'tcx, F>(tcx: TyCtxt<'tcx>, continuation: F)
    where F: Fn(VerificationCtxt<'tcx, '_>) -> ()
{
    let env = Environment::new(tcx);
    let env: &Environment = &*Box::leak(Box::new(env));

    let functions = env.get_annotated_procedures();
    info!("Found {} function(s)", functions.len());

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let type_translator = TypeTranslator::new(env, &struct_arena, &enum_arena);
    let procedure_registry = ProcedureScope::new();

    // first register names for all the procedures, to resolve mutual dependencies
    let spec_fn_ids = HashSet::new();

    let mut vcx = VerificationCtxt { env, functions: functions.as_slice(), type_translator: &type_translator, procedure_registry, spec_fn_ids };

    register_functions(&mut vcx);
    info!("found the following only_spec procedures, which will be ignored: {:?}", vcx.spec_fn_ids);

    register_shims(&mut vcx);

    translate_functions(&mut vcx);

    continuation(vcx);
}
