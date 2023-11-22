// This file uses code from the Prusti project (function `mir_borrowck`) under the MPL 2.0 license, https://github.com/viperproject/prusti-dev/blob/master/prusti/src/callbacks.rs.
//
// This file uses code adapted from the miri project (function `run_compiler`) under the MIT license, https://github.com/rust-lang/miri/blob/master/src/bin/miri.rs
//
// Other parts of the source are © 2023, The RefinedRust Developers and Contributors
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

#[macro_use]
extern crate lazy_static;

use log::{debug, info, warn};
use rustc_hir::{def_id::DefId, def_id::LocalDefId};
use rustc_middle::query::{queries::mir_borrowck, Providers, ExternProviders};
use std::env;

use rustc_driver::Compilation;
use rustc_interface::Config;
use rustc_middle::ty as ty;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use std::fs;
use std::io;
use std::io::Write;

use typed_arena::Arena;

use std::collections::{HashSet, HashMap};

use std::process::Command;


mod utils;
mod environment;
mod force_matches_macro;
mod data;
mod rrconfig;
mod function_body;
mod parse;
mod verbose_function_spec_parser;
mod struct_spec_parser;
mod enum_spec_parser;
mod caesium;
mod parse_utils;
mod shim_registry;
mod checked_op_analysis;
mod tyvars;
mod base;
mod type_translator;
mod inclusion_tracker;
mod arg_folder;

use environment::mir_storage;
use environment::Environment;
use function_body::BodyTranslator;
use type_translator::TypeTranslator;
use function_body::ProcedureScope;

use verbose_function_spec_parser::get_shim_attrs;

/// Args for the compiler.
pub const REFINEDRUST_DEFAULT_ARGS: &[&str] = &[
    // have debug assertions in the generated code
    "-Cdebug-assertions=on",
    // TODO: make this a config option
    "-Coverflow-checks=on",
    // use Polonius
    "-Zpolonius",
];

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

/// Main entry point to the frontend that is called by the driver.
/// This translates a crate.
pub fn analyze<'tcx>(tcx : TyCtxt<'tcx>) {
    let env = Environment::new(tcx);
    let env: &Environment = &*Box::leak(Box::new(env));

    // TODO Also think about putting different modules into different Coq files.

    let functions = env.get_annotated_procedures();
    info!("Found {} function(s)", functions.len());

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let type_translator = TypeTranslator::new(env, &struct_arena, &enum_arena);
    let mut procedure_registry = ProcedureScope::new();

    // first register names for all the procedures, to resolve mutual dependencies
    let mut spec_fn_defids = HashSet::new();
    for &f in &functions {
        let attrs = env.get_attributes(f.to_def_id());
        let v = crate::utils::filter_tool_attrs(attrs);
        // check if this is a purely spec function; if so, skip.
        if crate::utils::has_tool_attr(attrs, "only_spec") {
            spec_fn_defids.insert(f.to_def_id());
            continue;
        }
        if crate::utils::has_tool_attr(attrs, "shim") {
            // TODO better error message
            let annot = get_shim_attrs(v.as_slice()).unwrap();
            info!("Registering shim: {:?} as spec: {}, code: {}", f.to_def_id(), annot.spec_name, annot.code_name);
            procedure_registry.register_function(&f.to_def_id(), &annot.spec_name, &annot.code_name);
            continue;
        }

        let fname = type_translator::strip_coq_ident(&env.get_item_name(f.to_def_id()));

        let spec_name = format!("type_of_{}", fname);
        procedure_registry.register_function(&f.to_def_id(), &spec_name, &fname);
    }
    info!("found the following only_spec procedures, which will be ignored: {:?}", spec_fn_defids);

    // register shims
    let arena = Arena::new();
    let shim_registry = shim_registry::ShimRegistry::new(&arena).unwrap();
    for (path, kind, name, spec) in shim_registry.get_shims().iter() {
        let did;
        match kind {
            shim_registry::ShimKind::Function => {
                did = utils::try_resolve_did(tcx, &path)
            },
            shim_registry::ShimKind::Method => {
                did = utils::try_resolve_method_did(tcx, &path)
            },
        };

        match did {
            Some(did) => {
                // register as usual in the procedure registry
                info!("registering shim for {:?}", path);
                procedure_registry.register_function(&did, spec, name);
            },
            _ => {
                panic!("cannot find defid for shim {:?}", path);
            }
        }
    }


    for &f in &functions {
        let attrs = env.get_attributes(f.to_def_id());
        if crate::utils::has_tool_attr(attrs, "shim") {
            continue;
        }
        if crate::utils::has_tool_attr(attrs, "only_spec") {
            continue;
        }

        let proc = env.get_procedure(f.to_def_id());

        let fname = env.get_item_name(f.to_def_id());
        println!("\n========================================================\nTranslating function {}", fname);

        let translate = || {
            let translator = BodyTranslator::new(&env, fname, proc, attrs, &type_translator, &procedure_registry, &spec_fn_defids)?;
            translator.translate()
        };
        match translate() {
            Ok(fun) => {
                println!("Successfully translated");
                //print!("{}", fun.code.caesium_fmt());
                //println!("\n");
                //print!("{}", fun.spec);
                //println!("\n");
                procedure_registry.provide_translated_function(&f.to_def_id(), fun);
            },
            Err(function_body::TranslationError::FatalError(err)) => {
                println!("Encountered fatal cross-function error in translation: {:?}", err);
                println!("Aborting...");
                return;
            },
            Err(err) => {
                println!("Encountered error: {:?}", err);
                warn!("Skipping function....");
            }
        }
    }

    // get file stem for naming
    //let a = tcx.gcx;
    let stem;
    let filepath = &tcx.sess.local_crate_source_file();
    if let Some(path) = filepath {
        if let Some (file_stem) = path.file_stem() {
            info!("file stem: {:?}", file_stem);
            stem = file_stem.to_str().unwrap().to_string();
            //let path = std::path::Path::new(filename);
            //match path.file_stem
        }
        else {
            stem = "mod".to_string();
        }
    }
    else {
        stem = "mod".to_string();
    }

    // write output
    let dir_str = rrconfig::output_dir();
    let mut dir_path = std::path::PathBuf::from(&dir_str);
    dir_path.push(&stem);
    let dir_path = dir_path.as_path();
    if let Err(_) = fs::read_dir(dir_path) {
        warn!("Output directory {} does not exist, creating directory", dir_str);
        fs::create_dir_all(dir_path).unwrap();
    }

    let code_path = dir_path.join(format!("generated_code_{}.v", stem));
    let spec_path = dir_path.join(format!("generated_specs_{}.v", stem));
    let dune_path = dir_path.join("dune");
    let extra_path = dir_path.join(format!("extra_proofs_{}.v", stem));

    // files headers
    let mut code_file = io::BufWriter::new(fs::File::create(code_path.as_path()).unwrap());
    code_file.write("\
        From caesium Require Import lang notation.\n\
        From refinedrust Require Import typing shims.\n\n\
        ".as_bytes()).unwrap();

    // write file headers
    let mut spec_file = io::BufWriter::new(fs::File::create(spec_path.as_path()).unwrap());

    spec_file.write(format!("\
        From caesium Require Import lang notation.\n\
        From refinedrust Require Import typing shims.\n\
        From refinedrust.examples.{} Require Import generated_code_{} extra_proofs_{}.\n\n", stem, stem, stem).as_bytes()).unwrap();


    // write tuples up to the necessary size
    // TODO

    // write structs and enums
    // we need to do a bit of work to order them right
    let struct_defs = type_translator.get_struct_defs();
    let enum_defs = type_translator.get_enum_defs();

    let mut dids: Vec<_> = struct_defs.iter().map(|(did, _)| *did).collect();
    for did in enum_defs.iter().map(|(did, _)| *did) {
        dids.push(did);
    }
    let ordered = order_struct_defs(env, &dids);

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

    // write translated source code of functions
    code_file.write("Section code.\n\
        Context `{!typeGS Σ}.\n\
        Open Scope printing_sugar.\n\n".as_bytes()).unwrap();

    for (_, fun) in procedure_registry.iter_code() {
        code_file.write(fun.code.caesium_fmt().as_bytes()).unwrap();
        code_file.write("\n\n".as_bytes()).unwrap();
    }

    code_file.write("End code.".as_bytes()).unwrap();

    // write function specs
    spec_file.write("\
        Section specs.\n\
        Context `{!typeGS Σ}.\n\n".as_bytes()).unwrap();
    for (_, fun) in procedure_registry.iter_code() {
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

    // write proofs
    // each function gets a separate file in order to parallelize
    for (_, fun) in procedure_registry.iter_code() {
        let path = dir_path.join(format!("generated_proof_{}.v", fun.name()));
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
                Context `{typeGS Σ}.\n".as_bytes()).unwrap();

            proof_file.write(fun.generate_proof().as_bytes()).unwrap();

            proof_file.write("End proof.".as_bytes()).unwrap();
        }
        else {
            proof_file.write(format!("(* No specification provided *)").as_bytes()).unwrap();
        }
    }

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


    // maybe run proof checker

    // TODO: Refactor the analyze function into smaller parts.
    // The flush should not be done explicitly.
    code_file.flush().unwrap();
    spec_file.flush().unwrap();
    dune_file.flush().unwrap();

    if let Some(true) = rrconfig::check_proofs() {
        if cfg!(target_os = "windows") {
            println!("Cannot run proof checker on Windows.");
        }
        else {
            println!("calling type checker in {:?}", dir_path);

            let status = Command::new("dune")
                .arg("build")
                .current_dir(&dir_path)
                .status()
                .expect("failed to execute process");

            println!("Type checker finished with {status}");
        }
    }
}

/// Callbacks for the RefinedRust frontend.
struct RRCompilerCalls {
}

// From Prusti.
fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck::ProvidedValue<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        def_id,
        rustc_borrowck::consumers::ConsumerOptions::PoloniusOutputFacts
    );
    // SAFETY: This is safe because we are feeding in the same `tcx` that is
    // going to be used as a witness when pulling out the data.
    unsafe {
        mir_storage::store_mir_body(tcx, def_id, body_with_facts);
    }
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut Providers, _: &mut ExternProviders) {
    // overriding these queries makes sure that the `mir_storage` gets all the relevant bodies,
    // also for external crates?
    local.mir_borrowck = mir_borrowck;
    //external.mir_borrowck = mir_borrowck;
}

impl rustc_driver::Callbacks for RRCompilerCalls {
    fn config(&mut self, config : &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        _handler: &rustc_session::EarlyErrorHandler,
        _ : &rustc_interface::interface::Compiler,
        queries : &'tcx rustc_interface::Queries<'tcx>
    ) -> Compilation {
            // Analyze the crate and inspect the types under the cursor.
            queries.global_ctxt().unwrap().enter(|tcx| {
                analyze(tcx);
            }
        );
        Compilation::Stop
    }
}



/// Execute a compiler with the given CLI arguments and callbacks.
/// (adapted from Miri)
fn run_compiler(
    mut args: Vec<String>,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
    insert_default_args: bool,
) -> ! {
    if insert_default_args {
        // Some options have different defaults in Miri than in plain rustc; apply those by making
        // them the first arguments after the binary name (but later arguments can overwrite them).
        args.splice(1..1, REFINEDRUST_DEFAULT_ARGS.iter().map(ToString::to_string));
    }

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks).run()
    });
    std::process::exit(exit_code)
}

fn main() {
    rustc_driver::install_ice_hook("", |_| ());

    env_logger::init();

    println!("\
______      __ _                _______          _    \n\
| ___ \\    / _(_)              | | ___ \\        | |   \n\
| |_/ /___| |_ _ _ __   ___  __| | |_/ /   _ ___| |_  \n\
|    // _ \\  _| | '_ \\ / _ \\/ _` |    / | | / __| __| \n\
| |\\ \\  __/ | | | | | |  __/ (_| | |\\ \\ |_| \\__ \\ |_  \n\
\\_| \\_\\___|_| |_|_| |_|\\___|\\__,_\\_| \\_\\__,_|___/\\__| \n\
");
    //TODO possibly hook into the rrconfig for cmd args

    let mut rustc_args = vec![];

    for arg in env::args() {
        if rustc_args.is_empty() {
            // Very first arg: binary name.
            rustc_args.push(arg);
        } else {
            match arg.as_str() {
                _ => {
                    // Forward to rustc.
                    rustc_args.push(arg);
                }
            }
        }
    }

    debug!("rustc arguments: {:?}", rustc_args);


    run_compiler(
        rustc_args,
        &mut RRCompilerCalls { },
        true,
    );

}
