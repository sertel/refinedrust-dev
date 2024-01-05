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
use function_body::FunctionTranslator;
use type_translator::TypeTranslator;
use function_body::ProcedureScope;

use spec_parsers::verbose_function_spec_parser::get_shim_attrs;
use spec_parsers::module_attr_parser as mod_parser;
use mod_parser::ModuleAttrParser;
use spec_parsers::crate_attr_parser as crate_parser;
use crate_parser::CrateAttrParser;

use topological_sort::TopologicalSort;

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
        let next = topo.pop_all();
        if next.is_empty() {
            // dependency cycle detected
            panic!("RefinedRust does not currently support mutually recursive types");
        }
        // only track actual definitions
        defn_order.extend(next.into_iter().filter(|x| { defs.contains(&x) }));
    }

    defn_order
}

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
    type_translator: &'rcx TypeTranslator<'rcx, 'tcx>,
    functions: &'rcx [LocalDefId],
    extra_imports: HashSet<radium::CoqPath>,
    coq_path_prefix: String,
}

impl<'tcx, 'rcx> VerificationCtxt<'tcx, 'rcx> {

    /// Write specifications of a verification unit.
    fn write_specifications(&self, spec_path: &Path, code_path: &Path, stem: &str) {
        let mut spec_file = io::BufWriter::new(fs::File::create(spec_path).unwrap());
        let mut code_file = io::BufWriter::new(fs::File::create(code_path).unwrap());

        spec_file.write(format!("\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\
            From {}.{} Require Import generated_code_{} extra_proofs_{}.\n", self.coq_path_prefix, stem, stem, stem).as_bytes()).unwrap();
        self.extra_imports.iter().map(|path| spec_file.write(format!("{}", path).as_bytes()).unwrap()).count();
        spec_file.write("\n".as_bytes()).unwrap();

        code_file.write("\
            From caesium Require Import lang notation.\n\
            From refinedrust Require Import typing shims.\n\
            ".as_bytes()).unwrap();

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

        // also write only-spec functions specs
        for (_, spec) in self.procedure_registry.iter_only_spec() {
            if spec.has_spec() {
                spec_file.write(format!("{}", spec).as_bytes()).unwrap();
                spec_file.write("\n\n".as_bytes()).unwrap();
            }
            else {
                spec_file.write(format!("(* No specification provided for {} *)\n\n", spec.function_name).as_bytes()).unwrap();
            }
        }

        spec_file.write("End specs.".as_bytes()).unwrap();
    }

    /// Write proof templates for a verification unit.
    fn write_templates<F>(&self, file_path: F, stem: &str) where F : Fn(&str) -> std::path::PathBuf {
        // write templates
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(&fun.name());
            let mut template_file = io::BufWriter::new(fs::File::create(path.as_path()).unwrap());

            let mode = self.procedure_registry.lookup_function_mode(did).unwrap();

            if fun.spec.has_spec() && mode.needs_proof() {
                template_file.write(format!("\
                    From caesium Require Import lang notation.\n\
                    From refinedrust Require Import typing shims.\n\
                    From {}.{stem} Require Import generated_code_{stem} generated_specs_{stem} extra_proofs_{stem}.\n",
                    self.coq_path_prefix).as_bytes()).unwrap();
                self.extra_imports.iter().map(|path| template_file.write(format!("{}", path).as_bytes()).unwrap()).count();
                template_file.write("\n".as_bytes()).unwrap();

                template_file.write("Set Default Proof Using \"Type\".\n\n".as_bytes()).unwrap();

                template_file.write("\
                    Section proof.\n\
                    Context `{!typeGS Σ}.\n".as_bytes()).unwrap();

                fun.generate_lemma_statement(&mut template_file).unwrap();

                write!(template_file, "End proof.\n\n").unwrap();

                fun.generate_proof_prelude(&mut template_file).unwrap();

            }
            else if !fun.spec.has_spec() {
                write!(template_file, "(* No specification provided *)").unwrap();
            }
            else {
                write!(template_file, "(* Function is trusted *)").unwrap();
            }
        }
    }

    /// Write proofs for a verification unit.
    fn write_proofs<F>(&self, file_path: F, stem: &str) where F : Fn(&str) -> std::path::PathBuf {
        // write proofs
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(&fun.name());
            let mut proof_file = io::BufWriter::new(fs::File::create(path.as_path()).unwrap());

            let mode = self.procedure_registry.lookup_function_mode(did).unwrap();

            if fun.spec.has_spec() && mode.needs_proof() {
                write!(proof_file, "\
                    From caesium Require Import lang notation.\n\
                    From refinedrust Require Import typing shims.\n\
                    From {}.{stem} Require Import generated_code_{stem} generated_specs_{stem} extra_proofs_{stem}.\n\
                    From {}.{stem} Require Import generated_template_{}.\n",
                    self.coq_path_prefix, self.coq_path_prefix, fun.name()).unwrap();
                self.extra_imports.iter().map(|path| proof_file.write(format!("{}", path).as_bytes()).unwrap()).count();
                proof_file.write("\n".as_bytes()).unwrap();

                proof_file.write("Set Default Proof Using \"Type\".\n\n".as_bytes()).unwrap();


                proof_file.write("\
                    Section proof.\n\
                    Context `{!typeGS Σ}.\n".as_bytes()).unwrap();

                fun.generate_proof(&mut proof_file).unwrap();

                proof_file.write("End proof.".as_bytes()).unwrap();
            }
            else if !fun.spec.has_spec() {
                proof_file.write(format!("(* No specification provided *)").as_bytes()).unwrap();
            }
            else {
                proof_file.write(format!("(* Function is trusted *)").as_bytes()).unwrap();
            }
        }
    }

    /// Write Coq files for this verification unit.
    pub fn write_coq_files(&self) {
        // use the crate_name for naming
        let crate_name: rustc_span::symbol::Symbol = self.env.tcx().crate_name(rustc_span::def_id::LOCAL_CRATE);
        let stem = crate_name.as_str();

        // create output directory
        let base_dir_path: std::path::PathBuf = if let Some(output) = rrconfig::output_dir() {
            output
        } else {
            info!("No output directory specified, not writing files");
            return;
        };

        let mut dir_path = base_dir_path.clone();
        dir_path.push(&stem);
        let dir_path = dir_path.as_path();
        info!("outputting generated code to {}", dir_path.to_str().unwrap());
        if let Err(_) = fs::read_dir(dir_path) {
            warn!("Output directory {:?} does not exist, creating directory", base_dir_path);
            fs::create_dir_all(dir_path).unwrap();
        }

        let code_path = dir_path.join(format!("generated_code_{}.v", stem));
        let spec_path = dir_path.join(format!("generated_specs_{}.v", stem));
        let dune_path = dir_path.join("dune");
        let extra_path = dir_path.join(format!("extra_proofs_{}.v", stem));

        // write specs
        self.write_specifications(spec_path.as_path(), code_path.as_path(), &stem);
        // write templates
        self.write_templates(|name| { dir_path.join(format!("generated_template_{}.v", name)) }, &stem);
        // write proofs
        self.write_proofs(|name| { dir_path.join(format!("generated_proof_{}.v", name)) }, &stem);


        // write extra file, if it does not already exist
        if !extra_path.exists() {
            let mut extra_file = io::BufWriter::new(fs::File::create(extra_path.as_path()).unwrap());
            extra_file.write(format!("(* Your extra proofs go here *)\n").as_bytes()).unwrap();
        }

        // write dune meta file
        let mut dune_file = io::BufWriter::new(fs::File::create(dune_path.as_path()).unwrap());
        let extra_theories: Vec<_> = self.extra_imports.iter().filter_map(|path| path.path.clone()).collect();
        dune_file.write(format!("\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n\
             (name {}.{})\n\
             (theories stdpp iris Ltac2 Equations RecordUpdate lrust caesium lithium refinedrust {}))", self.coq_path_prefix, stem, extra_theories.join(" ")).as_bytes()).unwrap();
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
                let meta = function_body::ProcedureMeta::new(spec.to_string(), name.to_string(), function_body::ProcedureMode::Shim);
                vcx.procedure_registry.register_function(&did, meta);
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
        let mut mode = function_body::ProcedureMode::Prove;

        let attrs = vcx.env.get_attributes(f.to_def_id());
        let v = crate::utils::filter_tool_attrs(attrs);

        // check if this is a purely spec function; if so, skip.
        if crate::utils::has_tool_attr(attrs, "shim") {
            // TODO better error message
            let annot = get_shim_attrs(v.as_slice()).unwrap();

            info!("Registering shim: {:?} as spec: {}, code: {}", f.to_def_id(), annot.spec_name, annot.code_name);
            let meta = function_body::ProcedureMeta::new(annot.spec_name, annot.code_name, function_body::ProcedureMode::Shim);
            vcx.procedure_registry.register_function(&f.to_def_id(), meta);

            continue;
        }

        if crate::utils::has_tool_attr(attrs, "trust_me") {
            mode = function_body::ProcedureMode::TrustMe;
        }
        else if crate::utils::has_tool_attr(attrs, "only_spec") {
            mode = function_body::ProcedureMode::OnlySpec;
        }
        else if crate::utils::has_tool_attr(attrs, "ignore") {
            info!("Function {:?} will be ignored", f);
            mode = function_body::ProcedureMode::Ignore;
        }

        let fname = type_translator::strip_coq_ident(&vcx.env.get_item_name(f.to_def_id()));
        let spec_name = format!("type_of_{}", fname);

        let meta = function_body::ProcedureMeta::new(spec_name, fname, mode);

        vcx.procedure_registry.register_function(&f.to_def_id(), meta);
    }
}

/// Translate functions of the crate, assuming they were previously registered.
fn translate_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let proc = vcx.env.get_procedure(f.to_def_id());
        let fname = vcx.env.get_item_name(f.to_def_id());
        let meta = vcx.procedure_registry.lookup_function(&f.to_def_id()).unwrap();

        let attrs = vcx.env.get_attributes(f.to_def_id());

        let mode = meta.get_mode();
        if mode.is_shim() {
            continue;
        }
        if mode.is_ignore() {
            continue;
        }

        info!("Translating function {}", fname);


        let translator = FunctionTranslator::new(&vcx.env, meta, proc, attrs, &vcx.type_translator, &vcx.procedure_registry);

        if mode.is_only_spec() {
            // Only generate a spec
            match translator.and_then(|t| t.generate_spec()) {
                Ok(spec) => {
                    info!("Successfully generated spec for {}", fname);
                    vcx.procedure_registry.provide_specced_function(&f.to_def_id(), spec);
                },
                Err(function_body::TranslationError::FatalError(err)) => {
                    error!("Encountered fatal cross-function error in translation: {:?}", err);
                    error!("Aborting...");
                    return;
                },
                Err(err) => {
                    warn!("Encountered error: {:?}", err);
                    warn!("Skipping function {}", fname);
                    if !rrconfig::skip_unsupported_features() {
                        exit_with_error(&format!("Encountered error when translating function {}, stopping...", fname));
                    }
                }
            }
        }
        else {
            // Fully translate the function
            match translator.and_then(|t| t.translate()) {
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
                    if !rrconfig::skip_unsupported_features() {
                        exit_with_error(&format!("Encountered error when translating function {}, stopping...", fname));
                    }
                }
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

    let functions_with_spec: Vec<_> = functions.into_iter().filter(|id| {
        if env.has_any_tool_attribute(id.to_def_id()) {
            if env.has_tool_attribute(id.to_def_id(), "skip") {
                warn!("Function {:?} will be skipped due to a rr::skip annotation", id);
                false
            }
            else {
                true
            }
        } else {
            false
        }
    }).collect();

    for f in functions_with_spec.iter() {
        info!("Function {:?} has a spec and will be processed", f);
    }
    functions_with_spec
}

/// Get and parse all module attributes.
pub fn get_module_attributes<'tcx>(env: &Environment<'tcx>) -> Result<HashMap<LocalDefId, mod_parser::ModuleAttrs>, String> {
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


/// Translate a crate, creating a `VerificationCtxt` in the process.
pub fn generate_coq_code<'tcx, F>(tcx: TyCtxt<'tcx>, continuation: F)
    where F: Fn(VerificationCtxt<'tcx, '_>) -> ()
{
    let env = Environment::new(tcx);
    let env: &Environment = &*Box::leak(Box::new(env));

    // get crate attributes
    let crate_attrs = tcx.hir().krate_attrs();
    let crate_attrs = utils::filter_tool_attrs(crate_attrs);
    info!("Found crate attributes: {:?}", crate_attrs);
    // parse crate attributes
    let mut crate_parser = crate_parser::VerboseCrateAttrParser::new();
    let crate_spec = crate_parser.parse_crate_attrs(&crate_attrs).unwrap();

    let path_prefix = crate_spec.prefix.unwrap_or("refinedrust.examples".to_string());
    info!("Setting Coq path prefix: {:?}", path_prefix);

    // get module attributes
    let module_attrs = get_module_attributes(&env).unwrap();

    let mut imports: HashSet<radium::CoqPath> = HashSet::new();

    crate_spec.imports.into_iter().map(|path| imports.insert(path)).count();
    module_attrs.into_values().into_iter().map(|attrs| attrs.imports.into_iter().map(|path| imports.insert(path)).count()).count();
    info!("Importing extra Coq files: {:?}", imports);

    let functions = get_filtered_functions(&env);

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let type_translator = TypeTranslator::new(env, &struct_arena, &enum_arena);
    let procedure_registry = ProcedureScope::new();

    // first register names for all the procedures, to resolve mutual dependencies
    let mut vcx = VerificationCtxt {
        env,
        functions: functions.as_slice(),
        type_translator: &type_translator,
        procedure_registry,
        extra_imports: imports,
        coq_path_prefix: path_prefix,
    };

    register_functions(&mut vcx);

    register_shims(&mut vcx);

    translate_functions(&mut vcx);

    continuation(vcx);
}
