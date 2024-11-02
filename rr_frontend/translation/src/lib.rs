// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

#![feature(fn_traits)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(rustc_private)]
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
mod trait_registry;
mod traits;
mod type_translator;
mod tyvars;
mod utils;

use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{fs, io, process};

use log::{info, trace, warn};
use radium::coq;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{ast, hir, span};
use topological_sort::TopologicalSort;
use typed_arena::Arena;

use crate::environment::Environment;
use crate::function_body::{ConstScope, FunctionTranslator, ProcedureMode, ProcedureScope};
use crate::spec_parsers::const_attr_parser::{ConstAttrParser, VerboseConstAttrParser};
use crate::spec_parsers::crate_attr_parser::{CrateAttrParser, VerboseCrateAttrParser};
use crate::spec_parsers::module_attr_parser::{ModuleAttrParser, ModuleAttrs, VerboseModuleAttrParser};
use crate::spec_parsers::*;
use crate::trait_registry::TraitRegistry;
use crate::type_translator::{normalize_in_function, ParamScope, TypeTranslator};

/// Order ADT definitions topologically.
fn order_adt_defs(deps: &HashMap<DefId, HashSet<DefId>>) -> Vec<DefId> {
    let mut topo = TopologicalSort::new();
    let mut defs = HashSet::new();

    for (did, referenced_dids) in deps {
        defs.insert(did);
        topo.insert(*did);
        for did2 in referenced_dids {
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
    const_registry: ConstScope<'rcx>,
    type_translator: &'rcx TypeTranslator<'rcx, 'tcx>,
    trait_registry: &'rcx TraitRegistry<'tcx, 'rcx>,
    functions: &'rcx [LocalDefId],
    fn_arena: &'rcx Arena<radium::FunctionSpec<radium::InnerFunctionSpec<'rcx>>>,

    /// the second component determines whether to include it in the code file as well
    extra_exports: HashSet<(coq::module::Export, bool)>,

    /// extra Coq module dependencies (for generated dune files)
    extra_dependencies: HashSet<coq::module::DirPath>,

    coq_path_prefix: String,
    dune_package: Option<String>,
    shim_registry: shim_registry::ShimRegistry<'rcx>,

    /// trait implementations we generated
    trait_impls: HashMap<DefId, radium::TraitImplSpec<'rcx>>,
}

impl<'tcx, 'rcx> VerificationCtxt<'tcx, 'rcx> {
    fn get_path_for_shim(&self, did: DefId) -> Vec<&str> {
        let path = utils::get_export_path_for_did(self.env, did);
        let interned_path = self.shim_registry.intern_path(path);
        interned_path
    }

    fn make_shim_function_entry(&self, did: DefId, spec_name: &str) -> Option<shim_registry::FunctionShim> {
        let Some(mode) = self.procedure_registry.lookup_function_mode(did) else {
            return None;
        };

        if mode != ProcedureMode::Prove && mode != ProcedureMode::OnlySpec && mode != ProcedureMode::TrustMe {
            return None;
        }

        if self.env.tcx().visibility(did) != ty::Visibility::Public {
            // don't export
            return None;
        }

        // only export public items
        let is_method = self.env.tcx().impl_of_method(did).is_some();
        let interned_path = self.get_path_for_shim(did);

        let name = type_translator::strip_coq_ident(&self.env.get_item_name(did));
        info!("Found function path {:?} for did {:?} with name {:?}", interned_path, did, name);

        Some(shim_registry::FunctionShim {
            path: interned_path,
            is_method,
            name,
            spec_name: spec_name.to_owned(),
        })
    }

    fn make_shim_trait_method_entry(
        &self,
        did: DefId,
        spec_name: &str,
    ) -> Option<shim_registry::TraitMethodImplShim> {
        trace!("enter make_shim_trait_method_entry; did={did:?}");

        let Some(mode) = self.procedure_registry.lookup_function_mode(did) else {
            trace!("leave make_shim_trait_method_entry (failed)");
            return None;
        };

        if mode != ProcedureMode::Prove && mode != ProcedureMode::OnlySpec && mode != ProcedureMode::TrustMe {
            trace!("leave make_shim_trait_method_entry (failed)");
            return None;
        }

        match self.env.tcx().visibility(did) {
            // only export public items
            ty::Visibility::Public => {
                let impl_did = self.env.tcx().impl_of_method(did).unwrap();

                let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> =
                    self.env.tcx().impl_trait_ref(impl_did);

                let Some(impl_ref) = impl_ref else {
                    trace!("leave make_shim_trait_method_entry (failed)");
                    return None;
                };

                let impl_ref =
                    normalize_in_function(impl_did, self.env.tcx(), impl_ref.skip_binder()).unwrap();

                let args = impl_ref.args;
                let trait_did = impl_ref.def_id;

                // the first arg is self, skip that
                let trait_args = &args.as_slice()[1..];
                let impl_for = args[0].expect_ty();

                // flatten the trait reference
                let trait_path = utils::PathWithArgs::from_item(self.env, trait_did, trait_args)?;
                trace!("got trait path: {:?}", trait_path);

                // flatten the self type.
                let Some(for_type) = utils::convert_ty_to_flat_type(self.env, impl_for) else {
                    return None;
                };

                trace!("implementation for: {:?}", impl_for);

                // get name of this function
                let Some(ident) = self.env.tcx().opt_item_ident(did) else {
                    // can not find name of this function
                    return None;
                };

                let method_ident = ident.as_str().to_owned();
                let name = type_translator::strip_coq_ident(&self.env.get_item_name(did));

                trace!("leave make_shim_trait_method_entry (success)");
                Some(shim_registry::TraitMethodImplShim {
                    trait_path,
                    method_ident,
                    for_type,
                    name,
                    spec_name: spec_name.to_owned(),
                })
            },
            ty::Visibility::Restricted(_) => {
                // don't export
                trace!("leave make_shim_trait_method_entry (failed)");
                None
            },
        }
    }

    /// Make a shim entry for a trait.
    fn make_trait_impl_shim_entry(
        &self,
        did: DefId,
        decl: &radium::TraitImplSpec<'rcx>,
    ) -> Option<shim_registry::TraitImplShim> {
        info!("making shim entry for impl {did:?}");
        let impl_ref: Option<ty::EarlyBinder<ty::TraitRef<'_>>> = self.env.tcx().impl_trait_ref(did);

        let Some(impl_ref) = impl_ref else {
            trace!("leave make_trait_impl_shim_entry (failed getting impl ref)");
            return None;
        };

        let impl_ref = normalize_in_function(did, self.env.tcx(), impl_ref.skip_binder()).unwrap();

        let args = impl_ref.args;
        let trait_did = impl_ref.def_id;

        // the first arg is self, skip that
        // TODO don't handle Self specially, but treat it as any other arg
        let trait_args = &args.as_slice()[1..];
        let impl_for = args[0].expect_ty();

        // flatten the trait reference
        let trait_path = utils::PathWithArgs::from_item(self.env, trait_did, trait_args)?;
        trace!("got trait path: {:?}", trait_path);

        // flatten the self type.
        let Some(for_type) = utils::convert_ty_to_flat_type(self.env, impl_for) else {
            trace!("leave make_impl_shim_entry (failed transating self type)");
            return None;
        };

        trace!("implementation for: {:?}", impl_for);

        let mut method_specs = HashMap::new();
        for (name, spec) in &decl.methods.methods {
            method_specs.insert(name.to_owned(), (spec.function_name.clone(), spec.spec_name.clone()));
        }

        let a = shim_registry::TraitImplShim {
            trait_path,
            for_type,
            method_specs,
            spec_params_record: decl.names.spec_params_record.clone(),
            spec_attrs_record: decl.names.spec_attrs_record.clone(),
            spec_record: decl.names.spec_record.clone(),
            spec_subsumption_proof: decl.names.spec_subsumption_proof.clone(),
        };

        Some(a)
    }

    /// Make a shim entry for a trait.
    fn make_trait_shim_entry(
        &self,
        did: LocalDefId,
        decl: radium::LiteralTraitSpecRef<'rcx>,
    ) -> Option<shim_registry::TraitShim> {
        info!("making shim entry for {did:?}");
        if ty::Visibility::Public == self.env.tcx().visibility(did.to_def_id()) {
            let interned_path = self.get_path_for_shim(did.into());
            let a = shim_registry::TraitShim {
                path: interned_path,
                name: decl.name.clone(),
                spec_param_record: decl.spec_params_record.clone(),
                spec_attrs_record: decl.spec_attrs_record.clone(),
                spec_record: decl.spec_record.clone(),
                base_spec: decl.base_spec.clone(),
                base_spec_params: decl.base_spec_params.clone(),
                spec_subsumption: decl.spec_subsumption.clone(),
                allowed_attrs: decl.declared_attrs.clone(),
            };
            return Some(a);
        }
        None
    }

    fn make_adt_shim_entry(&self, did: DefId, lit: radium::LiteralType) -> Option<shim_registry::AdtShim> {
        info!("making shim entry for {did:?}");
        if did.is_local() && ty::Visibility::Public == self.env.tcx().visibility(did) {
            // only export public items
            let interned_path = self.get_path_for_shim(did);
            let name = type_translator::strip_coq_ident(&self.env.get_item_name(did));

            info!("Found adt path {:?} for did {:?} with name {:?}", interned_path, did, name);

            let a = shim_registry::AdtShim {
                path: interned_path,
                refinement_type: lit.refinement_type.to_string(),
                syn_type: lit.syn_type.to_string(),
                sem_type: lit.type_term,
            };
            return Some(a);
        }

        None
    }

    fn generate_module_summary(&self, module_path: &str, module: &str, name: &str, path: &Path) {
        let mut function_shims = Vec::new();
        let mut adt_shims = Vec::new();
        let mut trait_method_shims = Vec::new();
        let mut trait_shims = Vec::new();
        let mut trait_impl_shims = Vec::new();

        // traits
        let decls = self.trait_registry.get_trait_decls();
        for (did, decl) in &decls {
            if let Some(entry) = self.make_trait_shim_entry(*did, decl.lit) {
                trait_shims.push(entry);
            }
        }

        // trait impls
        for (did, decl) in &self.trait_impls {
            if let Some(entry) = self.make_trait_impl_shim_entry(*did, decl) {
                trait_impl_shims.push(entry);
            } else {
                info!("Creating trait impl shim entry failed for {did:?}");
            }
        }

        // ADTs
        let variant_defs = self.type_translator.get_variant_defs();
        let enum_defs = self.type_translator.get_enum_defs();

        for (did, entry) in &variant_defs {
            if let Some(entry) = entry {
                if let Some(shim) = self.make_adt_shim_entry(*did, entry.make_literal_type()) {
                    adt_shims.push(shim);
                }
            }
        }
        for (did, entry) in &enum_defs {
            if let Some(entry) = entry {
                if let Some(shim) = self.make_adt_shim_entry(*did, entry.make_literal_type()) {
                    adt_shims.push(shim);
                }
            }
        }

        // trait method implementations are handled differently, so we keep track of them here
        let mut trait_methods = Vec::new();

        // functions and methods
        for (did, fun) in self.procedure_registry.iter_code() {
            if let Some(impl_did) = self.env.tcx().impl_of_method(*did) {
                info!("found impl method: {:?}", did);
                if self.env.tcx().trait_id_of_impl(impl_did).is_some() {
                    info!("found trait method: {:?}", did);
                    trait_methods.push((did, fun.spec));
                    continue;
                }
            }
            if let Some(shim) = self.make_shim_function_entry(*did, &fun.spec.spec_name) {
                function_shims.push(shim);
            }
        }

        for (did, fun) in self.procedure_registry.iter_only_spec() {
            if let Some(impl_did) = self.env.tcx().impl_of_method(*did) {
                info!("found impl method: {:?}", did);
                if self.env.tcx().trait_id_of_impl(impl_did).is_some() {
                    info!("found trait method: {:?}", did);
                    trait_methods.push((did, fun));
                    continue;
                }
            }
            if let Some(shim) = self.make_shim_function_entry(*did, &fun.spec_name) {
                function_shims.push(shim);
            }
        }

        // trait methods
        for (did, fun) in trait_methods {
            if let Some(impl_did) = self.env.tcx().impl_of_method(*did) {
                // only register this as a separate method if it isn't part of a complete impl
                if self.trait_impls.get(&impl_did).is_none() {
                    if let Some(shim) = self.make_shim_trait_method_entry(*did, &fun.spec_name) {
                        trait_method_shims.push(shim);
                    }
                }
            }
        }

        let mut module_dependencies: Vec<coq::module::DirPath> =
            self.extra_exports.iter().filter_map(|(export, _)| export.get_path()).collect();

        module_dependencies.extend(self.extra_dependencies.iter().cloned());

        info!("Generated module summary ADTs: {:?}", adt_shims);
        info!("Generated module summary functions: {:?}", function_shims);

        let interface_file = File::create(path).unwrap();
        shim_registry::write_shims(
            interface_file,
            module_path,
            module,
            name,
            &module_dependencies,
            adt_shims,
            function_shims,
            trait_method_shims,
            trait_shims,
            trait_impl_shims,
        );
    }

    /// Write specifications of a verification unit.
    fn write_specifications(&self, spec_path: &Path, code_path: &Path, stem: &str) {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        let mut spec_file = io::BufWriter::new(File::create(spec_path).unwrap());
        let mut code_file = io::BufWriter::new(File::create(code_path).unwrap());

        {
            let mut spec_exports = vec![
                coq::module::Export::new(vec![format!("generated_code_{stem}")])
                    .from(vec![&self.coq_path_prefix, stem]),
            ];
            spec_exports.append(&mut self.extra_exports.iter().map(|(export, _)| export.clone()).collect());

            write!(spec_file, "{}", coq::module::ImportList(&common_imports)).unwrap();
            write!(spec_file, "{}", coq::module::ExportList(&spec_exports)).unwrap();
        }

        {
            let code_exports = self
                .extra_exports
                .iter()
                .filter(|(_, include)| *include)
                .map(|(export, _)| export.clone())
                .collect();

            write!(code_file, "{}", coq::module::ImportList(&common_imports)).unwrap();
            write!(code_file, "{}", coq::module::ExportList(&code_exports)).unwrap();
        }

        // write structs and enums
        // we need to do a bit of work to order them right
        {
            let struct_defs = self.type_translator.get_struct_defs();
            let enum_defs = self.type_translator.get_enum_defs();
            let adt_deps = self.type_translator.get_adt_deps();

            let ordered = order_adt_defs(&adt_deps);
            info!("ordered ADT defns: {:?}", ordered);

            for did in &ordered {
                if let Some(su_ref) = struct_defs.get(did) {
                    info!("writing struct {:?}, {:?}", did, su_ref);
                    let su = su_ref.as_ref().unwrap();

                    // layout specs
                    writeln!(code_file, "{}", su.generate_coq_sls_def()).unwrap();

                    // type aliases
                    writeln!(spec_file, "{}", su.generate_coq_type_def()).unwrap();

                    // abstracted type
                    if let Some(inv_spec) = su.generate_optional_invariant_def() {
                        writeln!(spec_file, "{}", inv_spec).unwrap();
                    }
                } else {
                    let eu = enum_defs[did].unwrap();
                    info!("writing enum {:?}, {:?}", did, eu);

                    // layout specs
                    writeln!(code_file, "{}", eu.generate_coq_els_def()).unwrap();

                    // type definition
                    writeln!(spec_file, "{}", eu.generate_coq_type_def()).unwrap();
                }
            }
        }

        // write tuples up to the necessary size
        // TODO

        // write trait specs
        let trait_deps = self.trait_registry.get_registered_trait_deps();
        let dep_order = order_adt_defs(&trait_deps);
        let trait_decls = self.trait_registry.get_trait_decls();
        for did in dep_order {
            let decl = &trait_decls[&did.as_local().unwrap()];
            write!(spec_file, "{decl}\n").unwrap();
        }

        // write the attribute spec declarations of trait impls
        {
            writeln!(spec_file, "Section attrs.").unwrap();
            writeln!(spec_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            for spec in self.trait_impls.values() {
                writeln!(spec_file, "{}.\n", spec.generate_attr_decl()).unwrap();
            }
            writeln!(spec_file, "End attrs.\n").unwrap();
        }

        // write translated source code of functions
        {
            writeln!(code_file, "Section code.").unwrap();
            writeln!(code_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(code_file, "Open Scope printing_sugar.").unwrap();
            writeln!(code_file).unwrap();

            for (_, fun) in self.procedure_registry.iter_code() {
                writeln!(code_file, "{}", fun.code).unwrap();
                writeln!(code_file).unwrap();
            }

            write!(code_file, "End code.").unwrap();
        }

        // write function specs
        {
            writeln!(spec_file, "Section specs.").unwrap();
            writeln!(spec_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(spec_file).unwrap();

            for (_, fun) in self.procedure_registry.iter_code() {
                if fun.spec.is_complete() {
                    //if fun.spec.spec.args.len() != fun.code.get_argument_count() {
                    //warn!("Function specification for {} is missing arguments", fun.name());
                    //}

                    writeln!(spec_file, "{}", fun.spec).unwrap();
                } else {
                    warn!("No specification for {}", fun.name());

                    writeln!(spec_file, "(* No specification provided for {} *)", fun.name()).unwrap();
                }
            }
            writeln!(spec_file).unwrap();
        }

        // also write only-spec functions specs
        {
            for (_, spec) in self.procedure_registry.iter_only_spec() {
                if spec.is_complete() {
                    writeln!(spec_file, "{spec}").unwrap();
                } else {
                    writeln!(spec_file, "(* No specification provided for {} *)", spec.function_name)
                        .unwrap();
                }
            }
            writeln!(spec_file).unwrap();
        }

        // Include extra specs
        {
            if let Some(extra_specs_path) = rrconfig::extra_specs_file() {
                writeln!(
                    spec_file,
                    "(* Included specifications from configured file {:?} *)",
                    extra_specs_path
                )
                .unwrap();

                let mut extra_specs_file = io::BufReader::new(File::open(extra_specs_path).unwrap());
                let mut extra_specs_string = String::new();
                extra_specs_file.read_to_string(&mut extra_specs_string).unwrap();

                write!(spec_file, "{}", extra_specs_string).unwrap();
            }
        }

        writeln!(spec_file, "End specs.").unwrap();

        // write trait impls
        {
            for spec in self.trait_impls.values() {
                writeln!(spec_file, "{spec}").unwrap();
            }
        }
    }

    /// Write proof templates for a verification unit.
    fn write_templates<F>(&self, file_path: F, stem: &str)
    where
        F: Fn(&str) -> PathBuf,
    {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        // write templates
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(fun.name());
            let mut template_file = io::BufWriter::new(File::create(path.as_path()).unwrap());

            let mode = self.procedure_registry.lookup_function_mode(*did).unwrap();

            if fun.spec.is_complete() && mode.needs_proof() {
                let mut imports = common_imports.clone();

                imports.append(&mut vec![
                    coq::module::Import::new(vec![
                        &format!("generated_code_{stem}"),
                        &format!("generated_specs_{stem}"),
                    ])
                    .from(vec![&self.coq_path_prefix, stem]),
                ]);

                let exports: Vec<_> = self.extra_exports.iter().map(|(export, _)| export.clone()).collect();

                write!(template_file, "{}", coq::module::ImportList(&imports)).unwrap();
                write!(template_file, "{}", coq::module::ExportList(&exports)).unwrap();
                write!(template_file, "\n").unwrap();

                write!(template_file, "Set Default Proof Using \"Type\".\n\n").unwrap();
                write!(
                    template_file,
                    "\
                    Section proof.\n\
                    Context `{{RRGS : !refinedrustGS Σ}}.\n"
                )
                .unwrap();

                fun.generate_lemma_statement(&mut template_file).unwrap();

                write!(template_file, "End proof.\n\n").unwrap();

                fun.generate_proof_prelude(&mut template_file).unwrap();
            } else if !fun.spec.is_complete() {
                write!(template_file, "(* No specification provided *)").unwrap();
            } else {
                write!(template_file, "(* Function is trusted *)").unwrap();
            }
        }
    }

    fn check_function_needs_proof(&self, did: DefId, fun: &radium::Function) -> bool {
        let mode = self.procedure_registry.lookup_function_mode(did).unwrap();
        fun.spec.is_complete() && mode.needs_proof()
    }

    /// Write proofs for a verification unit.
    fn write_proofs<F>(&self, file_path: F, stem: &str)
    where
        F: Fn(&str) -> PathBuf,
    {
        let common_imports = vec![
            coq::module::Import::new(vec!["lang", "notation"]).from(vec!["caesium"]),
            coq::module::Import::new(vec!["typing", "shims"]).from(vec!["refinedrust"]),
        ];

        // write proofs
        // each function gets a separate file in order to parallelize
        for (did, fun) in self.procedure_registry.iter_code() {
            let path = file_path(fun.name());

            if path.exists() {
                info!("Proof file for function {} already exists, skipping creation", fun.name());
                continue;
            }

            if !self.check_function_needs_proof(*did, fun) {
                continue;
            }

            info!("Proof file for function {} does not yet exist, creating", fun.name());

            let mut proof_file = io::BufWriter::new(File::create(path.as_path()).unwrap());

            let mut imports = common_imports.clone();

            imports.append(&mut vec![
                coq::module::Import::new(vec![
                    &format!("generated_code_{stem}"),
                    &format!("generated_specs_{stem}"),
                    &format!("generated_template_{}", fun.name()),
                ])
                .from(vec![&self.coq_path_prefix, stem, "generated"]),
            ]);

            writeln!(proof_file, "{}", coq::module::ImportList(&imports)).unwrap();

            // Note: we do not export the self.extra_exports explicitly, as we rely on them
            // being re-exported from the template -- we want to be stable under changes of the
            // extras

            writeln!(proof_file, "Set Default Proof Using \"Type\".").unwrap();
            writeln!(proof_file).unwrap();

            writeln!(proof_file, "Section proof.").unwrap();
            writeln!(proof_file, "Context `{{RRGS : !refinedrustGS Σ}}.").unwrap();
            writeln!(proof_file).unwrap();

            fun.generate_proof(&mut proof_file, rrconfig::admit_proofs()).unwrap();

            writeln!(proof_file, "End proof.").unwrap();
        }
    }

    /// Write Coq files for this verification unit.
    pub fn write_coq_files(&self) {
        // use the crate_name for naming
        let crate_name: span::symbol::Symbol = self.env.tcx().crate_name(span::def_id::LOCAL_CRATE);
        let stem = crate_name.as_str();

        // create output directory
        let Some(mut base_dir_path) = rrconfig::output_dir() else {
            info!("No output directory specified, not writing files");
            return;
        };

        base_dir_path.push(stem);

        if fs::read_dir(base_dir_path.as_path()).is_err() {
            warn!("Output directory {:?} does not exist, creating directory", base_dir_path);
            fs::create_dir_all(base_dir_path.as_path()).unwrap();
        }

        let toplevel_module_path = self.coq_path_prefix.clone();
        let coq_module_path = format!("{}.{}", toplevel_module_path, stem);
        let generated_module_path = format!("{}.generated", coq_module_path);
        let proof_module_path = format!("{}.proofs", coq_module_path);

        // write gitignore file
        let gitignore_path = base_dir_path.as_path().join(".gitignore");
        {
            let mut gitignore_file = io::BufWriter::new(File::create(gitignore_path.as_path()).unwrap());
            write!(
                gitignore_file,
                "\
                generated\n\
                proofs/dune\n\
                interface.rrlib"
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

        // write the dune-project file, if required
        if rrconfig::generate_dune_project() {
            let mut dune_project_path = rrconfig::absolute_work_dir();
            dune_project_path.push("dune-project");

            if !dune_project_path.exists() {
                let mut dune_project_file =
                    io::BufWriter::new(File::create(dune_project_path.as_path()).unwrap());

                let (project_name, dune_project_package) = if let Some(dune_package) = &self.dune_package {
                    (dune_package.to_string(), format!("(package (name {dune_package}))\n"))
                } else {
                    (stem.to_owned(), String::new())
                };

                write!(
                    dune_project_file,
                    "\
                    (lang dune 3.8)\n\
                    (using coq 0.8)\n\
                    (name {project_name})\n{dune_project_package}",
                )
                .unwrap();
            }
        }

        // write generated (subdirectory "generated")
        info!("outputting generated code to {}", generated_dir_path.to_str().unwrap());
        if fs::read_dir(generated_dir_path).is_err() {
            warn!("Output directory {:?} does not exist, creating directory", generated_dir_path);
        } else {
            // purge contents
            info!("Removing the contents of the generated directory");
            fs::remove_dir_all(generated_dir_path).unwrap();
        }
        fs::create_dir_all(generated_dir_path).unwrap();

        let code_path = generated_dir_path.join(format!("generated_code_{}.v", stem));
        let spec_path = generated_dir_path.join(format!("generated_specs_{}.v", stem));
        let generated_dune_path = generated_dir_path.join("dune");

        // write specs
        self.write_specifications(spec_path.as_path(), code_path.as_path(), stem);

        // write templates
        self.write_templates(|name| generated_dir_path.join(format!("generated_template_{name}.v")), stem);

        // write dune meta file
        let mut dune_file = io::BufWriter::new(File::create(generated_dune_path.as_path()).unwrap());

        let mut extra_theories: HashSet<coq::module::DirPath> =
            self.extra_exports.iter().filter_map(|(export, _)| export.get_path()).collect();

        extra_theories.extend(self.extra_dependencies.iter().cloned());

        let extra_theories: Vec<String> = extra_theories.into_iter().map(|x| x.to_string()).collect();

        let dune_package = if let Some(dune_package) = &self.dune_package {
            format!("(package {dune_package})\n")
        } else {
            String::new()
        };

        write!(
            dune_file,
            "\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n{dune_package}\
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

            for file in read.flatten() {
                // check if the file name is okay
                let filename = file.file_name();
                let Some(filename) = filename.to_str() else {
                    continue;
                };

                if filename == "dune" {
                    continue;
                }
                if proof_files_to_generate.contains(filename) {
                    continue;
                }

                println!("Warning: Proof file {filename} does not have a matching Rust function to verify.");
            }
        } else {
            warn!("Output directory {:?} does not exist, creating directory", proof_dir_path);
            fs::create_dir_all(proof_dir_path).unwrap();
        }

        self.write_proofs(|name| proof_dir_path.join(format!("proof_{name}.v")), stem);

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
        let mut dune_file = io::BufWriter::new(File::create(proof_dune_path.as_path()).unwrap());
        write!(dune_file, "\
            ; Generated by [refinedrust], do not edit.\n\
            (coq.theory\n\
             (flags -w -notation-overridden -w -redundant-canonical-projection)\n{dune_package}\
             (name {proof_module_path})\n\
             (modules {})\n\
             (theories stdpp iris Ltac2 Equations RecordUpdate lrust caesium lithium refinedrust {} {}.{}.generated))",
             proof_modules.join(" "), extra_theories.join(" "), self.coq_path_prefix, stem).unwrap();
    }
}

/// Register shims in the procedure registry.
fn register_shims<'tcx>(vcx: &mut VerificationCtxt<'tcx, '_>) -> Result<(), base::TranslationError<'tcx>> {
    for shim in vcx.shim_registry.get_function_shims() {
        let did = if shim.is_method {
            utils::try_resolve_method_did(vcx.env.tcx(), &shim.path)
        } else {
            utils::try_resolve_did(vcx.env.tcx(), &shim.path)
        };

        match did {
            Some(did) => {
                // register as usual in the procedure registry
                info!("registering shim for {:?}", shim.path);
                let meta = function_body::ProcedureMeta::new(
                    shim.spec_name.clone(),
                    shim.name.clone(),
                    function_body::ProcedureMode::Shim,
                );
                vcx.procedure_registry.register_function(did, meta)?;
            },
            _ => {
                println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
            },
        }
    }

    for shim in vcx.shim_registry.get_adt_shims() {
        let Some(did) = utils::try_resolve_did(vcx.env.tcx(), &shim.path) else {
            println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
            continue;
        };

        let lit = radium::LiteralType {
            rust_name: None,
            type_term: shim.sem_type.clone(),
            syn_type: radium::SynType::Literal(shim.syn_type.clone()),
            refinement_type: coq::term::Type::Literal(shim.refinement_type.clone()),
        };

        if let Err(e) = vcx.type_translator.register_adt_shim(did, &lit) {
            println!("Warning: {}", e);
        }

        info!("Resolved ADT shim {:?} as {:?} did", shim, did);
    }

    for shim in vcx.shim_registry.get_trait_shims() {
        if let Some(did) = utils::try_resolve_did(vcx.env.tcx(), &shim.path) {
            let assoc_tys = vcx.trait_registry.get_associated_type_names(did);
            let spec = radium::LiteralTraitSpec {
                assoc_tys,
                name: shim.name.clone(),
                spec_attrs_record: shim.spec_attrs_record.clone(),
                spec_params_record: shim.spec_param_record.clone(),
                spec_record: shim.spec_record.clone(),
                base_spec: shim.base_spec.clone(),
                base_spec_params: shim.base_spec_params.clone(),
                spec_subsumption: shim.spec_subsumption.clone(),
                declared_attrs: shim.allowed_attrs.clone(),
            };

            vcx.trait_registry.register_shim(did, spec)?;
        } else {
            println!("Warning: cannot find defid for shim {:?}, skipping", shim.path);
        }
    }

    for shim in vcx.shim_registry.get_trait_impl_shims() {
        // resolve the trait
        let Some((trait_did, args)) = shim.trait_path.to_item(vcx.env.tcx()) else {
            println!("Warning: cannot resolve {:?} as a trait, skipping shim", shim.trait_path);
            continue;
        };

        if !vcx.env.tcx().is_trait(trait_did) {
            println!("Warning: This is not a trait: {:?}", shim.trait_path);
            continue;
        }

        // resolve the type
        let Some(for_type) = shim.for_type.to_type(vcx.env.tcx()) else {
            println!("Warning: cannot resolve {:?} as a type, skipping shim", shim.for_type);
            continue;
        };

        let trait_impl_did = utils::try_resolve_trait_impl_did(vcx.env.tcx(), trait_did, &args, for_type);

        let Some(did) = trait_impl_did else {
            println!(
                "Warning: cannot find defid for implementation of {:?} for {:?}",
                shim.trait_path, for_type
            );
            continue;
        };

        let impl_lit = radium::LiteralTraitImpl::new(
            shim.spec_record.clone(),
            shim.spec_params_record.clone(),
            shim.spec_attrs_record.clone(),
            shim.spec_subsumption_proof.clone(),
        );
        vcx.trait_registry.register_impl_shim(did, impl_lit)?;

        // now register all the method shims
        let impl_assoc_items: &ty::AssocItems = vcx.env.tcx().associated_items(did);
        for (method_name, (name, spec_name)) in &shim.method_specs {
            // find the right item
            if let Some(item) = impl_assoc_items.find_by_name_and_kind(
                vcx.env.tcx(),
                span::symbol::Ident::from_str(method_name),
                ty::AssocKind::Fn,
                trait_did,
            ) {
                let method_did = item.def_id;
                // register as usual in the procedure registry
                info!(
                    "registering shim for implementation of {:?}::{:?} for {:?}, using method {:?}",
                    shim.trait_path, method_name, for_type, method_did
                );

                let meta = function_body::ProcedureMeta::new(
                    spec_name.clone(),
                    name.clone(),
                    function_body::ProcedureMode::Shim,
                );

                vcx.procedure_registry.register_function(method_did, meta)?;
            }
        }
    }

    // add the extra exports
    vcx.extra_exports
        .extend(vcx.shim_registry.get_extra_exports().iter().map(|export| (export.clone(), true)));
    // add the extra dependencies
    vcx.extra_dependencies.extend(vcx.shim_registry.get_extra_dependencies().iter().cloned());

    Ok(())
}

fn get_most_restrictive_function_mode(
    vcx: &VerificationCtxt<'_, '_>,
    did: DefId,
) -> function_body::ProcedureMode {
    let attrs = vcx.env.get_attributes_of_function(did, &propagate_method_attr_from_impl);

    // check if this is a purely spec function; if so, skip.
    if utils::has_tool_attr_filtered(attrs.as_slice(), "shim") {
        return function_body::ProcedureMode::Shim;
    }

    if utils::has_tool_attr_filtered(attrs.as_slice(), "trust_me") {
        return function_body::ProcedureMode::TrustMe;
    }

    if utils::has_tool_attr_filtered(attrs.as_slice(), "only_spec") {
        return function_body::ProcedureMode::OnlySpec;
    }

    if utils::has_tool_attr_filtered(attrs.as_slice(), "ignore") {
        info!("Function {:?} will be ignored", did);
        return function_body::ProcedureMode::Ignore;
    }

    function_body::ProcedureMode::Prove
}

/// Register functions of the crate in the procedure registry.
fn register_functions<'tcx>(
    vcx: &mut VerificationCtxt<'tcx, '_>,
) -> Result<(), base::TranslationError<'tcx>> {
    for &f in vcx.functions {
        let mut mode = get_most_restrictive_function_mode(vcx, f.to_def_id());

        if mode == function_body::ProcedureMode::Shim {
            // TODO better error message
            let attrs = vcx.env.get_attributes(f.to_def_id());
            let v = utils::filter_tool_attrs(attrs);
            let annot = spec_parsers::get_shim_attrs(v.as_slice()).unwrap();

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
            vcx.procedure_registry.register_function(f.to_def_id(), meta)?;

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

        vcx.procedure_registry.register_function(f.to_def_id(), meta)?;
    }
    Ok(())
}

/// Translate functions of the crate, assuming they were previously registered.
fn translate_functions<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) {
    for &f in vcx.functions {
        let proc = vcx.env.get_procedure(f.to_def_id());
        let fname = vcx.env.get_item_name(f.to_def_id());
        let meta = vcx.procedure_registry.lookup_function(f.to_def_id()).unwrap();

        let filtered_attrs =
            vcx.env.get_attributes_of_function(f.to_def_id(), &propagate_method_attr_from_impl);

        let mode = meta.get_mode();
        if mode.is_shim() {
            continue;
        }
        if mode.is_ignore() {
            continue;
        }

        info!("\nTranslating function {}", fname);

        let ty: ty::EarlyBinder<ty::Ty<'tcx>> = vcx.env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();

        let translator = match ty.kind() {
            ty::TyKind::FnDef(_def, _args) => FunctionTranslator::new(
                vcx.env,
                &meta,
                proc,
                &filtered_attrs,
                vcx.type_translator,
                vcx.trait_registry,
                &vcx.procedure_registry,
                &vcx.const_registry,
            ),
            ty::TyKind::Closure(_, _) => FunctionTranslator::new_closure(
                vcx.env,
                &meta,
                proc,
                &filtered_attrs,
                vcx.type_translator,
                vcx.trait_registry,
                &vcx.procedure_registry,
                &vcx.const_registry,
            ),
            _ => Err(base::TranslationError::UnknownError("unknown function kind".to_owned())),
        };

        if mode.is_only_spec() {
            // Only generate a spec
            match translator.and_then(FunctionTranslator::generate_spec) {
                Ok(spec) => {
                    println!("Successfully generated spec for {}", fname);
                    let spec_ref = vcx.fn_arena.alloc(spec);
                    vcx.procedure_registry.provide_specced_function(f.to_def_id(), spec_ref);
                },
                Err(base::TranslationError::FatalError(err)) => {
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
            match translator.and_then(|x| x.translate(vcx.fn_arena)) {
                Ok(fun) => {
                    println!("Successfully translated {}", fname);
                    vcx.procedure_registry.provide_translated_function(f.to_def_id(), fun);
                },
                Err(base::TranslationError::FatalError(err)) => {
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
    process::exit(-1);
}

/// Get all functions and closures in the current crate that have attributes on them and are not
/// skipped due to `rr::skip` attributes.
pub fn get_filtered_functions(env: &Environment<'_>) -> Vec<LocalDefId> {
    let mut functions = env.get_procedures();
    let closures = env.get_closures();
    info!("Found {} function(s) and {} closure(s)", functions.len(), closures.len());
    functions.extend(closures);

    let functions_with_spec: Vec<_> = functions
        .into_iter()
        .filter(|id| {
            if !env.has_any_tool_attribute(id.to_def_id()) {
                return false;
            }

            if env.has_tool_attribute(id.to_def_id(), "skip") {
                warn!("Function {:?} will be skipped due to a rr::skip annotation", id);
                return false;
            }

            let Some(impl_did) = env.tcx().impl_of_method(id.to_def_id()) else {
                return true;
            };

            if env.has_tool_attribute(impl_did, "skip") {
                warn!("Function {:?} will be skipped due to a rr::skip annotation on impl", id);
                return false;
            }

            true
        })
        .collect();

    for f in &functions_with_spec {
        info!("Function {:?} has a spec and will be processed", f);
    }
    functions_with_spec
}

/// Get constants in the current scope.
pub fn register_consts<'rcx, 'tcx>(vcx: &mut VerificationCtxt<'tcx, 'rcx>) -> Result<(), String> {
    let statics = vcx.env.get_statics();

    for s in &statics {
        let ty: ty::EarlyBinder<ty::Ty<'tcx>> = vcx.env.tcx().type_of(s.to_def_id());

        let const_attrs = utils::filter_tool_attrs(vcx.env.get_attributes(s.to_def_id()));
        if const_attrs.is_empty() {
            continue;
        }

        let ty = ty.skip_binder();
        let scope = ParamScope::default();
        match vcx.type_translator.translate_type_in_scope(scope, ty).map_err(|x| format!("{:?}", x)) {
            Ok(translated_ty) => {
                let _full_name = type_translator::strip_coq_ident(&vcx.env.get_item_name(s.to_def_id()));

                let mut const_parser = VerboseConstAttrParser::new();
                let const_spec = const_parser.parse_const_attrs(*s, &const_attrs)?;

                let name = const_spec.name;
                let loc_name = format!("{name}_loc");

                let meta = radium::StaticMeta {
                    ident: name,
                    loc_name,
                    ty: translated_ty,
                };
                vcx.const_registry.register_static(s.to_def_id(), meta);
            },
            Err(e) => {
                println!("Warning: static {:?} has unsupported type, skipping: {:?}", s, e);
            },
        }
    }
    Ok(())
}

/// Register traits.
fn register_traits(vcx: &VerificationCtxt<'_, '_>) -> Result<(), String> {
    let mut traits = vcx.env.get_traits();

    // order according to dependencies first
    let deps = vcx.trait_registry.get_trait_deps(traits.as_slice());
    let ordered_traits = order_adt_defs(&deps);

    for t in &ordered_traits {
        let t = t.as_local().unwrap();

        info!("found trait {:?}", t);
        let mut all_have_annots = true;
        let mut some_has_annot = false;
        // check that all children have a specification
        let children = vcx.env.tcx().module_children_local(t);
        for c in children {
            if let hir::def::Res::Def(def_kind, def_id) = c.res {
                if def_kind == hir::def::DefKind::AssocFn {
                    if vcx.env.has_any_tool_attribute(def_id) {
                        some_has_annot = true;
                    } else {
                        all_have_annots = false;
                    }
                }
            }
        }
        if !all_have_annots {
            if some_has_annot {
                println!("Warning: not all of trait {t:?}'s items are annotated, skipping");
            }
            continue;
        }

        vcx.trait_registry
            .register_trait(vcx.type_translator, t)
            .map_err(|x| format!("{x:?}"))
            .map_err(|e| format!("{e:?}"))?;
    }
    Ok(())
}

/// Register trait impls of all registered traits.
/// Precondition: traits have already been registered.
fn register_trait_impls(vcx: &VerificationCtxt<'_, '_>) -> Result<(), String> {
    let trait_impl_ids = vcx.env.get_trait_impls();
    info!("Found trait impls: {:?}", trait_impl_ids);

    for trait_impl_id in trait_impl_ids {
        let did = trait_impl_id.to_def_id();
        let trait_did = vcx.env.tcx().trait_id_of_impl(did).unwrap();

        // check if this trait has been registered
        if vcx.trait_registry.lookup_trait(trait_did).is_some() {
            // make sure all functions have a spec; otherwise, this is not a complete trait impl
            let assoc_items: &ty::AssocItems = vcx.env.tcx().associated_items(did);
            let mut all_specced = true;
            for x in assoc_items.in_definition_order() {
                if x.kind == ty::AssocKind::Fn {
                    // check if all functions have a specification
                    if let Some(mode) = vcx.procedure_registry.lookup_function_mode(x.def_id) {
                        all_specced = all_specced && mode.needs_spec();
                    } else {
                        all_specced = false;
                    }
                }
            }
            if !all_specced {
                continue;
            }

            // make names for the spec and inclusion proof
            let base_name = type_translator::strip_coq_ident(&vcx.env.get_item_name(did));
            let spec_name = format!("{base_name}_spec");
            let spec_params_name = format!("{base_name}_spec_params");
            let spec_attrs_name = format!("{base_name}_spec_attrs");
            let proof_name = format!("{base_name}_spec_subsumption");

            let impl_lit = radium::LiteralTraitImpl {
                spec_record: spec_name,
                spec_params_record: spec_params_name,
                spec_attrs_record: spec_attrs_name,
                spec_subsumption_proof: proof_name,
            };
            vcx.trait_registry
                .register_impl_shim(did, impl_lit)
                .map_err(|x| ToString::to_string(&x))?;
        }
    }

    Ok(())
}

/// Generate trait instances
fn assemble_trait_impls<'tcx, 'rcx>(
    vcx: &mut VerificationCtxt<'tcx, 'rcx>,
) -> Result<(), base::TranslationError<'tcx>> {
    let trait_impl_ids = vcx.env.get_trait_impls();

    for trait_impl_id in trait_impl_ids {
        let did = trait_impl_id.to_def_id();
        let trait_did = vcx.env.tcx().trait_id_of_impl(did).unwrap();

        // check if we registered this impl previously
        if let Some(lit) = vcx.trait_registry.lookup_impl(did) {
            let impl_info = vcx.trait_registry.get_trait_impl_info(did)?;
            let assoc_items: &'tcx ty::AssocItems = vcx.env.tcx().associated_items(did);
            let trait_assoc_items: &'tcx ty::AssocItems = vcx.env.tcx().associated_items(trait_did);
            let subject = vcx.env.tcx().impl_subject(did).skip_binder();
            if let ty::ImplSubject::Trait(trait_ref) = subject {
                let mut methods = HashMap::new();

                // TODO don't rely on definition order
                // maybe instead iterate over the assoc items of the trait

                for x in trait_assoc_items.in_definition_order() {
                    if x.kind == ty::AssocKind::Fn {
                        let fn_item = assoc_items.find_by_name_and_kind(
                            vcx.env.tcx(),
                            x.ident(vcx.env.tcx()),
                            ty::AssocKind::Fn,
                            did,
                        );
                        if let Some(fn_item) = fn_item {
                            if let Some(spec) = vcx.procedure_registry.lookup_function_spec(fn_item.def_id) {
                                methods.insert(x.name.as_str().to_owned(), spec);
                            } else {
                                // TODO should handle this case
                                unreachable!("");
                            }
                        } else {
                            // this is possible for functions with a default impl.
                            // TODO think about that case.
                        }
                    }
                }
                let instance_spec = radium::TraitInstanceSpec::new(methods);

                // assemble the spec and register it
                let spec = radium::TraitImplSpec::new(lit, impl_info, instance_spec);
                vcx.trait_impls.insert(did, spec);
            }
        }
    }
    Ok(())
}

/// Get and parse all module attributes.
pub fn get_module_attributes(env: &Environment<'_>) -> Result<HashMap<LocalDefId, ModuleAttrs>, String> {
    let modules = env.get_modules();
    let mut attrs = HashMap::new();
    info!("collected modules: {:?}", modules);

    for m in &modules {
        let module_attrs = utils::filter_tool_attrs(env.get_attributes(m.to_def_id()));
        let mut module_parser = VerboseModuleAttrParser::new();
        let module_spec = module_parser.parse_module_attrs(*m, &module_attrs)?;
        attrs.insert(*m, module_spec);
    }

    Ok(attrs)
}

/// Find `RefinedRust` modules in the given loadpath.
fn scan_loadpath(path: &Path, storage: &mut HashMap<String, PathBuf>) -> io::Result<()> {
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

/// Find `RefinedRust` modules in the given loadpaths.
fn scan_loadpaths(paths: &[PathBuf]) -> io::Result<HashMap<String, PathBuf>> {
    let mut found_lib_files: HashMap<String, PathBuf> = HashMap::new();

    for path in paths {
        scan_loadpath(path, &mut found_lib_files)?;
    }

    Ok(found_lib_files)
}

/// Translate a crate, creating a `VerificationCtxt` in the process.
pub fn generate_coq_code<'tcx, F>(tcx: ty::TyCtxt<'tcx>, continuation: F) -> Result<(), String>
where
    F: Fn(VerificationCtxt<'tcx, '_>),
{
    let env = Environment::new(tcx);
    let env: &Environment = &*Box::leak(Box::new(env));

    // get crate attributes
    let crate_attrs = tcx.hir().krate_attrs();
    let crate_attrs = utils::filter_tool_attrs(crate_attrs);
    info!("Found crate attributes: {:?}", crate_attrs);
    // parse crate attributes
    let mut crate_parser = VerboseCrateAttrParser::new();
    let crate_spec = crate_parser.parse_crate_attrs(&crate_attrs)?;

    let path_prefix = crate_spec.prefix.unwrap_or_else(|| "refinedrust.examples".to_owned());
    info!("Setting Coq path prefix: {:?}", path_prefix);

    let package = crate_spec.package;
    info!("Setting dune package: {:?}", package);

    // get module attributes
    let module_attrs = get_module_attributes(env)?;

    // process exports
    let mut exports: HashSet<coq::module::Export> = HashSet::new();

    exports.extend(crate_spec.exports);

    for module_attr in module_attrs.values() {
        exports.extend(module_attr.exports.clone());
    }

    info!("Exporting extra Coq files: {:?}", exports);

    // process includes
    let mut includes: HashSet<String> = HashSet::new();
    crate_spec.includes.into_iter().map(|name| includes.insert(name)).count();
    module_attrs
        .into_values()
        .map(|attrs| attrs.includes.into_iter().map(|name| includes.insert(name)).count())
        .count();
    info!("Including RefinedRust modules: {:?}", includes);

    let functions = get_filtered_functions(env);

    let struct_arena = Arena::new();
    let enum_arena = Arena::new();
    let shim_arena = Arena::new();
    let trait_arena = Arena::new();
    let trait_impl_arena = Arena::new();
    let fn_spec_arena = Arena::new();
    let type_translator = TypeTranslator::new(env, &struct_arena, &enum_arena, &shim_arena);
    let trait_registry =
        TraitRegistry::new(env, &type_translator, &trait_arena, &trait_impl_arena, &fn_spec_arena);
    let procedure_registry = ProcedureScope::new();
    let shim_string_arena = Arena::new();
    let mut shim_registry = shim_registry::ShimRegistry::empty(&shim_string_arena);

    // add includes to the shim registry
    let library_load_paths = rrconfig::lib_load_paths();
    info!("Loading libraries from {:?}", library_load_paths);
    let found_libs = scan_loadpaths(&library_load_paths).map_err(|e| e.to_string())?;
    info!("Found the following RefinedRust libraries in the loadpath: {:?}", found_libs);

    for incl in &includes {
        let Some(p) = found_libs.get(incl) else {
            println!("Warning: did not find library {} in loadpath", incl);
            continue;
        };

        let f = File::open(p).map_err(|e| e.to_string())?;
        shim_registry.add_source(f)?;
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
        trait_registry: &trait_registry,
        procedure_registry,
        extra_exports: exports.into_iter().map(|x| (x, false)).collect(),
        extra_dependencies: HashSet::new(),
        coq_path_prefix: path_prefix,
        shim_registry,
        dune_package: package,
        const_registry: ConstScope::empty(),
        trait_impls: HashMap::new(),
        fn_arena: &fn_spec_arena,
    };

    // this needs to be first, in order to ensure consistent ADT use
    register_shims(&mut vcx).map_err(|x| x.to_string())?;

    register_functions(&mut vcx).map_err(|x| x.to_string())?;

    register_traits(&vcx)?;

    register_consts(&mut vcx)?;

    register_trait_impls(&vcx)?;

    translate_functions(&mut vcx);

    // important: happens after all functions have been translated, as this uses the translated
    // function specs
    assemble_trait_impls(&mut vcx).map_err(|x| x.to_string())?;

    continuation(vcx);

    Ok(())
}
