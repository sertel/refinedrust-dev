// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{btree_map, BTreeMap, HashMap, HashSet};
use std::fmt::Write;

use log::{info, trace, warn};
use radium::coq;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir::interpret::{ConstValue, ErrorHandled, Scalar};
use rr_rustc_interface::middle::mir::tcx::PlaceTy;
use rr_rustc_interface::middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, Constant, ConstantKind, Local, LocalKind, Location,
    Mutability, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind, Terminator,
    TerminatorKind, UnOp, VarDebugInfoContents,
};
use rr_rustc_interface::middle::ty::fold::TypeFolder;
use rr_rustc_interface::middle::ty::{ConstKind, Ty, TyKind, TypeFoldable};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, ast, middle};
use typed_arena::Arena;

use crate::arg_folder::*;
use crate::base::*;
use crate::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{dump_borrowck_info, polonius_info, Environment};
use crate::inclusion_tracker::*;
use crate::spec_parsers::parse_utils::ParamLookup;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, FunctionRequirements, FunctionSpecParser, VerboseFunctionSpecParser,
};
use crate::trait_registry::{get_nontrivial_trait_requirements, TraitRegistry};
use crate::type_translator::*;
use crate::tyvars::*;
use crate::{traits, utils};

/// Mangle a name by appending type parameters to it.
pub fn mangle_name_with_tys(method_name: &str, args: &[Ty<'_>]) -> String {
    // TODO: maybe come up with some better way to generate names
    let mut mangled_name = method_name.to_owned();
    for arg in args {
        mangled_name.push_str(format!("_{}", arg).as_str());
    }
    strip_coq_ident(&mangled_name)
}

/// Mangle a name by appending generic args to it.
pub fn mangle_name_with_args(name: &str, args: &[ty::GenericArg<'_>]) -> String {
    let mut mangled_base = name.to_owned();
    for arg in args {
        if let ty::GenericArgKind::Type(ty) = arg.unpack() {
            write!(mangled_base, "_{}", strip_coq_ident(&format!("{ty}"))).unwrap();
        }
    }
    mangled_base
}

/// Get the syntypes of function arguments for a procedure call.
pub fn get_arg_syntypes_for_procedure_call<'tcx, 'def>(
    tcx: ty::TyCtxt<'tcx>,
    ty_translator: &LocalTypeTranslator<'def, 'tcx>,
    callee_did: DefId,
    ty_params: &[ty::GenericArg<'tcx>],
) -> Result<Vec<radium::SynType>, TranslationError<'tcx>> {
    let caller_did = ty_translator.get_proc_did();

    // Get the type of the callee.
    let full_ty: ty::EarlyBinder<Ty<'tcx>> = tcx.type_of(callee_did);
    let full_ty = full_ty.instantiate(tcx, ty_params);

    let mut syntypes = Vec::new();
    match full_ty.kind() {
        ty::TyKind::FnDef(_, _) => {
            let sig = full_ty.fn_sig(tcx);
            for ty in sig.inputs().skip_binder() {
                let st = ty_translator.translate_type_to_syn_type(*ty)?;
                syntypes.push(st);
            }
        },
        ty::TyKind::Closure(_, args) => {
            let clos_args = args.as_closure();
            let sig = clos_args.sig();
            let pre_sig = sig.skip_binder();
            // we also need to add the closure argument here

            let tuple_ty = clos_args.tupled_upvars_ty();
            match clos_args.kind() {
                ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
                    syntypes.push(radium::SynType::Ptr);
                },
                ty::ClosureKind::FnOnce => {
                    let st = ty_translator.translate_type_to_syn_type(tuple_ty)?;
                    syntypes.push(st);
                },
            }
            for ty in pre_sig.inputs() {
                let st = ty_translator.translate_type_to_syn_type(*ty)?;
                syntypes.push(st);
            }
        },
        _ => unimplemented!(),
    }

    Ok(syntypes)
}

/**
 * Tracks the functions we translated and the Coq names they are available under.
 * To account for dependencies between functions, we may register translated names before we have
 * actually translated the function.
 */

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ProcedureMode {
    Prove,
    OnlySpec,
    TrustMe,
    Shim,
    Ignore,
}

impl ProcedureMode {
    pub fn is_prove(self) -> bool {
        self == Self::Prove
    }

    pub fn is_only_spec(self) -> bool {
        self == Self::OnlySpec
    }

    pub fn is_trust_me(self) -> bool {
        self == Self::TrustMe
    }

    pub fn is_shim(self) -> bool {
        self == Self::Shim
    }

    pub fn is_ignore(self) -> bool {
        self == Self::Ignore
    }

    pub fn needs_proof(self) -> bool {
        self == Self::Prove
    }

    pub fn needs_def(self) -> bool {
        self == Self::Prove || self == Self::TrustMe
    }

    pub fn needs_spec(self) -> bool {
        self == Self::Prove || self == Self::TrustMe || self == Self::OnlySpec
    }
}

#[derive(Clone)]
pub struct ProcedureMeta {
    spec_name: String,
    name: String,
    mode: ProcedureMode,
}

impl ProcedureMeta {
    pub const fn new(spec_name: String, name: String, mode: ProcedureMode) -> Self {
        Self {
            spec_name,
            name,
            mode,
        }
    }

    pub fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub const fn get_mode(&self) -> ProcedureMode {
        self.mode
    }
}

pub struct ProcedureScope<'def> {
    /// maps the defid to (code_name, spec_name, name)
    name_map: BTreeMap<DefId, ProcedureMeta>,
    /// track the actually translated functions
    translated_functions: BTreeMap<DefId, radium::Function<'def>>,
    /// track the functions with just a specification (rr::only_spec)
    specced_functions: BTreeMap<DefId, &'def radium::FunctionSpec<radium::InnerFunctionSpec<'def>>>,
}

impl<'def> ProcedureScope<'def> {
    pub fn new() -> Self {
        Self {
            name_map: BTreeMap::new(),
            translated_functions: BTreeMap::new(),
            specced_functions: BTreeMap::new(),
        }
    }

    /// Lookup the meta information of a function.
    pub fn lookup_function(&self, did: DefId) -> Option<ProcedureMeta> {
        self.name_map.get(&did).cloned()
    }

    /// Lookup a translated function spec
    pub fn lookup_function_spec(
        &self,
        did: DefId,
    ) -> Option<&'def radium::FunctionSpec<radium::InnerFunctionSpec<'def>>> {
        if let Some(translated_fn) = self.translated_functions.get(&did) {
            Some(translated_fn.spec)
        } else if let Some(translated_spec) = self.specced_functions.get(&did) {
            Some(translated_spec)
        } else {
            None
        }
    }

    /// Lookup the Coq spec name for a function.
    pub fn lookup_function_spec_name(&self, did: DefId) -> Option<&str> {
        self.name_map.get(&did).map(ProcedureMeta::get_spec_name)
    }

    /// Lookup the name for a function.
    pub fn lookup_function_mangled_name(&self, did: DefId) -> Option<&str> {
        self.name_map.get(&did).map(ProcedureMeta::get_name)
    }

    /// Lookup the mode for a function.
    pub fn lookup_function_mode(&self, did: DefId) -> Option<ProcedureMode> {
        self.name_map.get(&did).map(ProcedureMeta::get_mode)
    }

    /// Register a function.
    pub fn register_function<'tcx>(
        &mut self,
        did: DefId,
        meta: ProcedureMeta,
    ) -> Result<(), TranslationError<'tcx>> {
        if self.name_map.insert(did, meta).is_some() {
            Err(TranslationError::ProcedureRegistry(format!(
                "function for defid {:?} has already been registered",
                did
            )))
        } else {
            Ok(())
        }
    }

    /// Provide the code for a translated function.
    pub fn provide_translated_function(&mut self, did: DefId, trf: radium::Function<'def>) {
        let meta = &self.name_map[&did];
        assert!(meta.get_mode().needs_def());
        assert!(self.translated_functions.insert(did, trf).is_none());
    }

    /// Provide the specification for an `only_spec` function.
    pub fn provide_specced_function(
        &mut self,
        did: DefId,
        spec: &'def radium::FunctionSpec<radium::InnerFunctionSpec<'def>>,
    ) {
        let meta = &self.name_map[&did];
        assert!(meta.get_mode().is_only_spec());
        assert!(self.specced_functions.insert(did, spec).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub fn iter_code(&self) -> btree_map::Iter<'_, DefId, radium::Function<'def>> {
        self.translated_functions.iter()
    }

    /// Iterate over the functions we have generated only specs for.
    pub fn iter_only_spec(
        &self,
    ) -> btree_map::Iter<'_, DefId, &'def radium::FunctionSpec<radium::InnerFunctionSpec<'def>>> {
        self.specced_functions.iter()
    }
}

/// Scope of consts that are available
pub struct ConstScope<'def> {
    // statics are explicitly declared
    statics: HashMap<DefId, radium::StaticMeta<'def>>,
    // const places are constants that lie in a static memory segment because they are referred to
    // by-ref
    const_places: HashMap<DefId, radium::ConstPlaceMeta<'def>>,
}

impl<'def> ConstScope<'def> {
    /// Create a new const scope.
    pub fn empty() -> Self {
        Self {
            statics: HashMap::new(),
            const_places: HashMap::new(),
        }
    }

    /// Register a static
    pub fn register_static(&mut self, did: DefId, meta: radium::StaticMeta<'def>) {
        self.statics.insert(did, meta);
    }

    /// Register a const place
    pub fn register_const_place(&mut self, did: DefId, meta: radium::ConstPlaceMeta<'def>) {
        self.const_places.insert(did, meta);
    }
}

// solve the constraints for the new_regions
// we first identify what kinds of constraints these new regions are subject to
#[derive(Debug)]
enum CallRegionKind {
    // this is just an intersection of local regions.
    Intersection(HashSet<Region>),
    // this is equal to a specific region
    EqR(Region),
}

struct CallRegions {
    pub early_regions: Vec<Region>,
    pub late_regions: Vec<Region>,
    pub classification: HashMap<Region, CallRegionKind>,
}

/// Information we compute when calling a function from another function.
/// Determines how to specialize the callee's generics in our spec assumption.
struct AbstractedGenerics<'def> {
    /// the scope with new generics to quantify over for the function's specialized spec
    scope: radium::GenericScope,
    /// instantiations for the specialized spec hint
    callee_lft_param_inst: Vec<radium::Lft>,
    callee_ty_param_inst: Vec<radium::Type<'def>>,
    /// instantiations for the function use
    fn_lft_param_inst: Vec<radium::Lft>,
    fn_ty_param_inst: Vec<radium::Type<'def>>,
}

/// A scope of trait attributes mapping to Coq names to be used in a function's spec
struct TraitSpecNameScope {
    attrs: HashMap<String, String>,
}

/// When translating a function spec where attributes of a trait are in scope,
/// we create a wrapper to lookup references to the trait's attributes when parsing function specs.
struct FunctionSpecScope<'a, T> {
    generics: &'a T,
    attrs: &'a TraitSpecNameScope,
}
impl<'a, T: ParamLookup> ParamLookup for FunctionSpecScope<'a, T> {
    fn lookup_ty_param(&self, path: &[&str]) -> Option<&radium::LiteralTyParam> {
        self.generics.lookup_ty_param(path)
    }

    fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
        self.generics.lookup_lft(lft)
    }

    fn lookup_literal(&self, path: &[&str]) -> Option<&str> {
        if path.len() == 1 {
            if let Some(lit) = self.attrs.attrs.get(path[0]) {
                return Some(lit);
            }
        }
        self.generics.lookup_literal(path)
    }
}

pub struct FunctionTranslator<'a, 'def, 'tcx> {
    env: &'def Environment<'tcx>,
    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// the Caesium function buildder
    translated_fn: radium::FunctionBuilder<'def>,
    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a ProcedureScope<'def>,
    /// registry of consts
    const_registry: &'a ConstScope<'def>,
    /// attributes on this function
    attrs: &'a [&'a ast::ast::AttrItem],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// translator for types
    ty_translator: LocalTypeTranslator<'def, 'tcx>,
    /// trait registry in the current scope
    trait_registry: &'def TraitRegistry<'tcx, 'def>,
    /// argument types (from the signature, with generics substituted)
    inputs: Vec<Ty<'tcx>>,
}

impl<'a, 'def: 'a, 'tcx: 'def> FunctionTranslator<'a, 'def, 'tcx> {
    /// Generate a spec for a trait method.
    pub fn spec_for_trait_method(
        env: &'def Environment<'tcx>,
        proc_did: DefId,
        name: &str,
        spec_name: &str,
        attrs: &'a [&'a ast::ast::AttrItem],
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        trait_registry: &'def TraitRegistry<'tcx, 'def>,
    ) -> Result<radium::FunctionSpec<radium::InnerFunctionSpec<'def>>, TranslationError<'tcx>> {
        let mut translated_fn = radium::FunctionBuilder::new(name, spec_name);

        let ty: ty::EarlyBinder<Ty<'tcx>> = env.tcx().type_of(proc_did);
        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        let sig = match ty.kind() {
            TyKind::FnDef(_def, _args) => {
                assert!(ty.is_fn());
                let sig = ty.fn_sig(env.tcx());
                sig
            },
            _ => panic!("can not handle non-fns"),
        };
        info!("Function signature: {:?}", sig);

        let params = Self::get_proc_ty_params(env.tcx(), proc_did);
        info!("Function generic args: {:?}", params);

        let (inputs, output, region_substitution) = Self::process_lifetimes_of_args(env, params, sig);
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let (type_scope, trait_attrs) = Self::setup_local_scope(
            env,
            ty_translator,
            trait_registry,
            proc_did,
            params.as_slice(),
            &mut translated_fn,
            region_substitution,
            false,
            None,
        )?;
        let type_translator = LocalTypeTranslator::new(ty_translator, type_scope);

        // TODO: add universal constraints (ideally in setup_local_scope)

        let spec_builder = Self::process_attrs(
            attrs,
            &type_translator,
            &mut translated_fn,
            &trait_attrs,
            inputs.as_slice(),
            output,
        )?;
        translated_fn.add_function_spec_from_builder(spec_builder);

        translated_fn.try_into().map_err(TranslationError::AttributeError)
    }

    /// Create a translation instance for a closure.
    pub fn new_closure(
        env: &'def Environment<'tcx>,
        meta: &ProcedureMeta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a ast::ast::AttrItem],
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        trait_registry: &'def TraitRegistry<'tcx, 'def>,
        proc_registry: &'a ProcedureScope<'def>,
        const_registry: &'a ConstScope<'def>,
    ) -> Result<Self, TranslationError<'tcx>> {
        let mut translated_fn = radium::FunctionBuilder::new(&meta.name, &meta.spec_name);

        // TODO can we avoid the leak
        let proc: &'def Procedure = &*Box::leak(Box::new(proc));
        let body = proc.get_mir();
        Self::dump_body(body);

        let ty: ty::EarlyBinder<Ty<'tcx>> = env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();
        let closure_kind = match ty.kind() {
            TyKind::Closure(_def, closure_args) => {
                assert!(ty.is_closure());
                let clos = closure_args.as_closure();
                clos.kind()
            },
            _ => panic!("can not handle non-closures"),
        };

        let local_decls = &body.local_decls;
        let closure_arg = local_decls.get(Local::from_usize(1)).unwrap();
        let closure_ty;

        match closure_kind {
            ty::ClosureKind::Fn => {
                if let ty::TyKind::Ref(_, ty, _) = closure_arg.ty.kind() {
                    closure_ty = ty;
                } else {
                    unreachable!();
                }
            },
            ty::ClosureKind::FnMut => {
                if let ty::TyKind::Ref(_, ty, _) = closure_arg.ty.kind() {
                    closure_ty = ty;
                } else {
                    unreachable!("unexpected type {:?}", closure_arg.ty);
                }
            },
            ty::ClosureKind::FnOnce => {
                closure_ty = &closure_arg.ty;
            },
        }

        let parent_args;
        let mut capture_regions = Vec::new();
        let sig;
        let captures;
        let upvars_tys;
        if let ty::TyKind::Closure(did, closure_args) = closure_ty.kind() {
            let clos = closure_args.as_closure();

            let tupled_upvars_tys = clos.tupled_upvars_ty();
            upvars_tys = clos.upvar_tys();
            parent_args = clos.parent_args();
            let unnormalized_sig = clos.sig();
            sig = unnormalized_sig;
            info!("closure sig: {:?}", sig);

            captures = env.tcx().closure_captures(did.as_local().unwrap());
            info!("Closure has captures: {:?}", captures);

            // find additional lifetime parameters
            for (place, ty) in captures.iter().zip(clos.upvar_tys().iter()) {
                if place.region.is_some() {
                    // find region from ty
                    if let ty::TyKind::Ref(region, _, _) = ty.kind() {
                        capture_regions.push(*region);
                    }
                }
            }
            info!("Closure capture regions: {:?}", capture_regions);

            info!("Closure arg upvar_tys: {:?}", tupled_upvars_tys);
            info!("Function signature: {:?}", sig);
            info!("Closure generic args: {:?}", parent_args);
        } else {
            unreachable!();
        }

        match PoloniusInfo::new(env, proc) {
            Ok(info) => {
                // TODO: avoid leak
                let info: &'def PoloniusInfo = &*Box::leak(Box::new(info));

                // For closures, we only handle the parent's args here!
                // TODO: do we need to do something special for the parent's late-bound region
                // parameters?
                // TODO: should we always take the lifetime parameters?
                let params = parent_args;
                //proc.get_type_params();
                info!("Function generic args: {:?}", params);

                // dump graphviz files
                // color code: red: dying loan, pink: becoming a zombie; green: is zombie
                if rrconfig::dump_borrowck_info() {
                    dump_borrowck_info(env, proc.get_id(), info);
                }

                let (tupled_inputs, output, mut region_substitution) =
                    Self::process_lifetimes_of_args(env, params, sig);

                // Process the lifetime parameters that come from the captures
                for r in capture_regions {
                    // TODO: problem: we're introducing inconsistent names here.
                    if let ty::RegionKind::ReVar(r) = r.kind() {
                        let lft = info.mk_atomic_region(r);
                        let name = format_atomic_region_direct(&lft, None);
                        region_substitution.region_names.insert(r, name);
                        // TODO: add to region_substitution?
                    } else {
                        unreachable!();
                    }
                }
                // also add the lifetime for the outer reference
                let mut maybe_outer_lifetime = None;
                if let ty::TyKind::Ref(r, _, _) = closure_arg.ty.kind() {
                    if let ty::RegionKind::ReVar(r) = r.kind() {
                        // We need to do some hacks here to find the right Polonius region:
                        // `r` is the non-placeholder region that the variable gets, but we are
                        // looking for the corresponding placeholder region
                        let r2 = Self::find_placeholder_region_for(r, info).unwrap();

                        info!("using lifetime {:?} for closure universal", r2);
                        let lft = info.mk_atomic_region(r2);
                        let name = format_atomic_region_direct(&lft, None);
                        region_substitution.region_names.insert(r2, name);

                        maybe_outer_lifetime = Some(r2);
                    } else {
                        unreachable!();
                    }
                }

                // detuple the inputs
                assert!(tupled_inputs.len() == 1);
                let input_tuple_ty = tupled_inputs[0];
                let mut inputs = Vec::new();

                // push the closure as the first argument
                /*
                if let Some(r2) = maybe_outer_lifetime {
                    // in this case, we need to patch the region first
                    if let ty::TyKind::Ref(_, ty, m) = closure_arg.ty.kind() {
                        let new_region = ty::Region::new_var(env.tcx(), r2);
                        inputs.push(env.tcx().mk_ty_from_kind(ty::TyKind::Ref(new_region, *ty, *m)));
                    }
                }
                else {
                    inputs.push(closure_arg.ty);
                }
                */

                if let ty::TyKind::Tuple(args) = input_tuple_ty.kind() {
                    inputs.extend(args.iter());
                }

                info!("inputs({}): {:?}, output: {:?}", inputs.len(), inputs, output);

                let mut inclusion_tracker = InclusionTracker::new(info);
                // add placeholder subsets
                let initial_point: facts::Point = facts::Point {
                    location: BasicBlock::from_u32(0).start_location(),
                    typ: facts::PointType::Start,
                };
                for (r1, r2) in &info.borrowck_in_facts.known_placeholder_subset {
                    inclusion_tracker.add_static_inclusion(
                        *r1,
                        *r2,
                        info.interner.get_point_index(&initial_point),
                    );
                }

                let (type_scope, trait_attrs) = Self::setup_local_scope(
                    env,
                    ty_translator,
                    trait_registry,
                    proc.get_id(),
                    params,
                    &mut translated_fn,
                    region_substitution,
                    true,
                    Some(info),
                )?;
                let type_translator = LocalTypeTranslator::new(ty_translator, type_scope);

                let mut t = Self {
                    env,
                    proc,
                    info,
                    translated_fn,
                    inclusion_tracker,
                    procedure_registry: proc_registry,
                    attrs,
                    ty_translator: type_translator,
                    trait_registry,
                    const_registry,
                    inputs: inputs.clone(),
                };

                // compute meta information needed to generate the spec
                let mut translated_upvars_types = Vec::new();
                for ty in upvars_tys {
                    let translated_ty = t.ty_translator.translate_type(ty)?;
                    translated_upvars_types.push(translated_ty);
                }
                let meta;
                {
                    let scope = t.ty_translator.scope.borrow();
                    meta = ClosureMetaInfo {
                        kind: closure_kind,
                        captures,
                        capture_tys: &translated_upvars_types,
                        closure_lifetime: maybe_outer_lifetime
                            .map(|x| scope.lifetime_scope.lookup_region(x).unwrap().to_owned()),
                    };
                }

                // process attributes
                t.process_closure_attrs(&trait_attrs, &inputs, output, meta)?;
                Ok(t)
            },
            Err(err) => Err(TranslationError::UnknownError(format!("{:?}", err))),
        }
    }

    /// Translate the body of a function.
    pub fn new(
        env: &'def Environment<'tcx>,
        meta: &ProcedureMeta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a ast::ast::AttrItem],
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        trait_registry: &'def TraitRegistry<'tcx, 'def>,
        proc_registry: &'a ProcedureScope<'def>,
        const_registry: &'a ConstScope<'def>,
    ) -> Result<Self, TranslationError<'tcx>> {
        let mut translated_fn = radium::FunctionBuilder::new(&meta.name, &meta.spec_name);

        // TODO can we avoid the leak
        let proc: &'def Procedure = &*Box::leak(Box::new(proc));

        let body = proc.get_mir();
        Self::dump_body(body);

        let ty: ty::EarlyBinder<Ty<'tcx>> = env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        let sig = match ty.kind() {
            TyKind::FnDef(_def, _args) => {
                assert!(ty.is_fn());
                let sig = ty.fn_sig(env.tcx());
                sig
            },
            _ => panic!("can not handle non-fns"),
        };

        info!("Function signature: {:?}", sig);

        match PoloniusInfo::new(env, proc) {
            Ok(info) => {
                // TODO: avoid leak
                let info: &'def PoloniusInfo = &*Box::leak(Box::new(info));

                let params = Self::get_proc_ty_params(env.tcx(), proc.get_id());
                info!("Function generic args: {:?}", params);

                // dump graphviz files
                // color code: red: dying loan, pink: becoming a zombie; green: is zombie
                if rrconfig::dump_borrowck_info() {
                    dump_borrowck_info(env, proc.get_id(), info);
                }

                let (inputs, output, region_substitution) = Self::process_lifetimes_of_args(env, params, sig);
                info!("inputs: {:?}, output: {:?}", inputs, output);

                let mut inclusion_tracker = InclusionTracker::new(info);
                // add placeholder subsets
                let initial_point: facts::Point = facts::Point {
                    location: BasicBlock::from_u32(0).start_location(),
                    typ: facts::PointType::Start,
                };
                for (r1, r2) in &info.borrowck_in_facts.known_placeholder_subset {
                    inclusion_tracker.add_static_inclusion(
                        *r1,
                        *r2,
                        info.interner.get_point_index(&initial_point),
                    );
                }

                let (type_scope, trait_attrs) = Self::setup_local_scope(
                    env,
                    ty_translator,
                    trait_registry,
                    proc.get_id(),
                    params.as_slice(),
                    &mut translated_fn,
                    region_substitution,
                    true,
                    Some(info),
                )?;
                let type_translator = LocalTypeTranslator::new(ty_translator, type_scope);

                // process attributes
                let mut spec_builder = Self::process_attrs(
                    attrs,
                    &type_translator,
                    &mut translated_fn,
                    &trait_attrs,
                    inputs.as_slice(),
                    output,
                )?;

                let mut t = Self {
                    env,
                    proc,
                    info,
                    translated_fn,
                    inclusion_tracker,
                    procedure_registry: proc_registry,
                    attrs,
                    ty_translator: type_translator,
                    trait_registry,
                    const_registry,
                    inputs: inputs.clone(),
                };

                if spec_builder.has_spec() {
                    // add universal constraints
                    let universal_constraints = t.get_relevant_universal_constraints();
                    info!("univeral constraints: {:?}", universal_constraints);
                    for (lft1, lft2) in universal_constraints {
                        spec_builder.add_lifetime_constraint(lft1, lft2);
                    }

                    t.translated_fn.add_function_spec_from_builder(spec_builder);
                } else {
                    let spec = t.make_trait_instance_spec()?;
                    if let Some(spec) = spec {
                        t.translated_fn.add_trait_function_spec(spec);
                    } else {
                        return Err(TranslationError::AttributeError(
                            "No valid specification provided".to_owned(),
                        ));
                    }
                }

                Ok(t)
            },
            Err(err) => Err(TranslationError::UnknownError(format!("{:?}", err))),
        }
    }

    pub fn translate(
        mut self,
        spec_arena: &'def Arena<radium::FunctionSpec<radium::InnerFunctionSpec<'def>>>,
    ) -> Result<radium::Function<'def>, TranslationError<'tcx>> {
        let body = self.proc.get_mir();

        // analyze which locals are used for the result of checked-ops, because we will
        // override their types (eliminating the tuples)
        let mut checked_op_analyzer = CheckedOpLocalAnalysis::new(self.env.tcx(), body);
        checked_op_analyzer.analyze();
        let checked_op_locals = checked_op_analyzer.results();

        // map to translate between locals and the string names we use in radium::
        let mut radium_name_map: HashMap<Local, String> = HashMap::new();

        let local_decls = &body.local_decls;
        info!("Have {} local decls\n", local_decls.len());

        let debug_info = &body.var_debug_info;
        info!("using debug info: {:?}", debug_info);

        let mut return_synty = radium::SynType::Unit; // default
        let mut fn_locals = Vec::new();
        let mut opt_return_name =
            Err(TranslationError::UnknownError("could not find local for return value".to_owned()));
        let mut used_names = HashSet::new();
        let mut arg_tys = Vec::new();

        // go over local_decls and create the right radium:: stack layout
        for (local, local_decl) in local_decls.iter_enumerated() {
            let kind = body.local_kind(local);
            let ty: Ty<'tcx>;
            if let Some(rewritten_ty) = checked_op_locals.get(&local) {
                ty = *rewritten_ty;
            } else {
                ty = local_decl.ty;
            }

            // check if the type is of a spec fn -- in this case, we can skip this temporary
            if let TyKind::Closure(id, _) = ty.kind() {
                if self.procedure_registry.lookup_function_mode(*id).map_or(false, ProcedureMode::is_ignore) {
                    // this is a spec fn
                    info!("skipping local which has specfn closure type: {:?}", local);
                    continue;
                }
            }

            // type:
            info!("Trying to translate type of local {local:?}: {:?}", ty);
            let tr_ty = self.ty_translator.translate_type(ty)?;
            let st = (&tr_ty).into();

            let name = Self::make_local_name(body, local, &mut used_names);
            radium_name_map.insert(local, name.clone());

            fn_locals.push((local, name.clone(), tr_ty));

            match kind {
                LocalKind::Arg => {
                    self.translated_fn.code.add_argument(&name, st);
                    arg_tys.push(ty);
                },
                //LocalKind::Var => translated_fn.code.add_local(&name, st),
                LocalKind::Temp => self.translated_fn.code.add_local(&name, st),
                LocalKind::ReturnPointer => {
                    return_synty = st.clone();
                    self.translated_fn.code.add_local(&name, st);
                    opt_return_name = Ok(name);
                },
            }
        }
        info!("radium name map: {:?}", radium_name_map);
        // create the function
        let return_name = opt_return_name?;

        // add lifetime parameters to the map
        let inputs2 = self.inputs.clone();
        let initial_constraints =
            self.get_initial_universal_arg_constraints(inputs2.as_slice(), arg_tys.as_slice());
        info!("initial constraints: {:?}", initial_constraints);

        let translator = BodyTranslator {
            env: self.env,
            proc: self.proc,
            info: self.info,
            variable_map: radium_name_map,
            translated_fn: self.translated_fn,
            return_name,
            return_synty,
            inclusion_tracker: self.inclusion_tracker,
            collected_procedures: HashMap::new(),
            procedure_registry: self.procedure_registry,
            attrs: self.attrs,
            local_lifetimes: Vec::new(),
            bb_queue: Vec::new(),
            processed_bbs: HashSet::new(),
            ty_translator: self.ty_translator,
            loop_specs: HashMap::new(),
            fn_locals,
            checked_op_temporaries: checked_op_locals,
            const_registry: self.const_registry,
            trait_registry: self.trait_registry,
            collected_statics: HashSet::new(),
        };
        translator.translate(initial_constraints, spec_arena)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> FunctionTranslator<'a, 'def, 'tcx> {
    /// Get type parameters of the given procedure.
    fn get_proc_ty_params(tcx: ty::TyCtxt<'tcx>, did: DefId) -> ty::GenericArgsRef<'tcx> {
        let ty = tcx.type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::FnDef(_, params) => params,
            ty::TyKind::Closure(_, closure_args) => {
                assert!(ty.is_closure());
                let clos = closure_args.as_closure();
                let parent_args = clos.parent_args();

                // TODO: this doesn't include lifetime parameters specific to this closure...
                tcx.mk_args(parent_args)
            },
            _ => panic!("Procedure::new called on a procedure whose type is not TyKind::FnDef!"),
        }
    }

    fn process_lifetimes_of_args(
        env: &Environment<'tcx>,
        params: &[ty::GenericArg<'tcx>],
        sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
    ) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap) {
        // a mapping of Polonius region IDs to names
        let mut universal_lifetimes = BTreeMap::new();
        let mut lifetime_names = HashMap::new();

        let mut region_substitution_early: Vec<Option<ty::RegionVid>> = Vec::new();

        // we create a substitution that replaces early bound regions with their Polonius
        // region variables
        let mut subst_early_bounds: Vec<ty::GenericArg<'tcx>> = Vec::new();
        let mut num_early_bounds = 0;
        for a in params {
            if let ty::GenericArgKind::Lifetime(r) = a.unpack() {
                // skip over 0 = static
                let next_id = ty::RegionVid::from_u32(num_early_bounds + 1);
                let revar = ty::Region::new_var(env.tcx(), next_id);
                num_early_bounds += 1;
                subst_early_bounds.push(ty::GenericArg::from(revar));

                region_substitution_early.push(Some(next_id));

                match *r {
                    ty::RegionKind::ReEarlyBound(r) => {
                        let name = strip_coq_ident(r.name.as_str());
                        universal_lifetimes.insert(next_id, format!("ulft_{}", name));
                        lifetime_names.insert(name, next_id);
                    },
                    _ => {
                        universal_lifetimes.insert(next_id, format!("ulft_{}", num_early_bounds));
                    },
                }
            } else {
                subst_early_bounds.push(*a);
                region_substitution_early.push(None);
            }
        }
        let subst_early_bounds = env.tcx().mk_args(&subst_early_bounds);

        info!("Computed early region map {region_substitution_early:?}");

        // add names for late bound region variables
        let mut num_late_bounds = 0;
        let mut region_substitution_late = Vec::new();
        for b in sig.bound_vars() {
            let next_id = ty::RegionVid::from_u32(num_early_bounds + num_late_bounds + 1);

            let ty::BoundVariableKind::Region(r) = b else {
                continue;
            };

            region_substitution_late.push(next_id);

            match r {
                ty::BoundRegionKind::BrNamed(_, sym) => {
                    let mut region_name = strip_coq_ident(sym.as_str());
                    if region_name == "_" {
                        region_name = next_id.as_usize().to_string();
                        universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                    } else {
                        universal_lifetimes.insert(next_id, format!("ulft_{}", region_name));
                        lifetime_names.insert(region_name, next_id);
                    }
                },
                ty::BoundRegionKind::BrAnon(_) => {
                    universal_lifetimes.insert(next_id, format!("ulft_{}", next_id.as_usize()));
                },
                _ => (),
            }

            num_late_bounds += 1;
        }

        // replace late-bound region variables by re-enumerating them in the same way as the MIR
        // type checker does (that this happens in the same way is important to make the names
        // line up!)
        let mut next_index = num_early_bounds + 1; // skip over one additional due to static
        let mut folder = |_| {
            let cur_index = next_index;
            next_index += 1;
            ty::Region::new_var(env.tcx(), ty::RegionVid::from_u32(cur_index))
        };
        let (late_sig, _late_region_map) = env.tcx().replace_late_bound_regions(sig, &mut folder);

        // replace early bound variables
        let inputs: Vec<_> = late_sig
            .inputs()
            .iter()
            .map(|ty| ty_instantiate(*ty, env.tcx(), subst_early_bounds))
            .collect();

        let output = ty_instantiate(late_sig.output(), env.tcx(), subst_early_bounds);

        info!("Computed late region map {region_substitution_late:?}");

        let region_map = EarlyLateRegionMap::new(
            region_substitution_early,
            region_substitution_late,
            universal_lifetimes,
            lifetime_names,
        );
        (inputs, output, region_map)
    }

    /// At the start of the function, there's a universal (placeholder) region for reference argument.
    /// These get subsequently relabeled.
    /// Given the relabeled region, find the original placeholder region.
    fn find_placeholder_region_for(r: ty::RegionVid, info: &PoloniusInfo) -> Option<ty::RegionVid> {
        let root_location = Location {
            block: BasicBlock::from_u32(0),
            statement_index: 0,
        };
        let root_point = info.interner.get_point_index(&facts::Point {
            location: root_location,
            typ: facts::PointType::Start,
        });

        for (r1, r2, p) in &info.borrowck_in_facts.subset_base {
            if *p == root_point && *r2 == r {
                info!("find placeholder region for: {:?} ⊑ {:?} = r = {:?}", r1, r2, r);
                return Some(*r1);
            }
        }
        None
    }

    /// Set up the local generic scope of the function, including type parameters, lifetime
    /// parameters, and trait constraints.
    fn setup_local_scope(
        env: &Environment<'tcx>,
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        trait_registry: &'def TraitRegistry<'tcx, 'def>,
        proc_did: DefId,
        params: &[ty::GenericArg<'tcx>],
        translated_fn: &mut radium::FunctionBuilder<'def>,
        region_substitution: EarlyLateRegionMap,
        add_trait_specs: bool,
        info: Option<&'def PoloniusInfo<'def, 'tcx>>,
    ) -> Result<(TypeTranslationScope<'tcx, 'def>, TraitSpecNameScope), TranslationError<'tcx>> {
        // add universals to the function
        // important: these need to be in the right order!
        for (vid, name) in &region_substitution.region_names {
            translated_fn.add_universal_lifetime(name.to_owned());
        }

        // enter the procedure
        let param_env: ty::ParamEnv<'tcx> = env.tcx().param_env(proc_did);
        let type_scope = TypeTranslationScope::new_with_traits(
            proc_did,
            env,
            env.tcx().mk_args(params),
            region_substitution,
            param_env,
            ty_translator,
            trait_registry,
            info,
        )?;

        // add generic args to the fn
        let generics = &type_scope.generic_scope;
        for t in generics.iter().flatten() {
            translated_fn.add_ty_param(t.clone());
        }

        // add associated types of generics to the fn as type parameters
        let assoc_tys = type_scope.get_associated_type_literals(env);
        for t in assoc_tys {
            translated_fn.add_ty_param(t);
        }

        // add specs for traits of generics
        if add_trait_specs {
            let trait_uses = type_scope.get_trait_uses();
            for ((did, params), trait_use) in trait_uses {
                if trait_use.trait_use.is_used_in_self_trait {
                    continue;
                }
                translated_fn.add_trait_requirement(trait_use.trait_use.clone());
            }
        }

        // In our case, we are in a trait impl declaration, right?

        // check if we are in the implementation of a trait or trait impl
        let mut trait_attr_map = HashMap::new();
        if let Some(trait_did) = env.tcx().trait_of_item(proc_did) {
            // we are in a trait declaration
            if let Some(trait_ref) = trait_registry.lookup_trait(trait_did) {
                // make the parameter for the attrs that the function is parametric over
                let param_name = trait_ref.make_fnspec_attr_param_name();

                // we need to apply it to the trait's type parameters and associated types which should be in
                // scope here
                let trait_generics = env.tcx().generics_of(trait_did);
                let param_scope = ParamScope::from(trait_generics.params.as_slice());
                let generics_scope: radium::GenericScope = param_scope.into();

                let assoc_tys = type_scope
                    .get_self_trait_assoc_types(env)
                    .expect("There should be a Self trait use within a trait declaration");

                let mut param_ty_args = Vec::new();
                for ty in generics_scope.get_ty_params() {
                    param_ty_args.push(ty.refinement_type.clone());
                }
                for ty in &assoc_tys {
                    param_ty_args.push(format!("{}", ty.get_rfn_type()));
                }
                let param_ty =
                    format!("{}", coq::term::App::new(trait_ref.spec_attrs_record.clone(), param_ty_args));
                let param =
                    coq::binder::Binder::new(Some(param_name.clone()), coq::term::Type::Literal(param_ty));

                // add it as a parameter to the function after the generics
                translated_fn.add_late_coq_param(param);

                // add the corresponding record entries to the map
                for attr in &trait_ref.declared_attrs {
                    let record_item = trait_ref.make_spec_attr_name(attr);
                    trait_attr_map.insert(attr.to_owned(), format!("{param_name}.({record_item})"));
                }
            }
        }
        if let Some(impl_did) = env.tcx().impl_of_method(proc_did) {
            if let Some(trait_did) = env.tcx().trait_id_of_impl(impl_did) {
                // we are in a trait impl
                if let Some(trait_ref) = trait_registry.lookup_trait(trait_did) {
                    /*
                    // We can get the info here because it's in the current crate
                    let impl_ref = trait_registry.get_trait_impl_info(impl_did)?;

                    // make the parameter for the attrs that the function is parametric over
                    let param_name = trait_ref.make_fnspec_attr_param_name();
                    // we need to apply it to the trait's parameters in this impl
                    let mut param_ty_args = Vec::new();
                    for ty in impl_ref.get_trait_param_inst().iter().chain(impl_ref.get_trait_assoc_inst()) {
                        param_ty_args.push(format!("{}", ty.get_rfn_type()));
                    }
                    let param_ty = format!("{}", radium::coq::App::new(trait_ref.spec_attrs_record.clone(), param_ty_args));
                    let param = radium::coq::Param::new(radium::coq::Name::Named(param_name.clone()), radium::coq::Type::Literal(param_ty), false);

                    // add it as parameter to the function after the generics
                    translated_fn.add_late_coq_param(param);

                    // add the corresponding record entries to the map
                    for attr in &trait_ref.declared_attrs {
                        let record_item = trait_ref.make_spec_attr_name(attr);
                        trait_attr_map.insert(attr.to_owned(), format!("{param_name}.({record_item})"));
                    }
                    */

                    // Now we should not add this parameter anymore. But when

                    let attrs = trait_registry.get_impl_attrs_term(impl_did)?;
                    // add the corresponding record entries to the map
                    for attr in &trait_ref.declared_attrs {
                        let record_item = trait_ref.make_spec_attr_name(attr);
                        trait_attr_map.insert(attr.to_owned(), format!("({attrs}).({record_item})"));
                    }
                }
            }
        }
        let trait_scope = TraitSpecNameScope {
            attrs: trait_attr_map,
        };

        // TODO: can we also setup the lifetime constraints here?
        // TODO: understand better how these clauses relate to Polonius
        // Note: these constraints do not seem to include implied bounds.
        /*
        let clauses = param_env.caller_bounds();
        info!("looking for outlives clauses");
        for cl in clauses.iter() {
            let cl_kind = cl.kind();
            let cl_kind = cl_kind.skip_binder();

            // only look for trait predicates for now
            if let ty::ClauseKind::RegionOutlives(region_pred) = cl_kind {
                info!("region outlives: {:?} {:?}", region_pred.0, region_pred.1);
            }
            if let ty::ClauseKind::TypeOutlives(outlives_pred) = cl_kind {
                info!("type outlives: {:?} {:?}", outlives_pred.0, outlives_pred.1);
            }
        }
        */

        Ok((type_scope, trait_scope))
    }

    /// Filter the "interesting" constraints between universal lifetimes that need to hold
    /// (this does not include the constraints that need to hold for all universal lifetimes,
    /// e.g. that they outlive the function lifetime and are outlived by 'static).
    fn get_relevant_universal_constraints(&mut self) -> Vec<(radium::UniversalLft, radium::UniversalLft)> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let placeholder_subset = &input_facts.known_placeholder_subset;

        let root_location = Location {
            block: BasicBlock::from_u32(0),
            statement_index: 0,
        };
        let root_point = self.info.interner.get_point_index(&facts::Point {
            location: root_location,
            typ: facts::PointType::Start,
        });

        let mut universal_constraints = Vec::new();

        for (r1, r2) in placeholder_subset {
            if let polonius_info::RegionKind::Universal(uk1) = info.get_region_kind(*r1) {
                if let polonius_info::RegionKind::Universal(uk2) = info.get_region_kind(*r2) {
                    // if LHS is static, ignore.
                    if uk1 == polonius_info::UniversalRegionKind::Static {
                        continue;
                    }
                    // if RHS is the function lifetime, ignore
                    if uk2 == polonius_info::UniversalRegionKind::Function {
                        continue;
                    }

                    let to_universal = || {
                        let x = self.to_universal_lft(uk1, *r2)?;
                        let y = self.to_universal_lft(uk2, *r1)?;
                        Some((x, y))
                    };
                    // else, add this constraint
                    // for the purpose of this analysis, it is fine to treat it as a dynamic inclusion
                    if let Some((x, y)) = to_universal() {
                        self.inclusion_tracker.add_dynamic_inclusion(*r1, *r2, root_point);
                        universal_constraints.push((x, y));
                    };
                }
            }
        }
        universal_constraints
    }

    fn process_function_requirements(
        fn_builder: &mut radium::FunctionBuilder<'def>,
        requirements: FunctionRequirements,
    ) {
        for e in requirements.early_coq_params {
            fn_builder.add_early_coq_param(e);
        }
        for e in requirements.late_coq_params {
            fn_builder.add_late_coq_param(e);
        }
        for e in requirements.proof_info.linktime_assumptions {
            fn_builder.add_linktime_assumption(e);
        }
        for e in requirements.proof_info.sidecond_tactics {
            fn_builder.add_manual_tactic(e);
        }
    }

    /// Parse and process attributes of this closure.
    fn process_closure_attrs<'b>(
        &mut self,
        trait_attrs: &TraitSpecNameScope,
        inputs: &[Ty<'tcx>],
        output: Ty<'tcx>,
        meta: ClosureMetaInfo<'b, 'tcx, 'def>,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("entering process_closure_attrs");
        let v = self.attrs;

        // Translate signature
        info!("inputs: {:?}, output: {:?}", inputs, output);
        let mut translated_arg_types: Vec<radium::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: radium::Type<'def> = self.ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: radium::Type<'def> = self.ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        // Determine parser
        let parser = rrconfig::attribute_parser();
        if parser.as_str() != "verbose" {
            trace!("leaving process_closure_attrs");
            return Err(TranslationError::UnknownAttributeParser(parser));
        }

        let mut spec_builder = radium::LiteralFunctionSpecBuilder::new();

        // add universal constraints
        let universal_constraints = self.get_relevant_universal_constraints();
        info!("universal constraints: {:?}", universal_constraints);
        for (lft1, lft2) in universal_constraints {
            spec_builder.add_lifetime_constraint(lft1, lft2);
        }

        let ty_translator = &self.ty_translator;
        // Hack: create indirection by tracking the tuple uses we create in here.
        // (We need a read reference to the scope, so we can't write to it at the same time)
        let mut tuple_uses = HashMap::new();
        {
            let scope = ty_translator.scope.borrow();
            let scope = FunctionSpecScope {
                generics: &*scope,
                attrs: trait_attrs,
            };
            let mut parser =
                VerboseFunctionSpecParser::new(&translated_arg_types, &translated_ret_type, &scope, |lit| {
                    ty_translator.translator.intern_literal(lit)
                });

            parser
                .parse_closure_spec(v, &mut spec_builder, meta, |x| {
                    ty_translator.make_tuple_use(x, Some(&mut tuple_uses))
                })
                .map_err(TranslationError::AttributeError)?;

            Self::process_function_requirements(&mut self.translated_fn, parser.into());
        }
        let mut scope = ty_translator.scope.borrow_mut();
        scope.tuple_uses.extend(tuple_uses);
        self.translated_fn.add_function_spec_from_builder(spec_builder);

        trace!("leaving process_closure_attrs");
        Ok(())
    }

    /// Parse and process attributes of this function.
    fn process_attrs(
        attrs: &[&ast::ast::AttrItem],
        ty_translator: &LocalTypeTranslator<'def, 'tcx>,
        translator: &mut radium::FunctionBuilder<'def>,
        trait_attrs: &TraitSpecNameScope,
        inputs: &[Ty<'tcx>],
        output: Ty<'tcx>,
    ) -> Result<radium::LiteralFunctionSpecBuilder<'def>, TranslationError<'tcx>> {
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let mut translated_arg_types: Vec<radium::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: radium::Type<'def> = ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: radium::Type<'def> = ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let mut spec_builder = radium::LiteralFunctionSpecBuilder::new();

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                {
                    let scope = ty_translator.scope.borrow();
                    let scope = FunctionSpecScope {
                        generics: &*scope,
                        attrs: trait_attrs,
                    };
                    let mut parser: VerboseFunctionSpecParser<'_, 'def, _, _> =
                        VerboseFunctionSpecParser::new(
                            &translated_arg_types,
                            &translated_ret_type,
                            &scope,
                            |lit| ty_translator.translator.intern_literal(lit),
                        );

                    parser
                        .parse_function_spec(attrs, &mut spec_builder)
                        .map_err(TranslationError::AttributeError)?;
                    Self::process_function_requirements(translator, parser.into());
                }

                Ok(spec_builder)
            },
            _ => Err(TranslationError::UnknownAttributeParser(parser)),
        }
    }

    /// Make a specification for a trait instance derived from the trait's default spec.
    fn make_trait_instance_spec(
        &self,
    ) -> Result<Option<radium::InstantiatedTraitFunctionSpec<'def>>, TranslationError<'tcx>> {
        let did = self.proc.get_id();
        if let Some(impl_did) = self.env.tcx().impl_of_method(did) {
            if let Some(trait_did) = self.env.tcx().trait_id_of_impl(impl_did) {
                let trait_ref = self
                    .trait_registry
                    .lookup_trait(trait_did)
                    .ok_or_else(|| TranslationError::TraitResolution(format!("{trait_did:?}")))?;
                let fn_name = strip_coq_ident(self.env.tcx().item_name(self.proc.get_id()).as_str());

                let trait_info = self.trait_registry.get_trait_impl_info(impl_did)?;
                //self.trait_registry.lookup_impl(impl_did)?;
                let attr_term = self.trait_registry.get_impl_attrs_term(impl_did)?;
                return Ok(Some(radium::InstantiatedTraitFunctionSpec::new(trait_info, fn_name, attr_term)));
            }
        }

        Ok(None)
    }

    // TODO refactor/ move
    fn to_universal_lft(
        &self,
        k: polonius_info::UniversalRegionKind,
        r: Region,
    ) -> Option<radium::UniversalLft> {
        match k {
            polonius_info::UniversalRegionKind::Function => Some(radium::UniversalLft::Function),
            polonius_info::UniversalRegionKind::Static => Some(radium::UniversalLft::Static),

            polonius_info::UniversalRegionKind::Local => self
                .ty_translator
                .scope
                .borrow()
                .lifetime_scope
                .lookup_region(r)
                .map(|x| radium::UniversalLft::Local(x.to_owned())),

            polonius_info::UniversalRegionKind::External => self
                .ty_translator
                .scope
                .borrow()
                .lifetime_scope
                .lookup_region(r)
                .map(|x| radium::UniversalLft::External(x.to_owned())),
        }
    }

    /// Translation that only generates a specification.
    pub fn generate_spec(
        self,
    ) -> Result<radium::FunctionSpec<radium::InnerFunctionSpec<'def>>, TranslationError<'tcx>> {
        self.translated_fn.try_into().map_err(TranslationError::AttributeError)
    }

    /// Generate a string identifier for a Local.
    /// Tries to find the Rust source code name of the local, otherwise simply enumerates.
    /// `used_names` keeps track of the Rust source code names that have already been used.
    fn make_local_name(mir_body: &Body<'tcx>, local: Local, used_names: &mut HashSet<String>) -> String {
        if let Some(mir_name) = Self::find_name_for_local(mir_body, local, used_names) {
            let name = strip_coq_ident(&mir_name);
            used_names.insert(mir_name);
            name
        } else {
            let mut name = "__".to_owned();
            name.push_str(&local.index().to_string());
            name
        }
    }

    /// Find a source name for a local of a MIR body, if possible.
    fn find_name_for_local(
        body: &mir::Body<'tcx>,
        local: mir::Local,
        used_names: &HashSet<String>,
    ) -> Option<String> {
        let debug_info = &body.var_debug_info;

        for dbg in debug_info {
            let name = &dbg.name;
            let val = &dbg.value;
            if let VarDebugInfoContents::Place(l) = *val {
                // make sure that the place projection is empty -- otherwise this might just
                // refer to the capture of a closure
                if let Some(this_local) = l.as_local() {
                    if this_local == local {
                        // around closures, multiple symbols may be mapped to the same name.
                        // To prevent this from happening, we check that the name hasn't been
                        // used already
                        // TODO: find better solution
                        if !used_names.contains(name.as_str()) {
                            return Some(name.as_str().to_owned());
                        }
                    }
                }
            } else {
                // is this case used when constant propagation happens during MIR construction?
            }
        }

        None
    }

    fn dump_body(body: &Body) {
        // TODO: print to file
        //for dec in &body.local_decls {
        //info!("Local decl: {:?}", dec);
        //}

        let basic_blocks = &body.basic_blocks;
        for (bb_idx, bb) in basic_blocks.iter_enumerated() {
            Self::dump_basic_block(bb_idx, bb);
        }
    }

    /// Dump a basic block as info debug output.
    fn dump_basic_block(bb_idx: BasicBlock, bb: &BasicBlockData) {
        info!("Basic block {:?}:", bb_idx);
        let mut i = 0;
        for s in &bb.statements {
            info!("{}\t{:?}", i, s);
            i += 1;
        }
        info!("{}\t{:?}", i, bb.terminator());
    }

    /// Determine initial constraints between universal regions and local place regions.
    /// Returns an initial mapping for the name _map that initializes place regions of arguments
    /// with universals.
    fn get_initial_universal_arg_constraints(
        &mut self,
        _sig_args: &[Ty<'tcx>],
        _local_args: &[Ty<'tcx>],
    ) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
        // Polonius generates a base subset constraint uregion ⊑ pregion.
        // We turn that into pregion = uregion, as we do strong updates at the top-level.
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let root_location = Location {
            block: BasicBlock::from_u32(0),
            statement_index: 0,
        };
        let root_point = self.info.interner.get_point_index(&facts::Point {
            location: root_location,
            typ: facts::PointType::Start,
        });

        // TODO: for nested references, this doesn't really seem to work.
        // Problem is that we don't have constraints for the mapping of nested references.
        // Potentially, we should instead just equalize the types

        let mut initial_arg_mapping = Vec::new();
        for (r1, r2, _) in subset_base {
            let lft1 = self.info.mk_atomic_region(*r1);
            let lft2 = self.info.mk_atomic_region(*r2);

            let polonius_info::AtomicRegion::Universal(polonius_info::UniversalRegionKind::Local, _) = lft1
            else {
                continue;
            };

            // this is a constraint we care about here, add it
            if self.inclusion_tracker.check_inclusion(*r1, *r2, root_point) {
                continue;
            }

            self.inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
            self.inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);

            assert!(matches!(lft2, polonius_info::AtomicRegion::PlaceRegion(_)));

            initial_arg_mapping.push((lft1, lft2));
        }
        initial_arg_mapping
    }

    #[allow(clippy::unused_self)]
    fn get_initial_universal_arg_constraints2(
        &mut self,
        sig_args: &[Ty<'tcx>],
        local_args: &[Ty<'tcx>],
    ) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
        // Polonius generates a base subset constraint uregion ⊑ pregion.
        // We turn that into pregion = uregion, as we do strong updates at the top-level.
        assert!(sig_args.len() == local_args.len());

        // TODO: implement a bitypefolder to solve this issue.
        Vec::new()
    }
}

/**
 * Struct that keeps track of all information necessary to translate a MIR Body to a `radium::Function`.
 * `'a` is the lifetime of the translator and ends after translation has finished.
 * `'def` is the lifetime of the generated code (the code may refer to struct defs).
 * `'tcx` is the lifetime of the rustc tctx.
 */
struct BodyTranslator<'a, 'def, 'tcx> {
    env: &'def Environment<'tcx>,
    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// maps locals to variable names
    variable_map: HashMap<Local, String>,
    /// the Caesium function buildder
    translated_fn: radium::FunctionBuilder<'def>,
    /// name of the return variable
    return_name: String,
    /// syntactic type of the thing to return
    return_synty: radium::SynType,
    /// all the other procedures used by this function, and:
    /// (code_loc_parameter_name, spec_name, type_inst, syntype_of_all_args)
    collected_procedures: HashMap<(DefId, GenericsKey<'tcx>), radium::UsedProcedure<'def>>,
    /// used statics
    collected_statics: HashSet<DefId>,

    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a ProcedureScope<'def>,
    /// scope of used consts
    const_registry: &'a ConstScope<'def>,
    /// trait registry
    trait_registry: &'def TraitRegistry<'tcx, 'def>,
    /// attributes on this function
    attrs: &'a [&'a ast::ast::AttrItem],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// local lifetimes: the LHS is the lifetime name, the RHS are the super lifetimes
    local_lifetimes: Vec<(radium::specs::Lft, Vec<radium::specs::Lft>)>,
    /// data structures for tracking which basic blocks still need to be translated
    /// (we only translate the basic blocks which are actually reachable, in particular when
    /// skipping unwinding)
    bb_queue: Vec<BasicBlock>,
    /// set of already processed blocks
    processed_bbs: HashSet<BasicBlock>,
    /// translator for types
    ty_translator: LocalTypeTranslator<'def, 'tcx>,

    /// map of loop heads to their optional spec closure defid
    loop_specs: HashMap<BasicBlock, Option<DefId>>,

    /// relevant locals: (local, name, type)
    fn_locals: Vec<(Local, String, radium::Type<'def>)>,

    /// result temporaries of checked ops that we rewrite
    /// we assume that this place is typed at (result_type, bool)
    /// and rewrite accesses to the first component to directly use the place,
    /// while rewriting accesses to the second component to true.
    /// TODO: once we handle panics properly, we should use a different translation.
    /// NOTE: we only rewrite for uses, as these are the only places these are used.
    checked_op_temporaries: HashMap<Local, Ty<'tcx>>,
}

impl<'a, 'def: 'a, 'tcx: 'def> BodyTranslator<'a, 'def, 'tcx> {
    /// Main translation function that actually does the translation and returns a `radium::Function`
    /// if successful.
    pub fn translate(
        mut self,
        initial_constraints: Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)>,
        spec_arena: &'def Arena<radium::FunctionSpec<radium::InnerFunctionSpec<'def>>>,
    ) -> Result<radium::Function<'def>, TranslationError<'tcx>> {
        // add loop info
        let loop_info = self.proc.loop_info();
        loop_info.dump_body_head();

        // translate the function's basic blocks
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // first translate the initial basic block; we add some additional annotations to the front
        let initial_bb_idx = BasicBlock::from_u32(0);
        if let Some(bb) = basic_blocks.get(initial_bb_idx) {
            let mut translated_bb = self.translate_basic_block(initial_bb_idx, bb)?;
            // push annotation for initial constraints that relate argument's place regions to universals
            for (r1, r2) in initial_constraints {
                translated_bb = radium::Stmt::Annot {
                    a: radium::Annotation::CopyLftName(
                        self.format_atomic_region(&r1),
                        self.format_atomic_region(&r2),
                    ),
                    s: Box::new(translated_bb),
                    why: Some("initialization".to_owned()),
                };
            }
            self.translated_fn.code.add_basic_block(initial_bb_idx.as_usize(), translated_bb);
        } else {
            info!("No basic blocks");
        }

        while let Some(bb_idx) = self.bb_queue.pop() {
            let bb = &basic_blocks[bb_idx];
            let translated_bb = self.translate_basic_block(bb_idx, bb)?;
            self.translated_fn.code.add_basic_block(bb_idx.as_usize(), translated_bb);
        }

        // assume that all generics are layoutable
        {
            let scope = self.ty_translator.scope.borrow();
            for ty in scope.generic_scope.iter().flatten() {
                self.translated_fn.assume_synty_layoutable(radium::SynType::Literal(ty.syn_type.clone()));
            }
        }
        // assume that all used literals are layoutable
        for g in self.ty_translator.scope.borrow().shim_uses.values() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }
        // assume that all used tuples are layoutable
        for g in self.ty_translator.scope.borrow().tuple_uses.values() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }

        // TODO: process self.loop_specs
        // - collect the relevant bb -> def_id mappings for this function (so we can eventually generate the
        //   definition)
        // - have a function that takes the def_id and then parses the attributes into a loop invariant
        for (head, did) in &self.loop_specs {
            let spec = self.parse_attributes_on_loop_spec_closure(*head, *did);
            self.translated_fn.register_loop_invariant(head.as_usize(), spec);
        }

        // generate dependencies on other procedures.
        for used_proc in self.collected_procedures.values() {
            self.translated_fn.require_function(used_proc.clone());
        }

        // generate dependencies on statics
        for did in &self.collected_statics {
            let s = &self.const_registry.statics[did];
            self.translated_fn.require_static(s.clone());
        }

        Ok(self.translated_fn.into_function(spec_arena))
    }

    /// Determine initial constraints between universal regions and local place regions.
    /// Returns an initial mapping for the name _map that initializes place regions of arguments
    /// with universals.
    fn get_initial_universal_arg_constraints(
        &mut self,
        _sig_args: &[Ty<'tcx>],
        _local_args: &[Ty<'tcx>],
    ) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
        // Polonius generates a base subset constraint uregion ⊑ pregion.
        // We turn that into pregion = uregion, as we do strong updates at the top-level.
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let root_location = Location {
            block: BasicBlock::from_u32(0),
            statement_index: 0,
        };
        let root_point = self.info.interner.get_point_index(&facts::Point {
            location: root_location,
            typ: facts::PointType::Start,
        });

        // TODO: for nested references, this doesn't really seem to work.
        // Problem is that we don't have constraints for the mapping of nested references.
        // Potentially, we should instead just equalize the types

        let mut initial_arg_mapping = Vec::new();
        for (r1, r2, _) in subset_base {
            let lft1 = self.info.mk_atomic_region(*r1);
            let lft2 = self.info.mk_atomic_region(*r2);

            let polonius_info::AtomicRegion::Universal(polonius_info::UniversalRegionKind::Local, _) = lft1
            else {
                continue;
            };

            // this is a constraint we care about here, add it
            if self.inclusion_tracker.check_inclusion(*r1, *r2, root_point) {
                continue;
            }

            self.inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
            self.inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);

            assert!(matches!(lft2, polonius_info::AtomicRegion::PlaceRegion(_)));

            initial_arg_mapping.push((lft1, lft2));
        }
        initial_arg_mapping
    }

    /// Abstract over the generics of a function and partially instantiate them.
    fn get_generic_abstraction_for_procedure(
        &self,
        ty_params: ty::GenericArgsRef<'tcx>,
        assoc_tys: &[ty::Ty<'tcx>],
    ) -> Result<AbstractedGenerics<'def>, TranslationError<'tcx>> {
        // get all the regions and type variables appearing that generics are instantiated with
        let mut tyvar_folder = TyVarFolder::new(self.env.tcx());
        let mut lft_folder = TyRegionCollectFolder::new(self.env.tcx());

        // also count the number of regions of the function itself
        let mut num_param_regions = 0;

        let mut callee_lft_param_inst: Vec<radium::Lft> = Vec::new();
        let mut callee_ty_param_inst = Vec::new();
        for v in ty_params {
            if let Some(ty) = v.as_type() {
                tyvar_folder.fold_ty(ty);
                lft_folder.fold_ty(ty);
            }
            if let Some(region) = v.as_region() {
                num_param_regions += 1;

                let lft_name =
                    self.ty_translator.translate_region(region).unwrap_or_else(|| "unknown".to_owned());
                callee_lft_param_inst.push(lft_name);
            }
        }
        // also find generics in the associated types
        for ty in assoc_tys {
            tyvar_folder.fold_ty(*ty);
            lft_folder.fold_ty(*ty);
        }

        let tyvars = tyvar_folder.get_result();
        let regions = lft_folder.get_regions();

        let mut scope = radium::GenericScope::empty();

        // instantiations for the function spec's paramters
        let mut fn_lft_param_inst = Vec::new();
        let mut fn_ty_param_inst = Vec::new();

        // re-bind the function's lifetime parameters
        for i in 0..num_param_regions {
            let lft_name = format!("ulft_{i}");
            scope.add_lft_param(lft_name.clone());
            fn_lft_param_inst.push(lft_name);
        }

        // bind the additional lifetime parameters
        let mut next_lft = num_param_regions;
        for region in regions {
            // Use the name the region has inside the function as the binder name, so that the
            // names work out when translating the types below
            let lft_name =
                self.ty_translator.translate_region_var(region).unwrap_or(format!("ulft_{next_lft}"));
            scope.add_lft_param(lft_name.clone());

            next_lft += 1;

            callee_lft_param_inst.push(lft_name);
        }

        // bind the generics we use
        for param in &tyvars {
            // NOTE: this should have the same name as the using occurrences
            let lit = radium::LiteralTyParam::new(param.name.as_str(), param.name.as_str());
            callee_ty_param_inst.push(radium::Type::LiteralParam(lit.clone()));
            scope.add_ty_param(lit);
        }
        // also bind associated types which we translate as generics
        for ty in assoc_tys {
            // we should check if it there is a parameter in the current scope for it
            let translated_ty = self.ty_translator.translate_type(*ty)?;
            if let radium::Type::LiteralParam(lit) = translated_ty {
                scope.add_ty_param(lit.clone());
                callee_ty_param_inst.push(radium::Type::LiteralParam(lit.clone()));
            }
        }

        // figure out instantiation for the function's generics
        for v in ty_params {
            if let Some(ty) = v.as_type() {
                let translated_ty = self.ty_translator.translate_type(ty)?;
                fn_ty_param_inst.push(translated_ty);
            }
        }
        // same for the associated types this function depends on
        for ty in assoc_tys {
            let translated_ty = self.ty_translator.translate_type(*ty)?;
            fn_ty_param_inst.push(translated_ty);
        }

        info!("Abstraction scope: {:?}", scope);
        info!("Fn instantiation: {:?}, {:?}", fn_lft_param_inst, fn_ty_param_inst);
        info!("Callee instantiation: {:?}, {:?}", callee_lft_param_inst, callee_ty_param_inst);

        let res = AbstractedGenerics {
            scope,
            callee_lft_param_inst,
            callee_ty_param_inst,
            fn_lft_param_inst,
            fn_ty_param_inst,
        };

        Ok(res)
    }

    /// Internally register that we have used a procedure with a particular instantiation of generics, and
    /// return the code parameter name.
    /// Arguments:
    /// - `callee_did`: the `DefId` of the callee
    /// - `ty_params`: the instantiation for the callee's type parameters
    /// - `trait_spec_terms`: if the callee has any trait assumptions, these are specification parameter terms
    ///   for these traits
    /// - `trait_assoc_tys`: if the callee has any trait assumptions, these are the instantiations for all
    ///   associated types
    fn register_use_procedure(
        &mut self,
        callee_did: DefId,
        extra_spec_args: Vec<String>,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_specs: Vec<radium::SpecializedTraitSpec<'def>>,
        trait_assoc_tys: &[ty::Ty<'tcx>],
    ) -> Result<(String, Vec<radium::Type<'def>>, Vec<radium::Lft>), TranslationError<'tcx>> {
        trace!("enter register_use_procedure callee_did={callee_did:?} ty_params={ty_params:?}");
        // The key does not include the associated types, as the resolution of the associated types
        // should always be unique for one combination of type parameters, as long as we remain in
        // the same environment (which is the case within this procedure).
        // Therefore, already the type parameters are sufficient to distinguish different
        // instantiations.
        let key = generate_args_inst_key(self.env.tcx(), ty_params)?;

        // re-quantify
        let quantified_args = self.get_generic_abstraction_for_procedure(ty_params, trait_assoc_tys)?;

        let tup = (callee_did, key);
        let res;
        if let Some(proc_use) = self.collected_procedures.get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            let meta = self
                .procedure_registry
                .lookup_function(callee_did)
                .ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", callee_did)))?;
            // explicit instantiation is needed sometimes
            let spec_name = format!("{} (RRGS:=RRGS)", meta.get_spec_name());
            let code_name = meta.get_name();
            let loc_name = format!("{}_loc", mangle_name_with_tys(code_name, tup.1.as_slice()));

            let syntypes = get_arg_syntypes_for_procedure_call(
                self.env.tcx(),
                &self.ty_translator,
                callee_did,
                ty_params.as_slice(),
            )?;

            let mut translated_params = quantified_args.fn_ty_param_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                loc_name, callee_did, translated_params, syntypes
            );

            let proc_use = radium::UsedProcedure::new(
                loc_name,
                spec_name,
                extra_spec_args,
                quantified_args.scope,
                trait_specs,
                translated_params,
                quantified_args.fn_lft_param_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures.insert(tup, proc_use);
        }
        trace!("leave register_use_procedure");
        Ok((res, quantified_args.callee_ty_param_inst, quantified_args.callee_lft_param_inst))
    }

    /// Internally register that we have used a trait method with a particular instantiation of
    /// generics, and return the code parameter name.
    fn register_use_trait_method<'c>(
        &'c mut self,
        callee_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
        trait_spec_terms: Vec<radium::SpecializedTraitSpec<'def>>,
        trait_assoc_tys: &[ty::Ty<'tcx>],
    ) -> Result<(String, Vec<radium::Type<'def>>, Vec<radium::Lft>), TranslationError<'tcx>> {
        trace!("enter register_use_trait_method did={:?} ty_params={:?}", callee_did, ty_params);
        // Does not include the associated types in the key; see `register_use_procedure` for an
        // explanation.
        let key = generate_args_inst_key(self.env.tcx(), ty_params)?;

        let (method_loc_name, method_spec_term, method_params) =
            self.ty_translator.register_use_trait_procedure(self.env, callee_did, ty_params)?;
        // re-quantify
        let quantified_args = self.get_generic_abstraction_for_procedure(method_params, trait_assoc_tys)?;

        let tup = (callee_did, key);
        let res;
        if let Some(proc_use) = self.collected_procedures.get(&tup) {
            res = proc_use.loc_name.clone();
        } else {
            // TODO: should we use ty_params or method_params?
            let syntypes = get_arg_syntypes_for_procedure_call(
                self.env.tcx(),
                &self.ty_translator,
                callee_did,
                ty_params.as_slice(),
            )?;

            let mut translated_params = quantified_args.fn_ty_param_inst;

            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                method_loc_name, callee_did, translated_params, syntypes
            );

            let proc_use = radium::UsedProcedure::new(
                method_loc_name,
                method_spec_term,
                vec![],
                quantified_args.scope,
                trait_spec_terms,
                translated_params,
                quantified_args.fn_lft_param_inst,
                syntypes,
            );

            res = proc_use.loc_name.clone();
            self.collected_procedures.insert(tup, proc_use);
        }
        trace!("leave register_use_procedure");
        Ok((res, quantified_args.callee_ty_param_inst, quantified_args.callee_lft_param_inst))
    }

    /// Enqueues a basic block for processing, if it has not already been processed,
    /// and marks it as having been processed.
    fn enqueue_basic_block(&mut self, bb: BasicBlock) {
        if !self.processed_bbs.contains(&bb) {
            self.bb_queue.push(bb);
            self.processed_bbs.insert(bb);
        }
    }

    /// Format an atomic region, using the naming info for universal lifetimes available in the current
    /// context.
    fn format_atomic_region(&self, r: &polonius_info::AtomicRegion) -> String {
        self.ty_translator.format_atomic_region(r)
    }

    fn format_region(&self, r: facts::Region) -> String {
        let lft = self.info.mk_atomic_region(r);
        self.format_atomic_region(&lft)
    }

    /// Parse the attributes on spec closure `did` as loop annotations and add it as an invariant
    /// to the generated code.
    fn parse_attributes_on_loop_spec_closure(
        &self,
        loop_head: BasicBlock,
        did: Option<DefId>,
    ) -> radium::LoopSpec {
        // for now: just make invariants True.

        // need to do:
        // - find out the locals in the right order, make parameter names for them. based on their type and
        //   initialization status, get the refinement type.
        // - output/pretty-print this map when generating the typing proof of each function. [done]
        //  + should not be a separate definition, but rather a "set (.. := ...)" with a marker type so
        //    automation can find it.

        // representation of loop invariants:
        // - introduce parameters for them.

        let mut rfn_binders = Vec::new();
        let prop_body = radium::IProp::True;

        // determine invariant on initialization:
        // - we need this both for the refinement invariant (though this could be removed if we make uninit
        //   generic over the refinement)
        // - in order to establish the initialization invariant in each loop iteration, since we don't have
        //   proper subtyping for uninit => maybe we could fix this too by making uninit variant in the
        //   refinement type? then we could have proper subtyping lemmas.
        //  + to bring it to the right refinement type initially, maybe have some automation /
        //  annotation
        // TODO: consider changing it like that.
        //
        // Note that StorageDead will not help us for determining initialization/ making it invariant, since
        // it only applies to full stack slots, not individual paths. one thing that makes it more
        // complicated in the frontend: initialization may in practice also be path-dependent.
        //  - this does not cause issues with posing a too strong loop invariant,
        //  - but this poses an issue for annotations
        //
        //

        // get locals
        for (_, name, ty) in &self.fn_locals {
            // get the refinement type
            let mut rfn_ty = ty.get_rfn_type();
            // wrap it in place_rfn, since we reason about places
            rfn_ty = coq::term::Type::PlaceRfn(Box::new(rfn_ty));

            // determine their initialization status
            //let initialized = true; // TODO
            // determine the actual refinement type for the current initialization status.

            let rfn_name = format!("r_{}", name);
            rfn_binders.push(coq::binder::Binder::new(Some(rfn_name), rfn_ty));
        }

        // TODO what do we do about stuff connecting borrows?
        if let Some(did) = did {
            let attrs = self.env.get_attributes(did);
            info!("attrs for loop {:?}: {:?}", loop_head, attrs);
        } else {
            info!("no attrs for loop {:?}", loop_head);
        }

        let pred = radium::IPropPredicate::new(rfn_binders, prop_body);
        radium::LoopSpec {
            func_predicate: pred,
        }
    }

    /// Checks whether a place access descends below a reference.
    fn check_place_below_reference(&self, place: &Place<'tcx>) -> bool {
        if self.checked_op_temporaries.contains_key(&place.local) {
            // temporaries are never below references
            return false;
        }

        for (pl, _) in place.iter_projections() {
            // check if the current ty is a reference that we then descend under with proj
            let cur_ty_kind = pl.ty(&self.proc.get_mir().local_decls, self.env.tcx()).ty.kind();
            if let TyKind::Ref(_, _, _) = cur_ty_kind {
                return true;
            }
        }

        false
    }

    fn get_assignment_strong_update_constraints(
        &mut self,
        loc: Location,
    ) -> HashSet<(Region, Region, PointIndex)> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let mut constraints = HashSet::new();
        // Polonius subset constraint are spawned for the midpoint
        let midpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Mid,
        });

        // for strong update: emit mutual equalities
        // TODO: alternative implementation: structurally compare regions in LHS type and RHS type
        for (s1, s2, point) in subset_base {
            if *point == midpoint {
                let lft1 = self.info.mk_atomic_region(*s1);
                let lft2 = self.info.mk_atomic_region(*s2);

                // We only care about inclusions into a place lifetime.
                // Moreover, we want to filter out the universal inclusions which are always
                // replicated at every point.
                if lft2.is_place() && !lft1.is_universal() {
                    // take this constraint and the reverse constraint
                    constraints.insert((*s1, *s2, *point));
                    //constraints.insert((*s2, *s1, *point));
                }
            }
        }
        constraints
    }

    fn get_assignment_weak_update_constraints(
        &mut self,
        loc: Location,
    ) -> HashSet<(Region, Region, PointIndex)> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let mut constraints = HashSet::new();
        // Polonius subset constraint are spawned for the midpoint
        let midpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Mid,
        });

        // for weak updates: should mirror the constraints generated by Polonius
        for (s1, s2, point) in subset_base {
            if *point == midpoint {
                // take this constraint
                // TODO should there be exceptions to this?

                if !self.inclusion_tracker.check_inclusion(*s1, *s2, *point) {
                    // only add it if it does not hold already, since we will enforce this
                    // constraint dynamically.
                    constraints.insert((*s1, *s2, *point));
                }
            }
        }
        constraints
    }

    /// Split the type of a function operand of a call expression to a base type and an instantiation for
    /// generics.
    fn call_expr_op_split_inst(
        &self,
        constant: &Constant<'tcx>,
    ) -> Result<
        (DefId, ty::PolyFnSig<'tcx>, ty::GenericArgsRef<'tcx>, ty::PolyFnSig<'tcx>),
        TranslationError<'tcx>,
    > {
        match constant.literal {
            ConstantKind::Ty(c) => {
                match c.ty().kind() {
                    TyKind::FnDef(def, args) => {
                        let ty: ty::EarlyBinder<Ty<'tcx>> = self.env.tcx().type_of(def);
                        let ty_ident = ty.instantiate_identity();
                        assert!(ty_ident.is_fn());
                        let ident_sig = ty_ident.fn_sig(self.env.tcx());

                        let ty_instantiated = ty.instantiate(self.env.tcx(), args.as_slice());
                        let instantiated_sig = ty_instantiated.fn_sig(self.env.tcx());

                        Ok((*def, ident_sig, args, instantiated_sig))
                    },
                    // TODO handle FnPtr, closure
                    _ => Err(TranslationError::Unimplemented {
                        description: "implement function pointers".to_owned(),
                    }),
                }
            },
            ConstantKind::Val(_, ty) => {
                match ty.kind() {
                    TyKind::FnDef(def, args) => {
                        let ty: ty::EarlyBinder<Ty<'tcx>> = self.env.tcx().type_of(def);

                        let ty_ident = ty.instantiate_identity();
                        assert!(ty_ident.is_fn());
                        let ident_sig = ty_ident.fn_sig(self.env.tcx());

                        let ty_instantiated = ty.instantiate(self.env.tcx(), args.as_slice());
                        let instantiated_sig = ty_instantiated.fn_sig(self.env.tcx());

                        Ok((*def, ident_sig, args, instantiated_sig))
                    },
                    // TODO handle FnPtr, closure
                    _ => Err(TranslationError::Unimplemented {
                        description: "implement function pointers".to_owned(),
                    }),
                }
            },
            ConstantKind::Unevaluated(_, _) => Err(TranslationError::Unimplemented {
                description: "implement ConstantKind::Unevaluated".to_owned(),
            }),
        }
    }

    /// Find the optional `DefId` of the closure giving the invariant for the loop with head `head_bb`.
    fn find_loop_spec_closure(&self, head_bb: BasicBlock) -> Result<Option<DefId>, TranslationError<'tcx>> {
        let bodies = self.proc.loop_info().get_loop_body(head_bb);
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // we go in order through the bodies in order to not stumble upon an annotation for a
        // nested loop!
        for body in bodies {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in &data.statements {
                    if let StatementKind::Assign(box (pl, _)) = stmt.kind {
                        if let Some(did) = self.is_spec_closure_local(pl.local)? {
                            return Ok(Some(did));
                        }
                    }
                }
            }
        }

        Ok(None)
    }

    /// Translate a goto-like jump to `target`.
    fn translate_goto_like(
        &mut self,
        _loc: &Location,
        target: BasicBlock,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        self.enqueue_basic_block(target);
        let res_stmt = radium::Stmt::GotoBlock(target.as_usize());

        let loop_info = self.proc.loop_info();
        if loop_info.is_loop_head(target) && !self.loop_specs.contains_key(&target) {
            let spec_defid = self.find_loop_spec_closure(target)?;
            self.loop_specs.insert(target, spec_defid);
        }

        Ok(res_stmt)
    }

    /// Check if a call goes to `std::rt::begin_panic`
    fn is_call_destination_panic(&mut self, func: &Operand) -> bool {
        let Operand::Constant(box c) = func else {
            return false;
        };

        let ConstantKind::Val(_, ty) = c.literal else {
            return false;
        };

        let TyKind::FnDef(did, _) = ty.kind() else {
            return false;
        };

        if let Some(panic_id_std) =
            utils::try_resolve_did(self.env.tcx(), &["std", "panicking", "begin_panic"])
        {
            if panic_id_std == *did {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of std::panicking::begin_panic");
        }

        if let Some(panic_id_core) = utils::try_resolve_did(self.env.tcx(), &["core", "panicking", "panic"]) {
            if panic_id_core == *did {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::panicking::panic");
        }

        false
    }

    /// Registers a drop shim for a particular type for the translation.
    #[allow(clippy::unused_self)]
    const fn register_drop_shim_for(&self, _ty: Ty<'tcx>) {
        // TODO!
        //let drop_in_place_did: DefId = utils::try_resolve_did(self.env.tcx(), &["std", "ptr",
        // "drop_in_place"]).unwrap();

        //let x: ty::InstanceDef = ty::InstanceDef::DropGlue(drop_in_place_did, Some(ty));
        //let body: &'tcx mir::Body = self.env.tcx().mir_shims(x);

        //info!("Generated drop shim for {:?}", ty);
        //Self::dump_body(body);
    }

    fn compute_call_regions(
        &self,
        func: &Constant<'tcx>,
        loc: Location,
    ) -> Result<CallRegions, TranslationError<'tcx>> {
        let midpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Mid,
        });

        // first identify substitutions for the early-bound regions
        let (target_did, sig, substs, _) = self.call_expr_op_split_inst(func)?;
        info!("calling function {:?}", target_did);
        let mut early_regions = Vec::new();
        info!("call substs: {:?} = {:?}, {:?}", func, sig, substs);
        for a in substs {
            if let ty::GenericArgKind::Lifetime(r) = a.unpack() {
                if let ty::RegionKind::ReVar(r) = r.kind() {
                    early_regions.push(r);
                }
            }
        }
        info!("call region instantiations (early): {:?}", early_regions);

        // this is a hack to identify the inference variables introduced for the
        // call's late-bound universals.
        // TODO: Can we get this information in a less hacky way?
        // One approach: compute the early + late bound regions for a given DefId, similarly to how
        // we do it when starting to translate a function
        // Problem: this doesn't give a straightforward way to compute their instantiation

        // now find all the regions that appear in type parameters we instantiate.
        // These are regions that the callee doesn't know about.
        let mut generic_regions = HashSet::new();
        let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
            ty::RegionKind::ReVar(rv) => {
                generic_regions.insert(rv);
                r
            },
            _ => r,
        };

        for a in substs {
            if let ty::GenericArgKind::Type(c) = a.unpack() {
                let mut folder = ty::fold::RegionFolder::new(self.env.tcx(), &mut clos);
                folder.fold_ty(c);
            }
        }
        info!("Regions of generic args: {:?}", generic_regions);

        // go over all region constraints initiated at this location
        let new_constraints = self.info.get_new_subset_constraints_at_point(midpoint);
        let mut new_regions = HashSet::new();
        let mut relevant_constraints = Vec::new();
        for (r1, r2) in &new_constraints {
            if matches!(self.info.get_region_kind(*r1), polonius_info::RegionKind::Unknown) {
                // this is probably a inference variable for the call
                new_regions.insert(*r1);
                relevant_constraints.push((*r1, *r2));
            }
            if matches!(self.info.get_region_kind(*r2), polonius_info::RegionKind::Unknown) {
                new_regions.insert(*r2);
                relevant_constraints.push((*r1, *r2));
            }
        }
        // first sort this to enable cycle resolution
        let mut new_regions_sorted: Vec<Region> = new_regions.iter().copied().collect();
        new_regions_sorted.sort();

        // identify the late-bound regions
        let mut late_regions = Vec::new();
        for r in &new_regions_sorted {
            // only take the ones which are not early bound and
            // which are not due to a generic (the callee doesn't care about generic regions)
            if !early_regions.contains(r) && !generic_regions.contains(r) {
                late_regions.push(*r);
            }
        }
        info!("call region instantiations (late): {:?}", late_regions);

        // Notes:
        // - if two of the call regions need to be equal due to constraints on the function, we define the one
        //   with the larger id in terms of the other one
        // - we ignore unidirectional subset constraints between call regions (these do not help in finding a
        //   solution if we take the transitive closure beforehand)
        // - if a call region needs to be equal to a local region, we directly define it in terms of the local
        //   region
        // - otherwise, it will be an intersection of local regions
        let mut new_regions_classification = HashMap::new();
        // compute transitive closure of constraints
        let relevant_constraints = polonius_info::compute_transitive_closure(relevant_constraints);
        for r in &new_regions_sorted {
            for (r1, r2) in &relevant_constraints {
                if *r2 != *r {
                    continue;
                }

                // i.e. (flipping it around when we are talking about lifetimes),
                // r needs to be a sublft of r1
                if relevant_constraints.contains(&(*r2, *r1)) {
                    // if r1 is also a new region and r2 is ordered before it, we will
                    // just define r1 in terms of r2
                    if new_regions.contains(r1) && r2.as_u32() < r1.as_u32() {
                        continue;
                    }
                    // need an equality constraint
                    new_regions_classification.insert(*r, CallRegionKind::EqR(*r1));
                    // do not consider the rest of the constraints as r is already
                    // fully specified
                    break;
                }

                // the intersection also needs to contain r1
                if new_regions.contains(r1) {
                    // we do not need this constraint, since we already computed the
                    // transitive closure.
                    continue;
                }

                let kind = new_regions_classification
                    .entry(*r)
                    .or_insert(CallRegionKind::Intersection(HashSet::new()));

                let CallRegionKind::Intersection(s) = kind else {
                    unreachable!();
                };

                s.insert(*r1);
            }
        }
        info!("call arg classification: {:?}", new_regions_classification);

        Ok(CallRegions {
            early_regions,
            late_regions,
            classification: new_regions_classification,
        })
    }

    fn translate_function_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Place<'tcx>,
        target: Option<middle::mir::BasicBlock>,
        loc: Location,
        dying_loans: &[facts::Loan],
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        let startpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Start,
        });

        let Operand::Constant(box func_constant) = func else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of call operand (got: {:?})",
                    func
                ),
            });
        };

        // for lifetime annotations:
        // 1. get the regions involved here. for that, get the instantiation of the function.
        //    + if it's a FnDef type, that should be easy.
        //    + for a function pointer: ?
        //    + for a closure: ?
        //   (Polonius does not seem to distinguish early/late bound in any way, except
        //   that they are numbered in different passes)
        // 2. find the constraints here involving the regions.
        // 3. solve for the regions.
        //    + transitively propagate the constraints
        //    + check for equalities
        //    + otherwise compute intersection. singleton intersection just becomes an equality def.
        // 4. add annotations accordingly
        //    + either a startlft
        //    + or a copy name
        // 5. add shortenlft annotations to line up arguments.
        //    + for that, we need the type of the LHS, and what the argument types (with
        //    substituted regions) should be.
        // 6. annotate the return value on assignment and establish constraints.

        let classification = self.compute_call_regions(func_constant, loc)?;

        // update the inclusion tracker with the new regions we have introduced
        // We just add the inclusions and ignore that we resolve it in a "tight" way.
        // the cases where we need the reverse inclusion should be really rare.
        for (r, c) in &classification.classification {
            match c {
                CallRegionKind::EqR(r2) => {
                    // put it at the start point, because the inclusions come into effect
                    // at the point right before.
                    self.inclusion_tracker.add_static_inclusion(*r, *r2, startpoint);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                },
                CallRegionKind::Intersection(lfts) => {
                    // all the regions represented by lfts need to be included in r
                    for r2 in lfts {
                        self.inclusion_tracker.add_static_inclusion(*r2, *r, startpoint);
                    }
                },
            }
        }

        // translate the function expression.
        let func_expr = self.translate_operand(func, false)?;
        // We expect this to be an Expr::CallTarget, being annotated with the type parameters we
        // instantiate it with.
        let radium::Expr::CallTarget(func_lit, ty_param_annots, mut lft_param_annots) = func_expr else {
            unreachable!("Logic error in call target translation");
        };
        let func_expr = radium::Expr::MetaParam(func_lit);

        // translate the arguments
        let mut translated_args = Vec::new();
        for arg in args {
            // to_ty is the type the function expects

            //let ty = arg.ty(&self.proc.get_mir().local_decls, self.env.tcx());
            let translated_arg = self.translate_operand(arg, true)?;
            translated_args.push(translated_arg);
        }

        // We have to add the late regions, since we do not requantify over them.
        for late in &classification.late_regions {
            let lft = self.format_region(*late);
            lft_param_annots.push(lft);
        }
        info!("Call lifetime instantiation (early): {:?}", classification.early_regions);
        info!("Call lifetime instantiation (late): {:?}", classification.late_regions);

        // Get the type of the return value from the function
        let (_, _, _, inst_sig) = self.call_expr_op_split_inst(func_constant)?;
        // TODO: do we need to do something with late bounds?
        let output_ty = inst_sig.output().skip_binder();
        info!("call has instantiated type {:?}", inst_sig);

        // compute the resulting annotations
        let (rhs_annots, pre_stmt_annots, post_stmt_annots) =
            self.get_assignment_annots(loc, destination, output_ty);
        info!(
            "assignment annots after call: expr: {:?}, pre-stmt: {:?}, post-stmt: {:?}",
            rhs_annots, pre_stmt_annots, post_stmt_annots
        );

        // TODO: add annotations for the assignment
        // for that:
        // - get the type of the place
        // - enforce constraints as necessary. this might spawn dyninclusions with some of the new regions =>
        //   In Coq, also the aliases should get proper endlft events to resolve the dyninclusions.
        // - update the name map
        let call_expr = radium::Expr::Call {
            f: Box::new(func_expr),
            lfts: lft_param_annots,
            tys: ty_param_annots,
            args: translated_args,
        };
        let stmt = match target {
            Some(target) => {
                let mut cont_stmt = self.translate_goto_like(&loc, target)?;
                // end loans before the goto, but after the call.
                // TODO: may cause duplications?
                cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.iter().copied());

                let cont_stmt = radium::Stmt::with_annotations(
                    cont_stmt,
                    post_stmt_annots,
                    &Some("post_function_call".to_owned()),
                );

                // assign stmt with call; then jump to bb
                let place_ty = self.get_type_of_place(destination);
                let place_st = self.ty_translator.translate_type_to_syn_type(place_ty.ty)?;
                let place_expr = self.translate_place(destination)?;
                let ot = place_st.into();

                let annotated_rhs = radium::Expr::with_optional_annotation(
                    call_expr,
                    rhs_annots,
                    Some("function_call".to_owned()),
                );
                let assign_stmt = radium::Stmt::Assign {
                    ot,
                    e1: place_expr,
                    e2: annotated_rhs,
                    s: Box::new(cont_stmt),
                };
                radium::Stmt::with_annotations(
                    assign_stmt,
                    pre_stmt_annots,
                    &Some("function_call".to_owned()),
                )
            },
            None => {
                // expr stmt with call; then stuck (we have not provided a continuation, after all)
                radium::Stmt::ExprS {
                    e: call_expr,
                    s: Box::new(radium::Stmt::Stuck),
                }
            },
        };

        let mut stmt_annots = Vec::new();

        // add annotations to initialize the regions for the call (before the call)
        for (r, class) in &classification.classification {
            let lft = self.format_region(*r);
            match class {
                CallRegionKind::EqR(r2) => {
                    let lft2 = self.format_region(*r2);
                    stmt_annots.push(radium::Annotation::CopyLftName(lft2, lft));
                },

                CallRegionKind::Intersection(rs) => {
                    match rs.len() {
                        0 => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support unconstrained lifetime"
                                    .to_owned(),
                            });
                        },
                        1 => {
                            // this is really just an equality constraint
                            if let Some(r2) = rs.iter().next() {
                                let lft2 = self.format_region(*r2);
                                stmt_annots.push(radium::Annotation::CopyLftName(lft2, lft));
                            }
                        },
                        _ => {
                            // a proper intersection
                            let lfts: Vec<_> = rs.iter().map(|r| self.format_region(*r)).collect();
                            stmt_annots.push(radium::Annotation::AliasLftIntersection(lft, lfts));
                        },
                    };
                },
            }
        }

        let stmt = radium::Stmt::with_annotations(stmt, stmt_annots, &Some("function_call".to_owned()));
        Ok(stmt)
    }

    /// Translate a terminator.
    /// We pass the dying loans during this terminator. They need to be added at the right
    /// intermediate point.
    fn translate_terminator(
        &mut self,
        term: &Terminator<'tcx>,
        loc: Location,
        dying_loans: Vec<facts::Loan>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        match &term.kind {
            TerminatorKind::Goto { target } => self.translate_goto_like(&loc, *target),

            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                trace!("translating Call {:?}", term);
                if self.is_call_destination_panic(func) {
                    info!("Replacing call to std::panicking::begin_panic with Stuck");
                    return Ok(radium::Stmt::Stuck);
                }

                self.translate_function_call(func, args, destination, *target, loc, dying_loans.as_slice())
            },

            TerminatorKind::Return => {
                // TODO: this requires additional handling for reborrows

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                let stmt = radium::Stmt::Return(radium::Expr::Use {
                    ot: (&self.return_synty).into(),
                    e: Box::new(radium::Expr::Var(self.return_name.clone())),
                });

                // TODO is this right?
                Ok(self.prepend_endlfts(stmt, dying_loans.into_iter()))
            },

            //TerminatorKind::Abort => {
            //res_stmt = radium::Stmt::Stuck;
            //res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
            //},
            TerminatorKind::SwitchInt { discr, targets } => {
                let operand = self.translate_operand(discr, true)?;
                let all_targets: &[BasicBlock] = targets.all_targets();

                if self.get_type_of_operand(discr).is_bool() {
                    // we currently special-case this as Caesium has a built-in if and this is more
                    // convenient to handle for the type-checker

                    // implementation detail: the first index is the `false` branch, the second the
                    // `true` branch
                    let true_target = all_targets[1];
                    let false_target = all_targets[0];

                    let true_branch = self.translate_goto_like(&loc, true_target)?;
                    let false_branch = self.translate_goto_like(&loc, false_target)?;

                    let stmt = radium::Stmt::If {
                        e: operand,
                        ot: radium::OpType::Bool,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    };

                    // TODO: is this right?
                    return Ok(self.prepend_endlfts(stmt, dying_loans.into_iter()));
                }

                //info!("switchint: {:?}", term.kind);
                let operand = self.translate_operand(discr, true)?;
                let ty = self.get_type_of_operand(discr);

                let mut target_map: HashMap<u128, usize> = HashMap::new();
                let mut translated_targets: Vec<radium::Stmt> = Vec::new();

                for (idx, (tgt, bb)) in targets.iter().enumerate() {
                    let bb: BasicBlock = bb;
                    let translated_target = self.translate_goto_like(&loc, bb)?;

                    target_map.insert(tgt, idx);
                    translated_targets.push(translated_target);
                }

                let translated_default = self.translate_goto_like(&loc, targets.otherwise())?;
                // TODO: need to put endlfts infront of gotos?

                let translated_ty = self.ty_translator.translate_type(ty)?;
                let radium::Type::Int(it) = translated_ty else {
                    return Err(TranslationError::UnknownError(
                        "SwitchInt switching on non-integer type".to_owned(),
                    ));
                };

                Ok(radium::Stmt::Switch {
                    e: operand,
                    it,
                    index_map: target_map,
                    bs: translated_targets,
                    def: Box::new(translated_default),
                })
            },

            TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // this translation gets stuck on failure
                let cond_translated = self.translate_operand(cond, true)?;
                let comp = radium::Expr::BinOp {
                    o: radium::Binop::Eq,
                    ot1: radium::OpType::Bool,
                    ot2: radium::OpType::Bool,
                    e1: Box::new(cond_translated),
                    e2: Box::new(radium::Expr::Literal(radium::Literal::Bool(*expected))),
                };

                let stmt = self.translate_goto_like(&loc, *target)?;

                // TODO: should we really have this?
                let stmt = self.prepend_endlfts(stmt, dying_loans.into_iter());

                Ok(radium::Stmt::AssertS {
                    e: comp,
                    s: Box::new(stmt),
                })
            },

            TerminatorKind::Drop { place, target, .. } => {
                let ty = self.get_type_of_place(place);
                self.register_drop_shim_for(ty.ty);

                let place_translated = self.translate_place(place)?;
                let _drope = radium::Expr::DropE(Box::new(place_translated));

                let stmt = self.translate_goto_like(&loc, *target)?;

                Ok(self.prepend_endlfts(stmt, dying_loans.into_iter()))

                //res_stmt = radium::Stmt::ExprS { e: drope, s: Box::new(res_stmt)};
            },

            // just a goto for our purposes
            TerminatorKind::FalseEdge { real_target, .. }
            // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                self.translate_goto_like(&loc, *real_target)
            },

            TerminatorKind::Unreachable => Ok(radium::Stmt::Stuck),

            TerminatorKind::UnwindResume => Err(TranslationError::Unimplemented {
                description: "implement UnwindResume".to_owned(),
            }),

            TerminatorKind::UnwindTerminate(_) => Err(TranslationError::Unimplemented {
                description: "implement UnwindTerminate".to_owned(),
            }),

            TerminatorKind::GeneratorDrop
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. } => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of terminator (got: {:?})",
                    term
                ),
            }),
        }
    }

    /// Prepend endlft annotations for dying loans to a statement.
    fn prepend_endlfts<I>(&self, st: radium::Stmt, dying: I) -> radium::Stmt
    where
        I: ExactSizeIterator<Item = facts::Loan>,
    {
        let mut cont_stmt = st;
        if dying.len() > 0 {
            //info!("Dying at {:?}: {:?}", loc, dying);
            for d in dying {
                let lft = self.info.atomic_region_of_loan(d);
                cont_stmt = radium::Stmt::Annot {
                    a: radium::Annotation::EndLft(self.format_atomic_region(&lft)),
                    s: Box::new(cont_stmt),
                    why: Some("endlft".to_owned()),
                };
            }
        }
        cont_stmt
    }

    /// Get predecessors in the CFG.
    fn get_loc_predecessors(&self, loc: Location) -> Vec<Location> {
        if loc.statement_index > 0 {
            let pred = Location {
                block: loc.block,
                statement_index: loc.statement_index - 1,
            };
            vec![pred]
        } else {
            // check for gotos that go to this basic block
            let pred_bbs = self.proc.predecessors(loc.block);
            let basic_blocks = &self.proc.get_mir().basic_blocks;
            pred_bbs
                .iter()
                .map(|bb| {
                    let data = &basic_blocks[*bb];
                    Location {
                        block: *bb,
                        statement_index: data.statements.len(),
                    }
                })
                .collect()
        }
    }

    /// Collect all the regions appearing in a type.
    fn find_region_variables_of_place_type(&self, ty: PlaceTy<'tcx>) -> HashSet<Region> {
        let mut collector = TyRegionCollectFolder::new(self.env.tcx());
        if ty.variant_index.is_some() {
            panic!("find_region_variables_of_place_type: don't support enums");
        }

        ty.ty.fold_with(&mut collector);
        collector.get_regions()
    }

    /// Generate an annotation on an expression needed to update the region name map.
    fn generate_strong_update_annot(&self, ty: PlaceTy<'tcx>) -> Option<radium::Annotation> {
        let (interesting, tree) = self.generate_strong_update_annot_rec(ty.ty);
        interesting.then(|| radium::Annotation::GetLftNames(tree))
    }

    /// Returns a tree for giving names to Coq lifetimes based on RR types.
    /// The boolean indicates whether the tree is "interesting", i.e. whether it names at least one
    /// lifetime.
    fn generate_strong_update_annot_rec(&self, ty: Ty<'tcx>) -> (bool, radium::LftNameTree) {
        // TODO for now this just handles nested references
        match ty.kind() {
            ty::TyKind::Ref(r, ty, _) => match r.kind() {
                ty::RegionKind::ReVar(r) => {
                    let name = self.format_region(r);
                    let (_, ty_tree) = self.generate_strong_update_annot_rec(*ty);
                    (true, radium::LftNameTree::Ref(name, Box::new(ty_tree)))
                },
                _ => {
                    panic!("generate_strong_update_annot: expected region variable");
                },
            },
            _ => (false, radium::LftNameTree::Leaf),
        }
    }

    /// Generate an annotation to adapt the type of `expr` to `target_ty` from type `current_ty` by
    /// means of shortening lifetimes.
    fn generate_shortenlft_annot(
        &self,
        target_ty: Ty<'tcx>,
        _current_ty: Ty<'tcx>,
        mut expr: radium::Expr,
    ) -> radium::Expr {
        // this is not so different from the strong update annotation
        let (interesting, tree) = self.generate_strong_update_annot_rec(target_ty);
        if interesting {
            expr = radium::Expr::Annot {
                a: radium::Annotation::ShortenLft(tree),
                e: Box::new(expr),
                why: None,
            };
        }
        expr
    }

    /// Find all regions that need to outlive a loan region at its point of creation, and
    /// add the corresponding constraints to the inclusion tracker.
    fn get_outliving_regions_on_loan(&mut self, r: Region, loan_point: PointIndex) -> Vec<Region> {
        // get all base subset constraints r' ⊆ r
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let mut outliving = Vec::new();

        let subset_base = &input_facts.subset_base;
        for (r1, r2, p) in subset_base {
            if *p == loan_point && *r2 == r {
                self.inclusion_tracker.add_static_inclusion(*r1, *r2, *p);
                outliving.push(*r1);
            }
            // other subset constraints at this point are due to (for instance) the assignment of
            // the loan to a place and are handled there.
        }
        outliving
    }

    /// Check if a local is used for a spec closure.
    fn is_spec_closure_local(&self, l: Local) -> Result<Option<DefId>, TranslationError<'tcx>> {
        // check if we should ignore this
        let local_type = self.get_type_of_local(l)?;

        let TyKind::Closure(did, _) = local_type.kind() else {
            return Ok(None);
        };

        Ok(self
            .procedure_registry
            .lookup_function_mode(*did)
            .and_then(|m| m.is_ignore().then_some(*did)))
    }

    fn region_to_region_vid(r: ty::Region<'tcx>) -> facts::Region {
        match r.kind() {
            ty::RegionKind::ReVar(vid) => vid,
            _ => panic!(),
        }
    }

    /// Generate a dynamic inclusion of r1 in r2 at point p. Prepends annotations for doing so to `cont`.
    fn generate_dyn_inclusion(
        &mut self,
        stmt_annots: &mut Vec<radium::Annotation>,
        r1: Region,
        r2: Region,
        p: PointIndex,
    ) {
        // check if inclusion already holds
        if !self.inclusion_tracker.check_inclusion(r1, r2, p) {
            // check if the reverse inclusion already holds
            if self.inclusion_tracker.check_inclusion(r2, r1, p) {
                // our invariant is that this must be a static inclusion
                assert!(self.inclusion_tracker.check_static_inclusion(r2, r1, p));
                self.inclusion_tracker.add_dynamic_inclusion(r1, r2, p);

                // we generate an extendlft instruction
                // for this, we need to figure out a path to make this inclusion true, i.e. we need
                // an explanation of why it is syntactically included.
                // TODO: for now, we just assume that r1 ⊑ₗ [r2] (in terms of Coq lifetime inclusion)
                stmt_annots.push(radium::Annotation::ExtendLft(self.format_region(r1)));
            } else {
                self.inclusion_tracker.add_dynamic_inclusion(r1, r2, p);
                // we generate a dynamic inclusion instruction
                // we flip this around because the annotations are talking about lifetimes, which are oriented
                // the other way around.
                stmt_annots
                    .push(radium::Annotation::DynIncludeLft(self.format_region(r2), self.format_region(r1)));
            }
        }
    }

    /// Generates dynamic inclusions for the set of inclusions in `incls`.
    /// These inclusions should not hold yet.
    /// Skips mutual inclusions -- we cannot interpret these.
    fn generate_dyn_inclusions(
        &mut self,
        incls: &HashSet<(Region, Region, PointIndex)>,
    ) -> Vec<radium::Annotation> {
        // before executing the assignment, first enforce dynamic inclusions
        info!("Generating dynamic inclusions {:?}", incls);
        let mut stmt_annots = Vec::new();

        for (r1, r2, p) in incls {
            if incls.contains(&(*r2, *r1, *p)) {
                warn!("Skipping impossible dynamic inclusion {:?} ⊑ {:?} at {:?}", r1, r2, p);
                continue;
            }

            self.generate_dyn_inclusion(&mut stmt_annots, *r1, *r2, *p);
        }

        stmt_annots
    }

    /// Get the annotations due to borrows appearing on the RHS of an assignment.
    fn get_assignment_loan_annots(&mut self, loc: Location, rhs: &Rvalue<'tcx>) -> Vec<radium::Annotation> {
        let mut stmt_annots = Vec::new();

        // if we create a new loan here, start a new lifetime for it
        let loan_point = self.info.get_point(loc, facts::PointType::Mid);
        if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
            // TODO: is this fine for aggregates? I suppose, if I create a loan for an
            // aggregate, I want to use the same atomic region for all of its components
            // anyways.

            let lft = self.info.atomic_region_of_loan(loan);
            let r = lft.get_region();

            // get the static inclusions we need to generate here and add them to the
            // inclusion tracker
            let outliving = self.get_outliving_regions_on_loan(r, loan_point);

            // add statement for issuing the loan
            stmt_annots.insert(
                0,
                radium::Annotation::StartLft(
                    self.format_atomic_region(&lft),
                    outliving.iter().map(|r| self.format_region(*r)).collect(),
                ),
            );

            let a = self.info.get_region_kind(r);
            info!("Issuing loan at {:?} with kind {:?}: {:?}; outliving: {:?}", loc, a, loan, outliving);
        } else if let Rvalue::Ref(region, BorrowKind::Shared, _) = rhs {
            // for shared reborrows, Polonius does not create a new loan, and so the
            // previous case did not match.
            // However, we still need to track the region created for the reborrow in an
            // annotation.

            let region = BodyTranslator::region_to_region_vid(*region);

            // find inclusion ?r1 ⊑ region -- we will actually enforce region = r1
            let new_constrs: Vec<(facts::Region, facts::Region)> =
                self.info.get_new_subset_constraints_at_point(loan_point);
            info!("Shared reborrow at {:?} with new constrs: {:?}", region, new_constrs);
            let mut included_region = None;
            for (r1, r2) in &new_constrs {
                if *r2 == region {
                    included_region = Some(r1);
                    break;
                }
            }
            if let Some(r) = included_region {
                //info!("Found inclusion {:?}⊑  {:?}", r, region);
                stmt_annots.push(radium::Annotation::CopyLftName(
                    self.format_region(*r),
                    self.format_region(region),
                ));

                // also add this to the inclusion checker
                self.inclusion_tracker.add_static_inclusion(*r, region, loan_point);
            } else {
                // This happens e.g. when borrowing from a raw pointer etc.
                info!("Found unconstrained shared borrow for {:?}", region);
                let inferred_constrained = vec![];

                // add statement for issuing the loan
                stmt_annots
                    .push(radium::Annotation::StartLft(self.format_region(region), inferred_constrained));
            }
        }

        stmt_annots
    }

    /// Compute the annotations for an assignment: an annotation for the rhs value, and a list of
    /// annotations to prepend to the statement, and a list of annotations to put after the
    /// statement.
    fn get_assignment_annots(
        &mut self,
        loc: Location,
        lhs: &Place<'tcx>,
        _rhs_ty: Ty<'tcx>,
    ) -> (Option<radium::Annotation>, Vec<radium::Annotation>, Vec<radium::Annotation>) {
        // check if the place is strongly writeable
        let strongly_writeable = !self.check_place_below_reference(lhs);
        let plc_ty = self.get_type_of_place(lhs);

        let new_dyn_inclusions;
        let expr_annot;
        let stmt_annot;
        if strongly_writeable {
            // we are going to update the region mapping through annotations,
            // and hence put up a barrier for propagation of region constraints

            // structurally go over the type and find region variables.
            // for each of the variables, issue a barrier.
            // also track them together with the PlaceItems needed to reach them.
            // from the latter, we can generate the necessary annotations
            let regions = self.find_region_variables_of_place_type(plc_ty);

            // put up a barrier at the Mid point
            let barrier_point_index = self.info.interner.get_point_index(&facts::Point {
                location: loc,
                typ: facts::PointType::Mid,
            });
            for r in &regions {
                self.inclusion_tracker.add_barrier(*r, barrier_point_index);
            }
            // get new constraints that should be enforced
            let new_constraints = self.get_assignment_strong_update_constraints(loc);
            stmt_annot = Vec::new();
            for (r1, r2, p) in &new_constraints {
                self.inclusion_tracker.add_static_inclusion(*r1, *r2, *p);
                self.inclusion_tracker.add_static_inclusion(*r2, *r1, *p);

                // TODO: use this instead of the expr_annot below
                //stmt_annot.push(
                //radium::Annotation::CopyLftName(
                //self.format_region(*r1),
                //self.format_region(*r2),
                //));
            }

            // TODO: get rid of this
            // similarly generate an annotation that encodes these constraints in the RR
            // type system
            expr_annot = self.generate_strong_update_annot(plc_ty);
            //expr_annot = None;

            new_dyn_inclusions = HashSet::new();
        } else {
            // need to filter out the constraints that are relevant here.
            // incrementally go through them.
            new_dyn_inclusions = self.get_assignment_weak_update_constraints(loc);
            expr_annot = None;
            stmt_annot = Vec::new();
        }

        // First enforce the new inclusions, then do the other annotations
        let new_dyn_inclusions = self.generate_dyn_inclusions(&new_dyn_inclusions);
        (expr_annot, new_dyn_inclusions, stmt_annot)
    }

    /// Get the regions appearing in a type.
    fn get_regions_of_ty(&self, ty: Ty<'tcx>) -> HashSet<ty::RegionVid> {
        let mut regions = HashSet::new();
        let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
            ty::RegionKind::ReVar(rv) => {
                regions.insert(rv);
                r
            },
            _ => r,
        };
        let mut folder = ty::fold::RegionFolder::new(self.env.tcx(), &mut clos);
        folder.fold_ty(ty);
        regions
    }

    /// On creating a composite value (e.g. a struct or enum), the composite value gets its own
    /// Polonius regions. We need to map these regions properly to the respective lifetimes.
    fn get_composite_rvalue_creation_annots(
        &mut self,
        loc: Location,
        rhs_ty: ty::Ty<'tcx>,
    ) -> Vec<radium::Annotation> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let regions_of_ty = self.get_regions_of_ty(rhs_ty);

        let mut annots = Vec::new();

        // Polonius subset constraint are spawned for the midpoint
        let midpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Mid,
        });

        for (s1, s2, point) in subset_base {
            if *point == midpoint {
                let lft1 = self.info.mk_atomic_region(*s1);
                let lft2 = self.info.mk_atomic_region(*s2);

                // a place lifetime is included in a value lifetime
                if lft2.is_value() && lft1.is_place() {
                    // make sure it's not due to an assignment constraint
                    if regions_of_ty.contains(s2) && !subset_base.contains(&(*s2, *s1, midpoint)) {
                        // we enforce this inclusion by setting the lifetimes to be equal
                        self.inclusion_tracker.add_static_inclusion(*s1, *s2, midpoint);
                        self.inclusion_tracker.add_static_inclusion(*s2, *s1, midpoint);

                        let annot = radium::Annotation::CopyLftName(
                            self.format_atomic_region(&lft1),
                            self.format_atomic_region(&lft2),
                        );
                        annots.push(annot);
                    }
                }
            }
        }
        annots
    }

    /**
     * Translate a single basic block.
     */
    fn translate_basic_block(
        &mut self,
        bb_idx: BasicBlock,
        bb: &BasicBlockData<'tcx>,
    ) -> Result<radium::Stmt, TranslationError<'tcx>> {
        // we translate from back to front, starting with the terminator, since Caesium statements
        // have a continuation (the next statement to execute)

        // first do the endlfts for the things right before the terminator
        let mut idx = bb.statements.len();
        let loc = Location {
            block: bb_idx,
            statement_index: idx,
        };
        let dying = self.info.get_dying_loans(loc);
        // TODO zombie?
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        let mut cont_stmt: radium::Stmt = self.translate_terminator(bb.terminator(), loc, dying)?;

        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying);
        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying_zombie);

        for stmt in bb.statements.iter().rev() {
            idx -= 1;
            let loc = Location {
                block: bb_idx,
                statement_index: idx,
            };

            // get all dying loans, and emit endlfts for these.
            // We loop over all predecessor locations, since some loans may end at the start of a
            // basic block (in particular related to NLL stuff)
            let pred = self.get_loc_predecessors(loc);
            let mut dying_loans = HashSet::new();
            for p in pred {
                let dying_between = self.info.get_loans_dying_between(p, loc, false);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
                // also include zombies
                let dying_between = self.info.get_loans_dying_between(p, loc, true);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
            }
            // we prepend them before the current statement

            match &stmt.kind {
                StatementKind::Assign(b) => {
                    let (plc, val) = b.as_ref();

                    if (self.is_spec_closure_local(plc.local)?).is_some() {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    } else if let Some(rewritten_ty) = self.checked_op_temporaries.get(&plc.local) {
                        // if this is a checked op, be sure to remember it
                        info!("rewriting assignment to checked op: {:?}", plc);

                        let synty = self.ty_translator.translate_type_to_syn_type(*rewritten_ty)?;

                        let translated_val = self.translate_rvalue(loc, val)?;
                        let translated_place = self.translate_place(plc)?;

                        // this should be a temporary
                        assert!(plc.projection.is_empty());

                        let ot = synty.into();
                        cont_stmt = radium::Stmt::Assign {
                            ot,
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                    } else {
                        let plc_ty = self.get_type_of_place(plc);
                        let rhs_ty = val.ty(&self.proc.get_mir().local_decls, self.env.tcx());

                        let borrow_annots = self.get_assignment_loan_annots(loc, val);
                        let (expr_annot, pre_stmt_annots, post_stmt_annots) =
                            self.get_assignment_annots(loc, plc, rhs_ty);

                        // TODO; maybe move this to rvalue
                        let composite_annots = self.get_composite_rvalue_creation_annots(loc, rhs_ty);

                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            post_stmt_annots,
                            &Some("post-assignment".to_owned()),
                        );

                        let translated_val = radium::Expr::with_optional_annotation(
                            self.translate_rvalue(loc, val)?,
                            expr_annot,
                            Some("assignment".to_owned()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.ty_translator.translate_type_to_syn_type(plc_ty.ty)?;
                        cont_stmt = radium::Stmt::Assign {
                            ot: synty.into(),
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            pre_stmt_annots,
                            &Some("assignment".to_owned()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            borrow_annots,
                            &Some("borrow".to_owned()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            composite_annots,
                            &Some("composite".to_owned()),
                        );
                    }
                },

                StatementKind::Deinit(_) => {
                    // TODO: find out where this is emitted
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support Deinit".to_owned(),
                    });
                },

                StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                },

                StatementKind::Intrinsic(intrinsic) => {
                    match intrinsic.as_ref() {
                        NonDivergingIntrinsic::Assume(_) => {
                            // ignore
                            info!("Ignoring Assume: {:?}", intrinsic);
                        },
                        NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support the CopyNonOverlapping Intrinsic".to_owned(),
                            });
                        },
                    }
                },

                StatementKind::PlaceMention(place) => {
                    // TODO: this is missed UB
                    info!("Ignoring PlaceMention: {:?}", place);
                },

                StatementKind::SetDiscriminant {
                    place: _place,
                    variant_index: _variant_index,
                } => {
                    // TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support SetDiscriminant".to_owned(),
                    });
                },

                // don't need that info
                | StatementKind::AscribeUserType(_, _)
                // don't need that
                | StatementKind::Coverage(_)
                // no-op
                | StatementKind::ConstEvalCounter
                // ignore
                | StatementKind::Nop
                // just ignore
                | StatementKind::StorageLive(_)
                // just ignore
                | StatementKind::StorageDead(_)
                // just ignore retags
                | StatementKind::Retag(_, _) => (),
            }

            cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.into_iter());
        }

        Ok(cont_stmt)
    }

    /// Translate a `BorrowKind`.
    fn translate_borrow_kind(kind: BorrowKind) -> Result<radium::BorKind, TranslationError<'tcx>> {
        match kind {
            BorrowKind::Shared => Ok(radium::BorKind::Shared),
            BorrowKind::Shallow => {
                // TODO: figure out what to do with this
                // arises in match lowering
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does currently not support shallow borrows".to_owned(),
                })
            },
            BorrowKind::Mut { .. } => {
                // TODO: handle two-phase borrows?
                Ok(radium::BorKind::Mutable)
            },
        }
    }

    const fn translate_mutability(mt: Mutability) -> radium::Mutability {
        match mt {
            Mutability::Mut => radium::Mutability::Mut,
            Mutability::Not => radium::Mutability::Shared,
        }
    }

    /// Get the inner type of a type to which we can apply the offset operator.
    fn get_offset_ty(ty: Ty<'tcx>) -> Result<Ty<'tcx>, TranslationError<'tcx>> {
        match ty.kind() {
            TyKind::Array(t, _) | TyKind::Slice(t) | TyKind::Ref(_, t, _) => Ok(*t),
            TyKind::RawPtr(tm) => Ok(tm.ty),
            _ => Err(TranslationError::UnknownError(format!("cannot take offset of {}", ty))),
        }
    }

    /// Translate binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_binop(
        &self,
        op: BinOp,
        e1: &Operand<'tcx>,
        _e2: &Operand<'tcx>,
    ) -> Result<radium::Binop, TranslationError<'tcx>> {
        match op {
            BinOp::Add | BinOp::AddUnchecked => Ok(radium::Binop::Add),
            BinOp::Sub | BinOp::SubUnchecked => Ok(radium::Binop::Sub),
            BinOp::Mul | BinOp::MulUnchecked => Ok(radium::Binop::Mul),
            BinOp::Div => Ok(radium::Binop::Div),
            BinOp::Rem => Ok(radium::Binop::Mod),

            BinOp::BitXor => Ok(radium::Binop::BitXor),
            BinOp::BitAnd => Ok(radium::Binop::BitAnd),
            BinOp::BitOr => Ok(radium::Binop::BitOr),
            BinOp::Shl | BinOp::ShlUnchecked => Ok(radium::Binop::Shl),
            BinOp::Shr | BinOp::ShrUnchecked => Ok(radium::Binop::Shr),

            BinOp::Eq => Ok(radium::Binop::Eq),
            BinOp::Lt => Ok(radium::Binop::Lt),
            BinOp::Le => Ok(radium::Binop::Le),
            BinOp::Ne => Ok(radium::Binop::Ne),
            BinOp::Ge => Ok(radium::Binop::Ge),
            BinOp::Gt => Ok(radium::Binop::Gt),

            BinOp::Offset => {
                // we need to get the layout of the thing we're offsetting
                // try to get the type of e1.
                let e1_ty = self.get_type_of_operand(e1);
                let off_ty = BodyTranslator::get_offset_ty(e1_ty)?;
                let st = self.ty_translator.translate_type_to_syn_type(off_ty)?;
                let ly = st.into();
                Ok(radium::Binop::PtrOffset(ly))
            },
        }
    }

    /// Translate checked binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_checked_binop(op: BinOp) -> Result<radium::Binop, TranslationError<'tcx>> {
        match op {
            BinOp::Add => Ok(radium::Binop::CheckedAdd),
            BinOp::Sub => Ok(radium::Binop::CheckedSub),
            BinOp::Mul => Ok(radium::Binop::CheckedMul),
            BinOp::Shl => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support checked Shl".to_owned(),
            }),
            BinOp::Shr => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support checked Shr".to_owned(),
            }),
            _ => Err(TranslationError::UnknownError(
                "unexpected checked binop that is not Add, Sub, Mul, Shl, or Shr".to_owned(),
            )),
        }
    }

    /// Translate unary operators.
    fn translate_unop(op: UnOp, ty: Ty<'tcx>) -> Result<radium::Unop, TranslationError<'tcx>> {
        match op {
            UnOp::Not => match ty.kind() {
                ty::TyKind::Bool => Ok(radium::Unop::NotBool),
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Ok(radium::Unop::NotInt),
                _ => Err(TranslationError::UnknownError(
                    "application of UnOp::Not to non-{Int, Bool}".to_owned(),
                )),
            },
            UnOp::Neg => Ok(radium::Unop::Neg),
        }
    }

    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(
        &self,
        bk: BorrowKind,
        pl: &Place<'tcx>,
    ) -> Result<Option<radium::RustType>, TranslationError<'tcx>> {
        let BorrowKind::Mut { .. } = bk else {
            return Ok(None);
        };

        let ty = self.get_type_of_place(pl);

        // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
        let translated_ty = self.ty_translator.translate_type(ty.ty)?;
        let annot_ty = radium::RustType::of_type(&translated_ty);

        Ok(Some(annot_ty))
    }

    /// Translates an Rvalue.
    fn translate_rvalue(
        &mut self,
        loc: Location,
        rval: &Rvalue<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match rval {
            Rvalue::Use(op) => {
                // converts an lvalue to an rvalue
                self.translate_operand(op, true)
            },

            Rvalue::Ref(region, bk, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_bk = BodyTranslator::translate_borrow_kind(*bk)?;
                let ty_annot = self.get_type_annotation_for_borrow(*bk, pl)?;

                if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
                    let atomic_region = self.info.atomic_region_of_loan(loan);
                    let lft = self.format_atomic_region(&atomic_region);
                    Ok(radium::Expr::Borrow {
                        lft,
                        bk: translated_bk,
                        ty: ty_annot,
                        e: Box::new(translated_pl),
                    })
                } else {
                    info!("Didn't find loan at {:?}: {:?}; region {:?}", loc, rval, region);
                    let region = BodyTranslator::region_to_region_vid(*region);
                    let lft = self.format_region(region);

                    Ok(radium::Expr::Borrow {
                        lft,
                        bk: translated_bk,
                        ty: ty_annot,
                        e: Box::new(translated_pl),
                    })
                }
            },

            Rvalue::AddressOf(mt, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_mt = BodyTranslator::translate_mutability(*mt);

                Ok(radium::Expr::AddressOf {
                    mt: translated_mt,
                    e: Box::new(translated_pl),
                })
            },

            Rvalue::BinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1);
                let e2_ty = self.get_type_of_operand(e2);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(e2_ty)?;

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = self.translate_binop(*op, &operands.as_ref().0, &operands.as_ref().1)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_st.into(),
                    ot2: e2_st.into(),
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            Rvalue::CheckedBinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1);
                let e2_ty = self.get_type_of_operand(e2);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(e2_ty)?;

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = BodyTranslator::translate_checked_binop(*op)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_st.into(),
                    ot2: e2_st.into(),
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            Rvalue::UnaryOp(op, operand) => {
                let translated_e1 = self.translate_operand(operand, true)?;
                let e1_ty = self.get_type_of_operand(operand);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let translated_op = BodyTranslator::translate_unop(*op, e1_ty)?;

                Ok(radium::Expr::UnOp {
                    o: translated_op,
                    ot: e1_st.into(),
                    e: Box::new(translated_e1),
                })
            },

            Rvalue::NullaryOp(op, _ty) => {
                // TODO: SizeOf
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does currently not support nullary ops (AlignOf, Sizeof)"
                        .to_owned(),
                })
            },

            Rvalue::Discriminant(pl) => {
                let ty = self.get_type_of_place(pl);
                let translated_pl = self.translate_place(pl)?;
                info!("getting discriminant of {:?} at type {:?}", pl, ty);

                let ty::TyKind::Adt(adt_def, args) = ty.ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support discriminant accesses on non-enum types ({:?}, got {:?})",
                            rval, ty.ty
                        ),
                    });
                };

                let enum_use = self.ty_translator.generate_enum_use(*adt_def, args.iter())?;
                let els = enum_use.generate_raw_syn_type_term();

                let discriminant_acc = radium::Expr::EnumDiscriminant {
                    els: els.to_string(),
                    e: Box::new(translated_pl),
                };

                // need to do a load from this place
                let it = ty.ty.discriminant_ty(self.env.tcx());
                let translated_it = self.ty_translator.translate_type(it)?;

                let radium::Type::Int(translated_it) = translated_it else {
                    return Err(TranslationError::UnknownError(format!(
                        "type of discriminant is not an integer type {:?}",
                        it
                    )));
                };

                let ot = radium::OpType::Int(translated_it);

                Ok(radium::Expr::Use {
                    ot,
                    e: Box::new(discriminant_acc),
                })
            },

            Rvalue::Aggregate(kind, op) => {
                // translate operands
                let mut translated_ops: Vec<radium::Expr> = Vec::new();
                let mut operand_types: Vec<Ty<'tcx>> = Vec::new();

                for o in op {
                    let translated_o = self.translate_operand(o, true)?;
                    let type_of_o = self.get_type_of_operand(o);
                    translated_ops.push(translated_o);
                    operand_types.push(type_of_o);
                }

                match *kind {
                    box mir::AggregateKind::Tuple => {
                        if operand_types.is_empty() {
                            // translate to unit literal
                            return Ok(radium::Expr::Literal(radium::Literal::ZST));
                        }

                        let struct_use =
                            self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                        let sl = struct_use.generate_raw_syn_type_term();
                        let initializers: Vec<_> =
                            translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                        Ok(radium::Expr::StructInitE {
                            sls: coq::term::App::new_lhs(sl.to_string()),
                            components: initializers,
                        })
                    },

                    box mir::AggregateKind::Adt(did, variant, args, ..) => {
                        // get the adt def
                        let adt_def: ty::AdtDef<'tcx> = self.env.tcx().adt_def(did);

                        if adt_def.is_struct() {
                            let variant = adt_def.variant(variant);
                            let struct_use = self.ty_translator.generate_struct_use(variant.def_id, args)?;

                            let Some(struct_use) = struct_use else {
                                // if not, it's replaced by unit
                                return Ok(radium::Expr::Literal(radium::Literal::ZST));
                            };

                            let sl = struct_use.generate_raw_syn_type_term();
                            let initializers: Vec<_> = translated_ops
                                .into_iter()
                                .zip(variant.fields.iter())
                                .map(|(o, field)| (field.name.to_string(), o))
                                .collect();

                            return Ok(radium::Expr::StructInitE {
                                sls: coq::term::App::new_lhs(sl.to_string()),
                                components: initializers,
                            });
                        }

                        if adt_def.is_enum() {
                            let variant_def = adt_def.variant(variant);

                            let struct_use =
                                self.ty_translator.generate_enum_variant_use(variant_def.def_id, args)?;
                            let sl = struct_use.generate_raw_syn_type_term();

                            let initializers: Vec<_> = translated_ops
                                .into_iter()
                                .zip(variant_def.fields.iter())
                                .map(|(o, field)| (field.name.to_string(), o))
                                .collect();

                            let variant_e = radium::Expr::StructInitE {
                                sls: coq::term::App::new_lhs(sl.to_string()),
                                components: initializers,
                            };

                            let enum_use = self.ty_translator.generate_enum_use(adt_def, args)?;
                            let els = enum_use.generate_raw_syn_type_term();

                            info!("generating enum annotation for type {:?}", enum_use);
                            let ty = radium::RustType::of_type(&radium::Type::Literal(enum_use));
                            let variant_name = variant_def.name.to_string();

                            return Ok(radium::Expr::EnumInitE {
                                els: coq::term::App::new_lhs(els.to_string()),
                                variant: variant_name,
                                ty,
                                initializer: Box::new(variant_e),
                            });
                        }

                        // TODO
                        Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support aggregate rvalue for other ADTs (got: {:?})",
                                rval
                            ),
                        })
                    },
                    box mir::AggregateKind::Closure(def, _args) => {
                        trace!("Translating Closure aggregate value for {:?}", def);

                        // We basically translate this to a tuple
                        if operand_types.is_empty() {
                            // translate to unit literal
                            return Ok(radium::Expr::Literal(radium::Literal::ZST));
                        }

                        let struct_use =
                            self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                        let sl = struct_use.generate_raw_syn_type_term();

                        let initializers: Vec<_> =
                            translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                        Ok(radium::Expr::StructInitE {
                            sls: coq::term::App::new_lhs(sl.to_string()),
                            components: initializers,
                        })
                    },

                    _ => {
                        // TODO
                        Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support this kind of aggregate rvalue (got: {:?})",
                                rval
                            ),
                        })
                    },
                }
            },

            Rvalue::Cast(kind, op, to_ty) => {
                let op_ty = self.get_type_of_operand(op);
                let op_st = self.ty_translator.translate_type_to_syn_type(op_ty)?;
                let op_ot = op_st.into();

                let translated_op = self.translate_operand(op, true)?;

                let target_st = self.ty_translator.translate_type_to_syn_type(*to_ty)?;
                let target_ot = target_st.into();

                match kind {
                    mir::CastKind::PointerCoercion(x) => {
                        match x {
                            ty::adjustment::PointerCoercion::MutToConstPointer => {
                                // this is a NOP in our model
                                Ok(translated_op)
                            },

                            ty::adjustment::PointerCoercion::ArrayToPointer
                            | ty::adjustment::PointerCoercion::ClosureFnPointer(_)
                            | ty::adjustment::PointerCoercion::ReifyFnPointer
                            | ty::adjustment::PointerCoercion::UnsafeFnPointer
                            | ty::adjustment::PointerCoercion::Unsize => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!(
                                        "RefinedRust does currently not support this kind of pointer coercion (got: {:?})",
                                        rval
                                    ),
                                })
                            },
                        }
                    },

                    mir::CastKind::DynStar => Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support dyn* cast".to_owned(),
                    }),

                    mir::CastKind::IntToInt => {
                        // Cast integer to integer
                        Ok(radium::Expr::UnOp {
                            o: radium::Unop::Cast(target_ot),
                            ot: op_ot,
                            e: Box::new(translated_op),
                        })
                    },

                    mir::CastKind::IntToFloat => Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support int-to-float cast".to_owned(),
                    }),

                    mir::CastKind::FloatToInt => Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support float-to-int cast".to_owned(),
                    }),

                    mir::CastKind::FloatToFloat => Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support float-to-float cast".to_owned(),
                    }),

                    mir::CastKind::PtrToPtr => {
                        match (op_ty.kind(), to_ty.kind()) {
                            (TyKind::RawPtr(_), TyKind::RawPtr(_)) => {
                                // Casts between raw pointers are NOPs for us
                                Ok(translated_op)
                            },

                            _ => {
                                // TODO: any other cases we should handle?
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!(
                                        "RefinedRust does currently not support ptr-to-ptr cast (got: {:?})",
                                        rval
                                    ),
                                })
                            },
                        }
                    },

                    mir::CastKind::FnPtrToPtr => Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support fnptr-to-ptr cast (got: {:?})",
                            rval
                        ),
                    }),

                    mir::CastKind::Transmute => Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support transmute cast (got: {:?})",
                            rval
                        ),
                    }),

                    mir::CastKind::PointerExposeAddress => {
                        // Cast pointer to integer
                        Ok(radium::Expr::UnOp {
                            o: radium::Unop::Cast(target_ot),
                            ot: radium::OpType::Ptr,
                            e: Box::new(translated_op),
                        })
                    },

                    mir::CastKind::PointerFromExposedAddress => Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support this kind of cast (got: {:?})",
                            rval
                        ),
                    }),
                }
            },

            Rvalue::CopyForDeref(_)
            | Rvalue::Len(..)
            | Rvalue::Repeat(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::ShallowInitBox(_, _) => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of rvalue (got: {:?})",
                    rval
                ),
            }),
        }
    }

    /// Make a trivial place accessing `local`.
    fn make_local_place(&self, local: Local) -> Place<'tcx> {
        Place {
            local,
            projection: self.env.tcx().mk_place_elems(&[]),
        }
    }

    /// Translate an operand.
    /// This will either generate an lvalue (in case of Move or Copy) or an rvalue (in most cases
    /// of Constant). How this is used depends on the context. (e.g., Use of an integer constant
    /// does not typecheck, and produces a stuck program).
    fn translate_operand(
        &mut self,
        op: &Operand<'tcx>,
        to_rvalue: bool,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match op {
            // In Caesium: typed_place needs deref (not use) for place accesses.
            // use is used top-level to convert an lvalue to an rvalue, which is why we use it here.
            Operand::Copy(place) | Operand::Move(place) => {
                // check if this goes to a temporary of a checked op
                let place_kind = if self.checked_op_temporaries.contains_key(&place.local) {
                    assert!(place.projection.len() == 1);

                    let ProjectionElem::Field(f, _0) = place.projection[0] else {
                        unreachable!("invariant violation for access to checked op temporary");
                    };

                    if f.index() != 0 {
                        // make this a constant false -- our semantics directly checks for overflows
                        // and otherwise throws UB.
                        return Ok(radium::Expr::Literal(radium::Literal::Bool(false)));
                    }

                    // access to the result of the op
                    self.make_local_place(place.local)
                } else {
                    *place
                };

                let translated_place = self.translate_place(&place_kind)?;
                let ty = self.get_type_of_place(place);

                let st = self.ty_translator.translate_type_to_syn_type(ty.ty)?;

                if to_rvalue {
                    Ok(radium::Expr::Use {
                        ot: st.into(),
                        e: Box::new(translated_place),
                    })
                } else {
                    Ok(translated_place)
                }
            },
            Operand::Constant(constant) => {
                // TODO: possibly need different handling of the rvalue flag
                // when this also handles string literals etc.
                return self.translate_constant(constant.as_ref());
            },
        }
    }

    /// Translate the use of an `FnDef`, registering that the current function needs to link against
    /// a particular monomorphization of the used function.
    /// Is guaranteed to return a `radium::Expr::CallTarget` with the parameter instantiation of
    /// this function annotated.
    fn translate_fn_def_use(&mut self, ty: Ty<'tcx>) -> Result<radium::Expr, TranslationError<'tcx>> {
        let TyKind::FnDef(defid, params) = ty.kind() else {
            return Err(TranslationError::UnknownError("not a FnDef type".to_owned()));
        };

        let key: ty::ParamEnv<'tcx> = self.env.tcx().param_env(self.proc.get_id());

        let callee_param_env = self.env.tcx().param_env(defid);
        info!("callee param env {callee_param_env:?}");

        // Get the trait requirements of the callee
        let callee_requirements = get_nontrivial_trait_requirements(self.env.tcx(), callee_param_env);
        info!("non-trivial callee requirements: {callee_requirements:?}");
        info!("subsituting with args {:?}", params);

        // Check whether we are calling into a trait method
        let calling_trait = self.env.tcx().trait_of_item(*defid);
        // Get the params of the trait we're calling
        let calling_trait_params = if let Some(trait_did) = calling_trait {
            Some(LocalTypeTranslator::split_trait_method_args(self.env, trait_did, params).0)
        } else {
            None
        };

        // For each trait requirement, resolve to a trait spec that we can provide
        // TODO: make sure to provide the list of trait instantiations in a consistent order with the callee
        // defining site
        let mut trait_spec_terms = Vec::new();
        // also compute the translated associated types of all trait instances this function depends on
        let mut ordered_assoc_tys = Vec::new();
        for trait_ref in &callee_requirements {
            // substitute the args with the arg instantiation of the callee at this call site
            // in order to get the args of this trait instance
            let args = trait_ref.args;
            let mut subst_args = Vec::new();
            for arg in args {
                let bound = ty::EarlyBinder::bind(arg);
                let bound = bound.instantiate(self.env.tcx(), params.as_slice());
                subst_args.push(bound);
            }

            // Check if the target of our call is a method of the same trait with the same args
            // Since this happens in the same ParamEnv, this is the assumption of the trait method
            // for its own trait, so we skip it.
            if let Some(trait_did) = calling_trait {
                if trait_ref.def_id == trait_did && subst_args == calling_trait_params.unwrap().as_slice() {
                    // if they match, this is the Self assumption, so skip
                    continue;
                }
            }

            // try to infer an instance for this
            let subst_args = self.env.tcx().mk_args(subst_args.as_slice());
            if let Some((impl_did, impl_args, kind)) =
                traits::resolve_trait(self.env.tcx(), key, trait_ref.def_id, subst_args)
            {
                info!("resolved trait impl as {impl_did:?} with {args:?} {kind:?}");

                match kind {
                    traits::TraitResolutionKind::UserDefined => {
                        // we can resolve it to a concrete implementation of the trait that the
                        // call links up against
                        // therefore, we specialize it to the specification for this implementation
                        //
                        // This is sound, as the compiler will make the same choice when resolving
                        // the trait reference in codegen

                        let (spec_term, assoc_tys) = self.trait_registry.get_impl_spec_term(
                            &self.ty_translator,
                            impl_did,
                            impl_args.as_slice(),
                            subst_args.as_slice(),
                        )?;
                        trait_spec_terms.push(spec_term);

                        ordered_assoc_tys.extend(assoc_tys.into_iter());
                    },
                    traits::TraitResolutionKind::Param => {
                        // Lookup in our current parameter environment to satisfy this trait
                        // assumption
                        let trait_did = trait_ref.def_id;

                        let assoc_types_did = self.env.get_trait_assoc_types(trait_did);
                        let mut assoc_types = Vec::new();
                        for did in assoc_types_did {
                            let alias = self.env.tcx().mk_alias_ty(did, subst_args);
                            let tykind = ty::TyKind::Alias(ty::AliasKind::Projection, alias);
                            let ty = self.env.tcx().mk_ty_from_kind(tykind);
                            assoc_types.push(ty);
                        }
                        info!("Param associated types: {:?}", assoc_types);
                        let trait_ref =
                            self.ty_translator.lookup_trait_param(self.env, trait_did, subst_args)?;
                        //let assoc_tys = trait_ref.get_associated_type_uses(self.env);

                        // TODO: do we have to requantify here?
                        // I guess for HRTBs we might need to requantify lifetimes

                        trait_spec_terms.push(radium::SpecializedTraitSpec::new_with_params(
                            trait_ref.trait_use.make_spec_param_name(),
                            None,
                            trait_ref.trait_use.make_spec_attrs_param_name(),
                            false,
                        ));

                        ordered_assoc_tys.extend(assoc_types.into_iter());
                    },
                    traits::TraitResolutionKind::Closure => {
                        // The callee requires a closure trait bound.
                        // This happens when we pass a closure as an argument?
                        return Err(TranslationError::UnsupportedFeature {
                            description: "TODO: do not support Closure parameters".to_owned(),
                        });
                    },
                }
            } else {
                //return Err(TranslationError::TraitResolution(
                //"could not resolve trait required for method call".to_owned(),
                //));
            }
        }
        info!("collected spec terms: {trait_spec_terms:?}");

        // Check whether we are calling a plain function or a trait method
        let Some(calling_trait) = calling_trait else {
            // track that we are using this function and generate the Coq location name
            let (code_param_name, ty_hint, lft_hint) =
                self.register_use_procedure(*defid, vec![], params, trait_spec_terms, &ordered_assoc_tys)?;

            let ty_hint = ty_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

            return Ok(radium::Expr::CallTarget(code_param_name, ty_hint, lft_hint));
        };

        // Otherwise, we are calling a trait method
        // Resolve the trait instance using trait selection
        let Some((resolved_did, resolved_params, kind)) =
            traits::resolve_assoc_item(self.env.tcx(), key, *defid, params)
        else {
            return Err(TranslationError::TraitResolution(format!("Could not resolve trait {:?}", defid)));
        };

        info!(
            "Resolved trait method {:?} as {:?} with substs {:?} and kind {:?}",
            defid, resolved_did, resolved_params, kind
        );

        match kind {
            traits::TraitResolutionKind::UserDefined => {
                // We can statically resolve the particular trait instance,
                // but need to apply the spec to the instance's spec attributes

                let (param_name, ty_hint, lft_hint) = self.register_use_procedure(
                    resolved_did,
                    vec![],
                    resolved_params,
                    trait_spec_terms,
                    &ordered_assoc_tys,
                )?;
                let ty_hint = ty_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(param_name, ty_hint, lft_hint))
            },

            traits::TraitResolutionKind::Param => {
                // In this case, we have already applied it to the spec attribute

                let (param_name, ty_hint, lft_hint) = self.register_use_trait_method(
                    resolved_did,
                    resolved_params,
                    trait_spec_terms,
                    &ordered_assoc_tys,
                )?;
                let ty_hint = ty_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(param_name, ty_hint, lft_hint))
            },

            traits::TraitResolutionKind::Closure => {
                // TODO: here, we should first generate an instance of the trait
                //let body = self.env.tcx().instance_mir(middle::ty::InstanceDef::Item(resolved_did));
                //let body = self.env.tcx().instance_mir(middle::ty::InstanceDef::FnPtrShim(*defid, ty));
                //info!("closure body: {:?}", body);

                //FunctionTranslator::dump_body(body);

                //let res_result = ty::Instance::resolve(self.env.tcx(), callee_param_env, *defid, params);
                //info!("Resolution {:?}", res_result);

                // the args are just the closure args. We can ignore them.
                let _clos_args = resolved_params.as_closure();

                let (param_name, ty_hint, lft_hint) = self.register_use_procedure(
                    resolved_did,
                    vec![],
                    ty::List::empty(),
                    trait_spec_terms,
                    &ordered_assoc_tys,
                )?;
                let ty_hint = ty_hint.into_iter().map(|x| radium::RustType::of_type(&x)).collect();

                Ok(radium::Expr::CallTarget(param_name, ty_hint, lft_hint))
            },
        }
    }

    /// Translate a scalar at a specific type to a `radium::Expr`.
    // TODO: Use `TryFrom` instead
    fn translate_scalar(
        &mut self,
        sc: &Scalar,
        ty: Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        // TODO: Use `TryFrom` instead
        fn translate_literal<'tcx, T, U>(
            sc: Result<T, U>,
            fptr: fn(T) -> radium::Literal,
        ) -> Result<radium::Expr, TranslationError<'tcx>> {
            sc.map_or(Err(TranslationError::InvalidLayout), |lit| Ok(radium::Expr::Literal(fptr(lit))))
        }

        match ty.kind() {
            TyKind::Bool => translate_literal(sc.to_bool(), radium::Literal::Bool),

            TyKind::Int(it) => match it {
                ty::IntTy::I8 => translate_literal(sc.to_i8(), radium::Literal::I8),
                ty::IntTy::I16 => translate_literal(sc.to_i16(), radium::Literal::I16),
                ty::IntTy::I32 => translate_literal(sc.to_i32(), radium::Literal::I32),
                ty::IntTy::I128 => translate_literal(sc.to_i128(), radium::Literal::I128),

                // For Radium, the pointer size is 8 bytes
                ty::IntTy::I64 | ty::IntTy::Isize => translate_literal(sc.to_i64(), radium::Literal::I64),
            },

            TyKind::Uint(it) => match it {
                ty::UintTy::U8 => translate_literal(sc.to_u8(), radium::Literal::U8),
                ty::UintTy::U16 => translate_literal(sc.to_u16(), radium::Literal::U16),
                ty::UintTy::U32 => translate_literal(sc.to_u32(), radium::Literal::U32),
                ty::UintTy::U128 => translate_literal(sc.to_u128(), radium::Literal::U128),

                // For Radium, the pointer is 8 bytes
                ty::UintTy::U64 | ty::UintTy::Usize => translate_literal(sc.to_u64(), radium::Literal::U64),
            },

            TyKind::Char => translate_literal(sc.to_char(), radium::Literal::Char),

            TyKind::FnDef(_, _) => self.translate_fn_def_use(ty),

            TyKind::Tuple(tys) => {
                if tys.is_empty() {
                    return Ok(radium::Expr::Literal(radium::Literal::ZST));
                }

                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support compound construction of tuples using literals (got: {:?})",
                        ty
                    ),
                })
            },

            TyKind::Ref(_, _, _) => match sc {
                Scalar::Int(_) => unreachable!(),

                Scalar::Ptr(pointer, _) => {
                    let glob_alloc = self.env.tcx().global_alloc(pointer.provenance);
                    match glob_alloc {
                        middle::mir::interpret::GlobalAlloc::Static(did) => {
                            info!(
                                "Found static GlobalAlloc {:?} for Ref scalar {:?} at type {:?}",
                                did, sc, ty
                            );

                            let Some(s) = self.const_registry.statics.get(&did) else {
                                return Err(TranslationError::UnknownError(format!(
                                    "Did not find a registered static for GlobalAlloc {:?} for scalar {:?} at type {:?}; registered: {:?}",
                                    glob_alloc, sc, ty, self.const_registry.statics
                                )));
                            };

                            self.collected_statics.insert(did);
                            Ok(radium::Expr::Literal(radium::Literal::Loc(s.loc_name.clone())))
                        },
                        middle::mir::interpret::GlobalAlloc::Memory(alloc) => {
                            // TODO: this is needed
                            Err(TranslationError::UnsupportedFeature {
                                description: format!(
                                    "RefinedRust does currently not support GlobalAlloc {:?} for scalar {:?} at type {:?}",
                                    glob_alloc, sc, ty
                                ),
                            })
                        },
                        _ => Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support GlobalAlloc {:?} for scalar {:?} at type {:?}",
                                glob_alloc, sc, ty
                            ),
                        }),
                    }
                },
            },

            _ => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support layout for const value: (got: {:?})",
                    ty
                ),
            }),
        }
    }

    /// Translate a constant value from const evaluation.
    fn translate_constant_value(
        &mut self,
        v: mir::interpret::ConstValue<'tcx>,
        ty: Ty<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match v {
            ConstValue::Scalar(sc) => self.translate_scalar(&sc, ty),
            ConstValue::ZeroSized => {
                // TODO are there more special cases we need to handle somehow?
                match ty.kind() {
                    TyKind::FnDef(_, _) => {
                        info!("Translating ZST val for function call target: {:?}", ty);
                        self.translate_fn_def_use(ty)
                    },
                    _ => Ok(radium::Expr::Literal(radium::Literal::ZST)),
                }
            },
            _ => {
                // TODO: do we actually care about this case or is this just something that can
                // appear as part of CTFE/MIRI?
                Err(TranslationError::UnsupportedFeature {
                    description: format!("Unsupported Constant: ConstValue; {:?}", v),
                })
            },
        }
    }

    /// Translate a Constant to a `radium::Expr`.
    fn translate_constant(
        &mut self,
        constant: &Constant<'tcx>,
    ) -> Result<radium::Expr, TranslationError<'tcx>> {
        match constant.literal {
            ConstantKind::Ty(v) => {
                let const_ty = v.ty();

                match v.kind() {
                    ConstKind::Value(v) => {
                        // this doesn't contain the necessary structure anymore. Need to reconstruct using the
                        // type.
                        match v.try_to_scalar() {
                            Some(sc) => self.translate_scalar(&sc, const_ty),
                            _ => Err(TranslationError::UnsupportedFeature {
                                description: format!("const value not supported: {:?}", v),
                            }),
                        }
                    },
                    _ => Err(TranslationError::UnsupportedFeature {
                        description: "Unsupported ConstKind".to_owned(),
                    }),
                }
            },
            ConstantKind::Val(val, ty) => self.translate_constant_value(val, ty),
            ConstantKind::Unevaluated(c, ty) => {
                // call const evaluation
                let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(self.proc.get_id());
                match self.env.tcx().const_eval_resolve(param_env, c, None) {
                    Ok(res) => self.translate_constant_value(res, ty),
                    Err(e) => match e {
                        ErrorHandled::Reported(_) => Err(TranslationError::UnsupportedFeature {
                            description: "Cannot interpret constant".to_owned(),
                        }),
                        ErrorHandled::TooGeneric => Err(TranslationError::UnsupportedFeature {
                            description: "Const use is too generic".to_owned(),
                        }),
                    },
                }
            },
        }
    }

    /// Translate a place to a Caesium lvalue.
    fn translate_place(&mut self, pl: &Place<'tcx>) -> Result<radium::Expr, TranslationError<'tcx>> {
        // Get the type of the underlying local. We will use this to
        // get the necessary layout information for dereferencing
        let mut cur_ty = self.get_type_of_local(pl.local).map(PlaceTy::from_ty)?;

        let local_name = self
            .variable_map
            .get(&pl.local)
            .ok_or_else(|| TranslationError::UnknownVar(format!("{:?}", pl.local)))?;

        let mut acc_expr = radium::Expr::Var(local_name.to_string());

        // iterate in evaluation order
        for it in pl.projection {
            match &it {
                ProjectionElem::Deref => {
                    // use the type of the dereferencee
                    let st = self.ty_translator.translate_type_to_syn_type(cur_ty.ty)?;
                    acc_expr = radium::Expr::Deref {
                        ot: st.into(),
                        e: Box::new(acc_expr),
                    };
                },
                ProjectionElem::Field(f, _) => {
                    // `t` is the type of the field we are accessing!
                    let lit = self.ty_translator.generate_structlike_use(cur_ty.ty, cur_ty.variant_index)?;
                    // TODO: does not do the right thing for accesses to fields of zero-sized objects.
                    let struct_sls = lit.map_or(radium::SynType::Unit, |x| x.generate_raw_syn_type_term());
                    let name = self.ty_translator.translator.get_field_name_of(
                        *f,
                        cur_ty.ty,
                        cur_ty.variant_index.map(abi::VariantIdx::as_usize),
                    )?;

                    acc_expr = radium::Expr::FieldOf {
                        e: Box::new(acc_expr),
                        name,
                        sls: struct_sls.to_string(),
                    };
                },
                ProjectionElem::Index(_v) => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement index access".to_owned(),
                    });
                },
                ProjectionElem::ConstantIndex { .. } => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement const index access".to_owned(),
                    });
                },
                ProjectionElem::Subslice { .. } => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement subslicing".to_owned(),
                    });
                },
                ProjectionElem::Downcast(_, variant_idx) => {
                    info!("Downcast of ty {:?} to {:?}", cur_ty, variant_idx);
                    if let ty::TyKind::Adt(def, args) = cur_ty.ty.kind() {
                        if def.is_enum() {
                            let enum_use = self.ty_translator.generate_enum_use(*def, args.iter())?;
                            let els = enum_use.generate_raw_syn_type_term();

                            let variant_name = TypeTranslator::get_variant_name_of(cur_ty.ty, *variant_idx)?;

                            acc_expr = radium::Expr::EnumData {
                                els: els.to_string(),
                                variant: variant_name,
                                e: Box::new(acc_expr),
                            }
                        } else {
                            return Err(TranslationError::UnknownError(
                                "places: ADT downcasting on non-enum type".to_owned(),
                            ));
                        }
                    } else {
                        return Err(TranslationError::UnknownError(
                            "places: ADT downcasting on non-enum type".to_owned(),
                        ));
                    }
                },
                ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement opaque casts".to_owned(),
                    });
                },
            };
            // update cur_ty
            cur_ty = cur_ty.projection_ty(self.env.tcx(), it);
        }
        info!("translating place {:?} to {:?}", pl, acc_expr);
        Ok(acc_expr)
    }

    /// Get the type of a local in a body.
    fn get_type_of_local(&self, local: Local) -> Result<Ty<'tcx>, TranslationError<'tcx>> {
        self.proc
            .get_mir()
            .local_decls
            .get(local)
            .map(|decl| decl.ty)
            .ok_or_else(|| TranslationError::UnknownVar(String::new()))
    }

    /// Get the type of a place expression.
    fn get_type_of_place(&self, pl: &Place<'tcx>) -> PlaceTy<'tcx> {
        pl.ty(&self.proc.get_mir().local_decls, self.env.tcx())
    }

    /// Get the type of a const.
    fn get_type_of_const(cst: &Constant<'tcx>) -> Ty<'tcx> {
        match cst.literal {
            ConstantKind::Ty(cst) => cst.ty(),
            ConstantKind::Val(_, ty) | ConstantKind::Unevaluated(_, ty) => ty,
        }
    }

    /// Get the type of an operand.
    fn get_type_of_operand(&self, op: &Operand<'tcx>) -> Ty<'tcx> {
        op.ty(&self.proc.get_mir().local_decls, self.env.tcx())
    }
}
