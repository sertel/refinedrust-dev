// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, HashMap, HashSet};

use log::{info, trace, warn};
use radium;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::tcx::PlaceTy;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, Constant, ConstantKind, Local, LocalKind, Location,
    Mutability, Operand, Place, ProjectionElem, Rvalue, StatementKind, Terminator, TerminatorKind, UnOp,
    VarDebugInfoContents,
};
use rustc_middle::ty::fold::TypeFolder;
use rustc_middle::ty::{ConstKind, Ty, TyKind};
use rustc_middle::{mir, ty};

use crate::arg_folder::*;
pub use crate::base::*;
use crate::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::environment::{polonius_info as info, Environment};
use crate::inclusion_tracker::*;
use crate::rustc_middle::ty::TypeFoldable;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, FunctionSpecParser, VerboseFunctionSpecParser,
};
use crate::type_translator::*;
use crate::tyvars::*;

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
    pub fn is_prove(&self) -> bool {
        *self == Self::Prove
    }

    pub fn is_only_spec(&self) -> bool {
        *self == Self::OnlySpec
    }

    pub fn is_trust_me(&self) -> bool {
        *self == Self::TrustMe
    }

    pub fn is_shim(&self) -> bool {
        *self == Self::Shim
    }

    pub fn is_ignore(&self) -> bool {
        *self == Self::Ignore
    }

    pub fn needs_proof(&self) -> bool {
        *self == Self::Prove
    }

    pub fn needs_def(&self) -> bool {
        *self == Self::Prove || *self == Self::TrustMe
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
    specced_functions: BTreeMap<DefId, radium::FunctionSpec<'def>>,
}

impl<'def> ProcedureScope<'def> {
    pub fn new() -> Self {
        Self {
            name_map: BTreeMap::new(),
            translated_functions: BTreeMap::new(),
            specced_functions: BTreeMap::new(),
        }
    }

    pub fn lookup_function(&self, did: &DefId) -> Option<ProcedureMeta> {
        self.name_map.get(did).cloned()
    }

    /// Lookup the Coq spec name for a function.
    pub fn lookup_function_spec_name(&self, did: &DefId) -> Option<&str> {
        self.name_map.get(did).map(|m| m.get_spec_name())
    }

    /// Lookup the name for a function.
    pub fn lookup_function_mangled_name(&self, did: &DefId) -> Option<&str> {
        self.name_map.get(did).map(|m| m.get_name())
    }

    /// Lookup the mode for a function.
    pub fn lookup_function_mode(&self, did: &DefId) -> Option<ProcedureMode> {
        self.name_map.get(did).map(|m| m.get_mode())
    }

    /// Register a function.
    pub fn register_function(&mut self, did: &DefId, meta: ProcedureMeta) -> Result<(), String> {
        if let Some(_) = self.name_map.insert(*did, meta) {
            Err(format!("function for defid {:?} has already been registered", did))
        } else {
            Ok(())
        }
    }

    /// Provide the code for a translated function.
    pub fn provide_translated_function(&mut self, did: &DefId, trf: radium::Function<'def>) {
        let meta = self.name_map.get(did).unwrap();
        assert!(meta.get_mode().needs_def());
        assert!(self.translated_functions.insert(*did, trf).is_none());
    }

    /// Provide the specification for an only_spec function.
    pub fn provide_specced_function(&mut self, did: &DefId, spec: radium::FunctionSpec<'def>) {
        let meta = self.name_map.get(did).unwrap();
        assert!(meta.get_mode().is_only_spec());
        assert!(self.specced_functions.insert(*did, spec).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub fn iter_code(&self) -> std::collections::btree_map::Iter<'_, DefId, radium::Function<'def>> {
        self.translated_functions.iter()
    }

    /// Iterate over the functions we have generated only specs for.
    pub fn iter_only_spec(&self) -> std::collections::btree_map::Iter<'_, DefId, radium::FunctionSpec<'def>> {
        self.specced_functions.iter()
    }
}

/// Scope of consts that are available
pub struct ConstScope<'def> {
    pub statics: HashMap<DefId, radium::StaticMeta<'def>>,
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
    attrs: &'a [&'a rustc_ast::ast::AttrItem],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// translator for types
    ty_translator: LocalTypeTranslator<'a, 'def, 'tcx>,
    /// argument types (from the signature, with generics substituted)
    inputs: Vec<Ty<'tcx>>,
}

impl<'a, 'def: 'a, 'tcx: 'def> FunctionTranslator<'a, 'def, 'tcx> {
    pub fn process_lifetimes_of_args(
        env: &Environment<'tcx>,
        params: &[ty::GenericArg<'tcx>],
        sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
        _body: &mir::Body<'tcx>,
    ) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, HashMap<ty::RegionVid, (String, Option<String>)>) {
        let mut universal_lifetimes = HashMap::new();

        // we create a substitution that replaces early bound regions with their Polonius
        // region variables
        let mut subst_early_bounds: Vec<ty::GenericArg<'tcx>> = Vec::new();
        let mut num_early_bounds = 0;
        for a in params {
            match a.unpack() {
                ty::GenericArgKind::Lifetime(r) => {
                    // skip over 0 = static
                    let next_id = ty::RegionVid::from_u32(num_early_bounds + 1);
                    let revar = ty::Region::new_var(env.tcx(), next_id);
                    num_early_bounds += 1;
                    subst_early_bounds.push(ty::GenericArg::from(revar));

                    match *r {
                        ty::RegionKind::ReEarlyBound(r) => {
                            let name = strip_coq_ident(r.name.as_str());
                            universal_lifetimes.insert(next_id, (format!("ulft_{}", name), Some(name)));
                        },
                        _ => {
                            universal_lifetimes.insert(next_id, (format!("ulft_{}", num_early_bounds), None));
                        },
                    }
                },
                _ => {
                    subst_early_bounds.push(*a);
                },
            }
        }
        let subst_early_bounds = env.tcx().mk_args(&subst_early_bounds);

        // add names for late bound region variables
        let mut num_late_bounds = 0;
        for b in sig.bound_vars() {
            let next_id = ty::RegionVid::from_u32(num_early_bounds + num_late_bounds + 1);
            match b {
                ty::BoundVariableKind::Region(r) => {
                    match r {
                        ty::BoundRegionKind::BrNamed(_, sym) => {
                            let mut region_name = strip_coq_ident(sym.as_str());
                            if region_name == "_" {
                                region_name = format!("{}", next_id.as_usize());
                                universal_lifetimes.insert(next_id, (format!("ulft_{}", region_name), None));
                            } else {
                                universal_lifetimes
                                    .insert(next_id, (format!("ulft_{}", region_name), Some(region_name)));
                            }
                        },
                        ty::BoundRegionKind::BrAnon(_) => {
                            universal_lifetimes
                                .insert(next_id, (format!("ulft_{}", next_id.as_usize()), None));
                        },
                        _ => (),
                    }
                    num_late_bounds += 1;
                },
                _ => (),
            }
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

        (inputs, output, universal_lifetimes)
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

        for (ref r1, ref r2, ref p) in &info.borrowck_in_facts.subset_base {
            if *p == root_point && *r2 == r {
                info!("find placeholder region for: {:?} ⊑ {:?} = r = {:?}", r1, r2, r);
                return Some(*r1);
            }
        }
        None
    }

    /// Create a translation instance for a closure.
    pub fn new_closure(
        env: &'def Environment<'tcx>,
        meta: ProcedureMeta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a rustc_ast::ast::AttrItem],
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        proc_registry: &'a ProcedureScope<'def>,
        const_registry: &'a ConstScope<'def>,
    ) -> Result<Self, TranslationError> {
        let mut translated_fn = radium::FunctionBuilder::new(&meta.name, &meta.spec_name);

        // TODO can we avoid the leak
        let proc: &'def Procedure = &*Box::leak(Box::new(proc));
        let body = proc.get_mir();
        Self::dump_body(&body);

        let closure_kind;

        let ty: ty::EarlyBinder<Ty<'tcx>> = env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();
        match ty.kind() {
            TyKind::Closure(_def, closure_args) => {
                assert!(ty.is_closure());
                let clos = closure_args.as_closure();

                closure_kind = clos.kind();
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
            sig = normalize_in_function(proc.get_id(), env.tcx(), unnormalized_sig)?;
            info!("closure sig: {:?}", sig);

            captures = env.tcx().closure_captures(did.as_local().unwrap());
            info!("Closure has captures: {:?}", captures);

            // find additional lifetime parameters
            for (place, ty) in captures.iter().zip(clos.upvar_tys().iter()) {
                if let Some(_) = place.region {
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
                    crate::environment::dump_borrowck_info(env, &proc.get_id(), &info);
                }

                let (tupled_inputs, output, mut universal_lifetimes) =
                    Self::process_lifetimes_of_args(&env, params, sig, body);

                // Process the lifetime parameters that come from the captures
                for r in capture_regions {
                    // TODO: problem: we're introducing inconsistent names here.
                    if let ty::RegionKind::ReVar(r) = r.kind() {
                        let lft = info.mk_atomic_region(r);
                        let name = format_atomic_region_direct(&lft, None);
                        universal_lifetimes.insert(r, (name, None));
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
                        universal_lifetimes.insert(r2, (name, None));

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
                info!("Have lifetime parameters: {:?}", universal_lifetimes);

                // add universal lifetimes to the spec
                for (lft, name) in universal_lifetimes.values() {
                    //let lft = info::AtomicRegion::Universal(info::UniversalRegionKind::Local,
                    // ty::RegionVid::from_u32(1+r));
                    translated_fn
                        .add_universal_lifetime(name.clone(), lft.to_string())
                        .map_err(|e| TranslationError::UnknownError(e))?;
                }

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

                // enter the procedure
                let universal_lifetime_map: HashMap<_, _> =
                    universal_lifetimes.into_iter().map(|(x, y)| (x, y.0)).collect();
                let type_scope = TypeTranslationScope::new(
                    proc.get_id(),
                    env.tcx().mk_args(params),
                    universal_lifetime_map,
                )?;
                // add generic args to the fn
                let generics = &type_scope.generic_scope;
                for t in generics.iter().flatten() {
                    translated_fn.add_generic_type(t.clone());
                }

                let mut t = Self {
                    env,
                    proc,
                    info,
                    translated_fn,
                    inclusion_tracker,
                    procedure_registry: proc_registry,
                    attrs,
                    ty_translator: LocalTypeTranslator::new(ty_translator, type_scope),
                    const_registry,
                    inputs: inputs.clone(),
                };

                // add universal constraints
                let universal_constraints = t.get_relevant_universal_constraints();
                info!("univeral constraints: {:?}", universal_constraints);
                for (lft1, lft2) in universal_constraints {
                    t.translated_fn
                        .add_universal_lifetime_constraint(lft1, lft2)
                        .map_err(|e| TranslationError::UnknownError(e))?;
                }

                // compute meta information needed to generate the spec
                let mut translated_upvars_types = Vec::new();
                for ty in upvars_tys {
                    let translated_ty = t.ty_translator.translate_type(&ty)?;
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
                            .map(|x| scope.lookup_universal_region(x).unwrap()),
                    };
                }

                // process attributes
                t.process_closure_attrs(&inputs, &output, meta)?;
                Ok(t)
            },
            Err(err) => Err(TranslationError::UnknownError(format!("{:?}", err))),
        }
    }

    /// Translate the body of a function.
    pub fn new(
        env: &'def Environment<'tcx>,
        meta: ProcedureMeta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a rustc_ast::ast::AttrItem],
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        proc_registry: &'a ProcedureScope<'def>,
        const_registry: &'a ConstScope<'def>,
    ) -> Result<Self, TranslationError> {
        let mut translated_fn = radium::FunctionBuilder::new(&meta.name, &meta.spec_name);

        // TODO can we avoid the leak
        let proc: &'def Procedure = &*Box::leak(Box::new(proc));

        let body = proc.get_mir();
        Self::dump_body(&body);

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
        let sig = normalize_in_function(proc.get_id(), env.tcx(), sig)?;

        info!("Function signature: {:?}", sig);

        match PoloniusInfo::new(env, proc) {
            Ok(info) => {
                // TODO: avoid leak
                let info: &'def PoloniusInfo = &*Box::leak(Box::new(info));

                let params = proc.get_type_params();
                info!("Function generic args: {:?}", params);

                // dump graphviz files
                // color code: red: dying loan, pink: becoming a zombie; green: is zombie
                if rrconfig::dump_borrowck_info() {
                    crate::environment::dump_borrowck_info(env, &proc.get_id(), &info);
                }

                let (inputs, output, universal_lifetimes) =
                    Self::process_lifetimes_of_args(&env, params, sig, &body);
                info!("Have lifetime parameters: {:?}", universal_lifetimes);
                info!("inputs: {:?}, output: {:?}", inputs, output);

                // add universal lifetimes to the spec
                for (lft, name) in universal_lifetimes.values() {
                    translated_fn
                        .add_universal_lifetime(name.clone(), lft.to_string())
                        .map_err(|e| TranslationError::UnknownError(e))?;
                }

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

                // enter the procedure
                let universal_lifetime_map: HashMap<_, _> =
                    universal_lifetimes.into_iter().map(|(x, y)| (x, y.0)).collect();
                let type_scope = TypeTranslationScope::new(proc.get_id(), params, universal_lifetime_map)?;
                // add generic args to the fn
                let generics = &type_scope.generic_scope;
                for t in generics.iter().flatten() {
                    translated_fn.add_generic_type(t.clone());
                }

                let mut t = Self {
                    env,
                    proc,
                    info,
                    translated_fn,
                    inclusion_tracker,
                    procedure_registry: proc_registry,
                    attrs,
                    ty_translator: LocalTypeTranslator::new(ty_translator, type_scope),
                    const_registry,
                    inputs: inputs.clone(),
                };
                // add universal constraints
                let universal_constraints = t.get_relevant_universal_constraints();
                info!("univeral constraints: {:?}", universal_constraints);
                for (lft1, lft2) in universal_constraints {
                    t.translated_fn
                        .add_universal_lifetime_constraint(lft1, lft2)
                        .map_err(|e| TranslationError::UnknownError(e))?;
                }

                // process attributes
                t.process_attrs(inputs.as_slice(), &output)?;

                Ok(t)
            },
            Err(err) => Err(TranslationError::UnknownError(format!("{:?}", err))),
        }
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
            if let info::RegionKind::Universal(uk1) = info.get_region_kind(*r1) {
                if let info::RegionKind::Universal(uk2) = info.get_region_kind(*r2) {
                    // if LHS is static, ignore.
                    if uk1 == info::UniversalRegionKind::Static {
                        continue;
                    }
                    // if RHS is the function lifetime, ignore
                    if uk2 == info::UniversalRegionKind::Function {
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

    /// Parse and process attributes of this closure.
    fn process_closure_attrs<'b>(
        &mut self,
        normalized_inputs: &[Ty<'tcx>],
        normalized_output: &Ty<'tcx>,
        meta: ClosureMetaInfo<'b, 'tcx, 'def>,
    ) -> Result<(), TranslationError> {
        trace!("entering process_closure_attrs");
        let v = self.attrs;

        info!("inputs: {:?}, output: {:?}", normalized_inputs, normalized_output);
        let mut translated_arg_types: Vec<radium::Type<'def>> = Vec::new();
        for arg in normalized_inputs {
            let translated: radium::Type<'def> = self.ty_translator.translate_type_no_normalize(arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: radium::Type<'def> =
            // output is already normalized
            self.ty_translator.translate_type_no_normalize(normalized_output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                let ty_translator = &self.ty_translator;
                let mut parser: VerboseFunctionSpecParser<'_, 'def, _> =
                    VerboseFunctionSpecParser::new(&translated_arg_types, &translated_ret_type, |lit| {
                        ty_translator.translator.intern_literal(lit)
                    });
                parser
                    .parse_closure_spec(v, &mut self.translated_fn, meta, |x| ty_translator.make_tuple_use(x))
                    .map_err(|e| TranslationError::AttributeError(e))?;
                trace!("leaving process_closure_attrs");
                Ok(())
            },
            _ => {
                trace!("leaving process_closure_attrs");
                Err(TranslationError::UnknownAttributeParser(parser))
            },
        }
    }

    /// Parse and process attributes of this function.
    fn process_attrs(
        &mut self,
        normalized_inputs: &[Ty<'tcx>],
        normalized_output: &Ty<'tcx>,
    ) -> Result<(), TranslationError> {
        let v = self.attrs;

        info!("inputs: {:?}, output: {:?}", normalized_inputs, normalized_output);
        let mut translated_arg_types: Vec<radium::Type<'def>> = Vec::new();
        for arg in normalized_inputs {
            let translated: radium::Type<'def> = self.ty_translator.translate_type_no_normalize(arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: radium::Type<'def> =
            self.ty_translator.translate_type_no_normalize(normalized_output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                let ty_translator = &self.ty_translator;
                let mut parser: VerboseFunctionSpecParser<'_, 'def, _> =
                    VerboseFunctionSpecParser::new(&translated_arg_types, &translated_ret_type, |lit| {
                        ty_translator.translator.intern_literal(lit)
                    });
                parser
                    .parse_function_spec(v, &mut self.translated_fn)
                    .map_err(|e| TranslationError::AttributeError(e))?;
                Ok(())
            },
            _ => Err(TranslationError::UnknownAttributeParser(parser)),
        }
    }

    // TODO refactor/ move
    fn to_universal_lft(&self, k: info::UniversalRegionKind, r: Region) -> Option<radium::UniversalLft> {
        match k {
            info::UniversalRegionKind::Function => Some(radium::UniversalLft::Function),
            info::UniversalRegionKind::Static => Some(radium::UniversalLft::Static),
            info::UniversalRegionKind::Local => self
                .ty_translator
                .scope
                .borrow()
                .lookup_universal_region(r)
                .map(|x| radium::UniversalLft::Local(x)),
            info::UniversalRegionKind::External => self
                .ty_translator
                .scope
                .borrow()
                .lookup_universal_region(r)
                .map(|x| radium::UniversalLft::External(x)),
        }
    }

    /// Translation that only generates a specification.
    pub fn generate_spec(self) -> Result<radium::FunctionSpec<'def>, TranslationError> {
        Ok(self.translated_fn.into())
    }

    /// Generate a string identifier for a Local.
    /// Tries to find the Rust source code name of the local, otherwise simply enumerates.
    /// `used_names` keeps track of the Rust source code names that have already been used.
    fn make_local_name(mir_body: &Body<'tcx>, local: &Local, used_names: &mut HashSet<String>) -> String {
        if let Some(mir_name) = Self::find_name_for_local(mir_body, local, &used_names) {
            let name = strip_coq_ident(&mir_name);
            used_names.insert(mir_name);
            name
        } else {
            let mut name = "__".to_string();
            name.push_str(&local.index().to_string());
            name
        }
    }

    /// Find a source name for a local of a MIR body, if possible.
    fn find_name_for_local(
        body: &mir::Body<'tcx>,
        local: &mir::Local,
        used_names: &HashSet<String>,
    ) -> Option<String> {
        let debug_info = &body.var_debug_info;
        for dbg in debug_info {
            let name = &dbg.name;
            let val = &dbg.value;
            match *val {
                VarDebugInfoContents::Place(l) => {
                    // make sure that the place projection is empty -- otherwise this might just
                    // refer to the capture of a closure
                    if let Some(this_local) = l.as_local() {
                        if this_local == *local {
                            // around closures, multiple symbols may be mapped to the same name.
                            // To prevent this from happening, we check that the name hasn't been
                            // used already
                            // TODO: find better solution
                            if !used_names.contains(name.as_str()) {
                                return Some(name.as_str().to_string());
                            }
                        }
                    }
                },
                VarDebugInfoContents::Const(_) => {
                    // is this case used when constant propagation happens during MIR construction?
                },
            }
        }

        return None;
    }

    fn dump_body(body: &Body) {
        // TODO: print to file
        let basic_blocks = &body.basic_blocks;
        for (bb_idx, bb) in basic_blocks.iter_enumerated() {
            Self::dump_basic_block(&bb_idx, bb);
        }
    }

    /// Dump a basic block as info debug output.
    fn dump_basic_block(bb_idx: &BasicBlock, bb: &BasicBlockData) {
        info!("Basic block {:?}:", bb_idx);
        let mut i = 0;
        for s in &bb.statements {
            info!("{}\t{:?}", i, s);
            i += 1;
        }
        info!("{}\t{:?}", i, bb.terminator());
    }

    pub fn translate(mut self) -> Result<radium::Function<'def>, TranslationError> {
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
            Err(TranslationError::UnknownError("could not find local for return value".to_string()));
        let mut used_names = HashSet::new();
        let mut arg_tys = Vec::new();

        // go over local_decls and create the right radium:: stack layout
        for (local, local_decl) in local_decls.iter_enumerated() {
            let kind = body.local_kind(local);
            let ty: &Ty<'tcx>;
            if let Some(rewritten_ty) = checked_op_locals.get(&local) {
                ty = rewritten_ty;
            } else {
                ty = &local_decl.ty;
            }

            // check if the type is of a spec fn -- in this case, we can skip this temporary
            if let TyKind::Closure(id, _) = ty.kind() {
                if self.procedure_registry.lookup_function_mode(id).map_or(false, |m| m.is_ignore()) {
                    // this is a spec fn
                    info!("skipping local which has specfn closure type: {:?}", local);
                    continue;
                }
            }

            // type:
            let tr_ty = self.ty_translator.translate_type(ty)?;
            let st = tr_ty.get_syn_type();

            let name = Self::make_local_name(body, &local, &mut used_names);
            radium_name_map.insert(local, name.to_string());

            fn_locals.push((local, name.clone(), tr_ty));

            match kind {
                LocalKind::Arg => {
                    self.translated_fn.code.add_argument(&name, st);
                    arg_tys.push(*ty);
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
            collected_statics: HashSet::new(),
        };
        translator.translate(initial_constraints)
    }

    /// Determine initial constraints between universal regions and local place regions.
    /// Returns an initial mapping for the name _map that initializes place regions of arguments
    /// with universals.
    fn get_initial_universal_arg_constraints(
        &mut self,
        _sig_args: &[Ty<'tcx>],
        _local_args: &[Ty<'tcx>],
    ) -> Vec<(info::AtomicRegion, info::AtomicRegion)> {
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

            if let info::AtomicRegion::Universal(info::UniversalRegionKind::Local, _) = lft1 {
                // this is a constraint we care about here, add it
                if !self.inclusion_tracker.check_inclusion(*r1, *r2, root_point) {
                    self.inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);
                    assert!(match lft2 {
                        info::AtomicRegion::PlaceRegion(_) => true,
                        _ => false,
                    });
                    initial_arg_mapping.push((lft1, lft2));
                }
            }
        }
        initial_arg_mapping
    }

    fn get_initial_universal_arg_constraints2(
        &mut self,
        sig_args: &[Ty<'tcx>],
        local_args: &[Ty<'tcx>],
    ) -> Vec<(info::AtomicRegion, info::AtomicRegion)> {
        // Polonius generates a base subset constraint uregion ⊑ pregion.
        // We turn that into pregion = uregion, as we do strong updates at the top-level.
        assert!(sig_args.len() == local_args.len());

        let initial_arg_mapping = Vec::new();
        // TODO: implement a bitypefolder to solve this issue.

        initial_arg_mapping
    }
}

/**
 * Struct that keeps track of all information necessary to translate a MIR Body to a radium::Function.
 * `'a` is the lifetime of the translator and ends after translation has finished.
 * `'def` is the lifetime of the generated code (the code may refer to struct defs).
 * `'tcx' is the lifetime of the rustc tctx.
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
    collected_procedures:
        HashMap<(DefId, FnGenericKey<'tcx>), (String, String, Vec<radium::Type<'def>>, Vec<radium::SynType>)>,
    /// used statics
    collected_statics: HashSet<DefId>,

    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a ProcedureScope<'def>,
    /// scope of used consts
    const_registry: &'a ConstScope<'def>,
    /// attributes on this function
    attrs: &'a [&'a rustc_ast::ast::AttrItem],
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
    ty_translator: LocalTypeTranslator<'a, 'def, 'tcx>,

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
    /// Main translation function that actually does the translation and returns a radium::Function
    /// if successful.
    pub fn translate(
        mut self,
        initial_constraints: Vec<(info::AtomicRegion, info::AtomicRegion)>,
    ) -> Result<radium::Function<'def>, TranslationError> {
        // add loop info
        let loop_info = self.proc.loop_info();
        info!("loop heads: {:?}", loop_info.loop_heads);
        for (head, bodies) in &loop_info.loop_bodies {
            info!("loop {:?} -> {:?}", head, bodies);
        }

        // translate the function's basic blocks
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // first translate the initial basic block; we add some additional annotations to the front
        let initial_bb_idx = BasicBlock::from_u32(0);
        if let Some(bb) = basic_blocks.get(initial_bb_idx) {
            let mut translated_bb = self.translate_basic_block(initial_bb_idx, bb)?;
            // push annotation for initial constraints that relate argument's place regions to universals
            for (r1, r2) in &initial_constraints {
                translated_bb = radium::Stmt::Annot {
                    a: radium::Annotation::CopyLftName(
                        self.format_atomic_region(r1),
                        self.format_atomic_region(r2),
                    ),
                    s: Box::new(translated_bb),
                    why: Some("initialization".to_string()),
                };
            }
            self.translated_fn.code.add_basic_block(initial_bb_idx.as_usize(), translated_bb);
        } else {
            info!("No basic blocks");
        }

        while let Some(bb_idx) = self.bb_queue.pop() {
            let ref bb = basic_blocks[bb_idx];
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
        for g in &self.ty_translator.scope.borrow().tuple_uses {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }

        // TODO: process self.loop_specs
        // - collect the relevant bb -> def_id mappings for this function (so we can eventually generate the
        //   definition)
        // - have a function that takes the def_id and then parses the attributes into a loop invariant
        for (head, did) in &self.loop_specs {
            let spec = self.parse_attributes_on_loop_spec_closure(head, did);
            self.translated_fn.register_loop_invariant(head.as_usize(), spec);
        }

        // generate dependencies on other procedures.
        for (loc_name, spec_name, params, sts) in self.collected_procedures.values() {
            self.translated_fn.require_function(
                loc_name.clone(),
                spec_name.clone(),
                params.clone(),
                sts.clone(),
            );
        }

        // generate dependencies on statics
        for did in &self.collected_statics {
            let s = self.const_registry.statics.get(did).unwrap();
            self.translated_fn.require_static(s.clone());
        }

        Ok(self.translated_fn.into())
    }

    /// Determine initial constraints between universal regions and local place regions.
    /// Returns an initial mapping for the name _map that initializes place regions of arguments
    /// with universals.
    fn get_initial_universal_arg_constraints(&mut self) -> Vec<(info::AtomicRegion, info::AtomicRegion)> {
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

            if let info::AtomicRegion::Universal(info::UniversalRegionKind::Local, _) = lft1 {
                // this is a constraint we care about here, add it
                if !self.inclusion_tracker.check_inclusion(*r1, *r2, root_point) {
                    self.inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);
                    assert!(match lft2 {
                        info::AtomicRegion::PlaceRegion(_) => true,
                        _ => false,
                    });
                    initial_arg_mapping.push((lft1, lft2));
                }
            }
        }
        initial_arg_mapping
    }

    /// Generate a key for generics to index into our map of other required procedures.
    fn generate_procedure_inst_key(
        &self,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> Result<FnGenericKey<'tcx>, TranslationError> {
        // erase parameters to their syntactic types
        let mut key = Vec::new();
        let mut region_eraser = TyRegionEraseFolder::new(self.env.tcx());
        for p in ty_params {
            match p.unpack() {
                ty::GenericArgKind::Lifetime(_) => {
                    // lifetimes are not relevant here
                },
                ty::GenericArgKind::Type(t) => {
                    // TODO: this should erase to the syntactic type.
                    // Is erasing regions enough for that?
                    let t_erased = t.fold_with(&mut region_eraser);
                    key.push(t_erased);
                },
                ty::GenericArgKind::Const(_c) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does not support const generics".to_string(),
                    });
                },
            }
        }
        Ok(key)
    }

    /// Internally register that we have used a procedure with a particular instantiation of generics, and
    /// return the code parameter name.
    fn register_use_procedure(
        &mut self,
        did: &DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> Result<String, TranslationError> {
        trace!("enter register_use_procedure did={:?} ty_params={:?}", did, ty_params);
        let key = self.generate_procedure_inst_key(ty_params)?;

        let tup = (*did, key);
        let res;
        if let Some((n, ..)) = self.collected_procedures.get(&tup) {
            res = format!("{}", n);
        } else {
            // lookup the name in the procedure registry

            let name = self
                .procedure_registry
                .lookup_function_mangled_name(did)
                .ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", did)))?;
            let spec_name = self
                .procedure_registry
                .lookup_function_spec_name(did)
                .ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", did)))?;

            let mut mangled_name = name.to_string();
            let mut translated_params = Vec::new();

            // TODO: maybe come up with some better way to generate names
            info!("register_use_procedure: translating args {:?}", tup.1);
            for p in &tup.1 {
                mangled_name.push_str(format!("_{}", p).as_str());

                let translated_ty = self.ty_translator.translate_type(p)?;

                translated_params.push(translated_ty);
            }
            let mangled_name = strip_coq_ident(&mangled_name);

            // also gather all the layouts of the arguments.
            let full_ty: ty::EarlyBinder<Ty<'tcx>> = self.env.tcx().type_of(*did);
            let full_ty: Ty<'tcx> = full_ty.instantiate_identity();

            let mut normalized_inputs = Vec::new();
            let mut syntypes = Vec::new();
            match full_ty.kind() {
                ty::TyKind::FnDef(_, _) => {
                    let sig = full_ty.fn_sig(self.env.tcx());
                    let sig = normalize_in_function(*did, self.env.tcx(), sig)?;
                    for ty in sig.inputs().skip_binder() {
                        normalized_inputs.push(*ty);
                    }
                },
                ty::TyKind::Closure(_, args) => {
                    let clos_args = args.as_closure();
                    let sig = clos_args.sig();
                    let sig = normalize_in_function(*did, self.env.tcx(), sig)?;
                    let pre_sig = sig.skip_binder();
                    // we also need to add the closure argument here
                    // in this case, we need to patch the region first

                    let tuple_ty = clos_args.tupled_upvars_ty();
                    match clos_args.kind() {
                        ty::ClosureKind::Fn => {
                            syntypes.push(radium::SynType::Ptr);
                        },
                        ty::ClosureKind::FnMut => {
                            syntypes.push(radium::SynType::Ptr);
                        },
                        ty::ClosureKind::FnOnce => {
                            normalized_inputs.push(tuple_ty);
                        },
                    }
                    for ty in pre_sig.inputs() {
                        normalized_inputs.push(*ty);
                    }
                },
                _ => unimplemented!(),
            }

            //info!("substs: {:?}, inputs {:?} ", ty_params, inputs);
            for i in &normalized_inputs {
                // need to wrap it, because there's no Subst instance for Ty
                let i = ty::EarlyBinder::bind(*i);
                let ty = i.instantiate(self.env.tcx(), ty_params);
                let t = self.ty_translator.translate_type_to_syn_type_no_normalize(&ty)?;
                syntypes.push(t);
            }

            let loc_name = format!("{}_loc", mangled_name);
            info!(
                "Registered procedure instance {} of {:?} with {:?} and layouts {:?}",
                mangled_name, did, translated_params, syntypes
            );
            self.collected_procedures
                .insert(tup, (loc_name.clone(), spec_name.to_string(), translated_params, syntypes));
            res = loc_name;
        }
        trace!("leave register_use_procedure");
        Ok(res)
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
    fn format_atomic_region(&self, r: &info::AtomicRegion) -> String {
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
        loop_head: &BasicBlock,
        did: &Option<DefId>,
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
        for (_l, name, ty) in &self.fn_locals {
            // get the refinement type
            let mut rfn_ty = ty.get_rfn_type(&[]);
            // wrap it in place_rfn, since we reason about places
            rfn_ty = radium::CoqType::PlaceRfn(Box::new(rfn_ty));

            // determine their initialization status
            //let initialized = true; // TODO
            // determine the actual refinement type for the current initialization status.

            let rfn_name = radium::CoqName::Named(format!("r_{}", name));
            rfn_binders.push(radium::CoqBinder::new(rfn_name, rfn_ty));
        }

        // TODO what do we do about stuff connecting borrows?
        if let Some(did) = did {
            let attrs = self.env.get_attributes(*did);
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
    fn check_place_below_reference(&self, place: &Place<'tcx>) -> Result<bool, TranslationError> {
        if self.checked_op_temporaries.contains_key(&place.local) {
            // temporaries are never below references
            return Ok(false);
        }

        for (pl, _) in place.iter_projections() {
            // check if the current ty is a reference that we then descend under with proj
            let cur_ty_kind = pl.ty(&self.proc.get_mir().local_decls, self.env.tcx()).ty.kind();
            match cur_ty_kind {
                TyKind::Ref(_, _, _) => {
                    return Ok(true);
                },
                _ => (),
            }
        }
        Ok(false)
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
        op: &Operand<'tcx>,
    ) -> Result<(DefId, ty::PolyFnSig<'tcx>, ty::GenericArgsRef<'tcx>, ty::PolyFnSig<'tcx>), TranslationError>
    {
        match op {
            Operand::Constant(box Constant { literal, .. }) => {
                match literal {
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
                                description: "implement function pointers".to_string(),
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
                                description: "implement function pointers".to_string(),
                            }),
                        }
                    },
                    ConstantKind::Unevaluated(_, _) => Err(TranslationError::Unimplemented {
                        description: "implement ConstantKind::Unevaluated".to_string(),
                    }),
                }
            },
            _ => panic!("should not be reachable"),
        }
    }

    /// Find the optional DefId of the closure giving the invariant for the loop with head `head_bb`.
    fn find_loop_spec_closure(&self, head_bb: BasicBlock) -> Result<Option<DefId>, TranslationError> {
        let bodies = self.proc.loop_info().ordered_loop_bodies.get(&head_bb).unwrap();
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // we go in order through the bodies in order to not stumble upon an annotation for a
        // nested loop!
        for body in bodies {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in &data.statements {
                    if let StatementKind::Assign(box (ref pl, _)) = stmt.kind {
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
        target: &BasicBlock,
    ) -> Result<radium::Stmt, TranslationError> {
        self.enqueue_basic_block(*target);
        let res_stmt = radium::Stmt::GotoBlock(target.as_usize());

        let loop_info = self.proc.loop_info();
        if loop_info.is_loop_head(*target) && !self.loop_specs.contains_key(target) {
            let spec_defid = self.find_loop_spec_closure(*target)?;
            self.loop_specs.insert(*target, spec_defid);
        }

        Ok(res_stmt)
    }

    /// Check if a call goes to std::rt::begin_panic
    fn is_call_destination_panic(&mut self, func: &Operand) -> Result<bool, TranslationError> {
        match func {
            Operand::Constant(box c) => match c.literal {
                ConstantKind::Val(_, ty) => match ty.kind() {
                    TyKind::FnDef(did, _) => {
                        if let Some(panic_id1) = crate::utils::try_resolve_did(self.env.tcx(), &[
                            "std",
                            "panicking",
                            "begin_panic",
                        ]) {
                            if panic_id1 == *did {
                                return Ok(true);
                            }
                        } else {
                            warn!("Failed to determine DefId of std::panicking::begin_panic");
                        }

                        if let Some(panic_id2) =
                            crate::utils::try_resolve_did(self.env.tcx(), &["core", "panicking", "panic"])
                        {
                            if panic_id2 == *did {
                                return Ok(true);
                            }
                        } else {
                            warn!("Failed to determine DefId of core::panicking::panic");
                        }
                        Ok(false)
                    },
                    _ => Ok(false),
                },
                _ => Ok(false),
            },
            _ => Ok(false),
        }
    }

    /// Registers a drop shim for a particular type for the translation.
    const fn register_drop_shim_for(&self, _ty: Ty<'tcx>) {
        // TODO!
        //let drop_in_place_did: DefId = crate::utils::try_resolve_did(self.env.tcx(), &["std", "ptr",
        // "drop_in_place"]).unwrap();

        //let x: ty::InstanceDef = ty::InstanceDef::DropGlue(drop_in_place_did, Some(ty));
        //let body: &'tcx mir::Body = self.env.tcx().mir_shims(x);

        //info!("Generated drop shim for {:?}", ty);
        //Self::dump_body(body);
    }

    fn compute_call_regions(
        &self,
        func: &Operand<'tcx>,
        loc: Location,
    ) -> Result<CallRegions, TranslationError> {
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
            match a.unpack() {
                ty::GenericArgKind::Lifetime(r) => match r.kind() {
                    ty::RegionKind::ReVar(r) => early_regions.push(r),
                    _ => (),
                },
                _ => (),
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
            match a.unpack() {
                ty::GenericArgKind::Type(c) => {
                    let mut folder = ty::fold::RegionFolder::new(self.env.tcx(), &mut clos);
                    folder.fold_ty(c);
                },
                _ => (),
            }
        }
        info!("Regions of generic args: {:?}", generic_regions);

        // go over all region constraints initiated at this location
        let new_constraints = self.info.get_new_subset_constraints_at_point(midpoint);
        let mut new_regions = HashSet::new();
        let mut relevant_constraints = Vec::new();
        for (r1, r2) in &new_constraints {
            if matches!(self.info.get_region_kind(*r1), info::RegionKind::Unknown) {
                // this is probably a inference variable for the call
                new_regions.insert(*r1);
                relevant_constraints.push((*r1, *r2));
            }
            if matches!(self.info.get_region_kind(*r2), info::RegionKind::Unknown) {
                new_regions.insert(*r2);
                relevant_constraints.push((*r1, *r2));
            }
        }
        // first sort this to enable cycle resolution
        let mut new_regions_sorted: Vec<Region> = new_regions.iter().cloned().collect();
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
        let relevant_constraints = info::compute_transitive_closure(relevant_constraints);
        for r in &new_regions_sorted {
            for (r1, r2) in &relevant_constraints {
                if *r2 == *r {
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
                    } else {
                        // the intersection also needs to contain r1
                        if new_regions.contains(r1) {
                            // we do not need this constraint, since we already computed the
                            // transitive closure.
                            continue;
                        }
                        let kind = new_regions_classification
                            .entry(*r)
                            .or_insert(CallRegionKind::Intersection(HashSet::new()));
                        match kind {
                            CallRegionKind::Intersection(s) => {
                                s.insert(*r1);
                            },
                            _ => panic!("unreachable"),
                        }
                    }
                }
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
        target: Option<rustc_middle::mir::BasicBlock>,
        loc: Location,
        dying_loans: &[facts::Loan],
    ) -> Result<radium::Stmt, TranslationError> {
        let startpoint = self.info.interner.get_point_index(&facts::Point {
            location: loc,
            typ: facts::PointType::Start,
        });

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

        let classification = self.compute_call_regions(func, loc)?;

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

        let func_expr = self.translate_operand(func, false)?;
        // translate the arguments
        let mut translated_args = Vec::new();
        for arg in args {
            // to_ty is the type the function expects

            //let ty = arg.ty(&self.proc.get_mir().local_decls, self.env.tcx());
            let translated_arg = self.translate_operand(arg, true)?;
            translated_args.push(translated_arg);
        }

        // make the call lifetime instantiation list
        let mut lifetime_insts = Vec::new();
        for early in &classification.early_regions {
            let lft = self.format_region(*early);
            lifetime_insts.push(lft);
        }
        for late in &classification.late_regions {
            let lft = self.format_region(*late);
            lifetime_insts.push(lft);
        }
        info!("Call lifetime instantiation: {:?}", lifetime_insts);

        // TODO: add annotations for the assignment
        // for that:
        // - get the type of the place
        // - enforce constraints as necessary. this might spawn dyninclusions with some of the new regions =>
        //   In Coq, also the aliases should get proper endlft events to resolve the dyninclusions.
        // - update the name map
        let call_expr = radium::Expr::Call {
            f: Box::new(func_expr),
            lfts: lifetime_insts,
            args: translated_args,
        };
        let stmt = match target {
            Some(ref target) => {
                let mut cont_stmt = self.translate_goto_like(&loc, target)?;
                // end loans before the goto, but after the call.
                // TODO: may cause duplications?
                cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.iter().cloned());

                // Get the type of the return value from the function
                let (_, _, _, inst_sig) = self.call_expr_op_split_inst(func)?;
                // TODO: do we need to do something with late bounds?
                let output_ty = inst_sig.output().skip_binder();
                info!("call has instantiated type {:?}", inst_sig);

                // compute the resulting annotations
                let (rhs_annots, pre_stmt_annots, post_stmt_annots) =
                    self.get_assignment_annots(loc, &destination, output_ty)?;
                info!(
                    "assignment annots after call: expr: {:?}, pre-stmt: {:?}, post-stmt: {:?}",
                    rhs_annots, pre_stmt_annots, post_stmt_annots
                );

                let cont_stmt = radium::Stmt::with_annotations(
                    cont_stmt,
                    post_stmt_annots,
                    Some("post_function_call".to_string()),
                );

                // assign stmt with call; then jump to bb
                let place_ty = self.get_type_of_place(destination)?;
                let place_st = self.ty_translator.translate_type_to_syn_type(&place_ty.ty)?;
                let place_expr = self.translate_place(destination)?;

                let ot = self.ty_translator.translate_syn_type_to_op_type(&place_st);

                let annotated_rhs = radium::Expr::with_optional_annotation(
                    call_expr,
                    rhs_annots,
                    Some("function_call".to_string()),
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
                    Some("function_call".to_string()),
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
                        0 => panic!("unconstrained lifetime"),
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

        let stmt = radium::Stmt::with_annotations(stmt, stmt_annots, Some("function_call".to_string()));
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
    ) -> Result<radium::Stmt, TranslationError> {
        let mut res_stmt;
        match term.kind {
            TerminatorKind::UnwindResume => {
                return Err(TranslationError::Unimplemented {
                    description: "implement UnwindResume".to_string(),
                });
            },
            TerminatorKind::UnwindTerminate(_) => {
                return Err(TranslationError::Unimplemented {
                    description: "implement UnwindTerminate".to_string(),
                });
            },
            TerminatorKind::Goto { ref target } => {
                res_stmt = self.translate_goto_like(&loc, target)?;
            },
            TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ref target,
                ..
            } => {
                trace!("translating Call {:?}", term);
                let is_panic = self.is_call_destination_panic(func)?;
                if is_panic {
                    info!("Replacing call to std::panicking::begin_panic with Stuck");
                    return Ok(radium::Stmt::Stuck);
                }
                res_stmt = self.translate_function_call(
                    func,
                    args,
                    destination,
                    *target,
                    loc,
                    dying_loans.as_slice(),
                )?;
            },
            TerminatorKind::Return => {
                // TODO: this requires additional handling for reborrows

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                res_stmt = radium::Stmt::Return(radium::Expr::Use {
                    ot: self.ty_translator.translate_syn_type_to_op_type(&self.return_synty),
                    e: Box::new(radium::Expr::Var(self.return_name.to_string())),
                });

                // TODO is this right?
                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
            },
            //TerminatorKind::Abort => {
            //res_stmt = radium::Stmt::Stuck;
            //res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
            //},
            TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } => {
                let operand = self.translate_operand(discr, true)?;
                let all_targets: &[BasicBlock] = targets.all_targets();

                let switch_ty = self.get_type_of_operand(discr)?;
                if switch_ty.is_bool() {
                    // we currently special-case this as Caesium has a built-in if and this is more
                    // convenient to handle for the type-checker

                    // implementation detail: the first index is the `false` branch, the second the
                    // `true` branch
                    let true_target = all_targets.get(1).unwrap();
                    let false_target = all_targets[0];
                    let true_branch = self.translate_goto_like(&loc, &true_target)?;
                    let false_branch = self.translate_goto_like(&loc, &false_target)?;
                    res_stmt = radium::Stmt::If {
                        e: operand,
                        ot: radium::OpType::BoolOp,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    };

                    // TODO: is this right?
                    res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
                } else {
                    //info!("switchint: {:?}", term.kind);
                    let operand = self.translate_operand(discr, true)?;
                    let ty = self.get_type_of_operand(discr)?;

                    let mut target_map: HashMap<u128, usize> = HashMap::new();
                    let mut translated_targets: Vec<radium::Stmt> = Vec::new();
                    for (idx, (tgt, bb)) in targets.iter().enumerate() {
                        let bb: BasicBlock = bb;
                        let translated_target = self.translate_goto_like(&loc, &bb)?;

                        target_map.insert(tgt, idx);
                        translated_targets.push(translated_target);
                    }
                    let translated_default = self.translate_goto_like(&loc, &targets.otherwise())?;
                    // TODO: need to put endlfts infront of gotos?

                    let translated_ty = self.ty_translator.translate_type(&ty)?;
                    if let radium::Type::Int(it) = translated_ty {
                        res_stmt = radium::Stmt::Switch {
                            e: operand,
                            it,
                            index_map: target_map,
                            bs: translated_targets,
                            def: Box::new(translated_default),
                        };
                    } else {
                        return Err(TranslationError::UnknownError(
                            "SwitchInt switching on non-integer type".to_string(),
                        ));
                    }
                }
            },
            TerminatorKind::Assert {
                ref cond,
                expected,
                ref target,
                ..
            } => {
                // this translation gets stuck on failure
                let cond_translated = self.translate_operand(cond, true)?;
                let comp = radium::Expr::BinOp {
                    o: radium::Binop::EqOp,
                    ot1: radium::OpType::BoolOp,
                    ot2: radium::OpType::BoolOp,
                    e1: Box::new(cond_translated),
                    e2: Box::new(radium::Expr::Literal(radium::Literal::LitBool(expected))),
                };

                res_stmt = self.translate_goto_like(&loc, target)?;

                // TODO: should we really have this?
                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());

                res_stmt = radium::Stmt::AssertS {
                    e: comp,
                    s: Box::new(res_stmt),
                };
            },
            TerminatorKind::Drop {
                ref place,
                ref target,
                ..
            } => {
                let ty = self.get_type_of_place(place)?;
                self.register_drop_shim_for(ty.ty);

                let place_translated = self.translate_place(place)?;
                let _drope = radium::Expr::DropE(Box::new(place_translated));

                res_stmt = self.translate_goto_like(&loc, target)?;

                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());

                //res_stmt = radium::Stmt::ExprS { e: drope, s: Box::new(res_stmt)};
            },
            TerminatorKind::FalseEdge { real_target, .. } => {
                // just a goto for our purposes
                res_stmt = self.translate_goto_like(&loc, &real_target)?;
            },
            TerminatorKind::FalseUnwind {
                ref real_target, ..
            } => {
                // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
                res_stmt = self.translate_goto_like(&loc, real_target)?;
            },
            TerminatorKind::GeneratorDrop => {
                return Err(TranslationError::UnsupportedFeature {
                    description: format!("Unsupported terminator {:?}", term),
                });
            },
            TerminatorKind::Yield { .. } => {
                return Err(TranslationError::UnsupportedFeature {
                    description: format!("Unsupported terminator {:?}", term),
                });
            },
            TerminatorKind::Unreachable => {
                res_stmt = radium::Stmt::Stuck;
            },
            TerminatorKind::InlineAsm { .. } => {
                return Err(TranslationError::UnsupportedFeature {
                    description: format!("Unsupported terminator {:?}", term),
                });
            },
        };

        Ok(res_stmt)
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
                    why: Some("endlft".to_string()),
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
    fn find_region_variables_of_place_type(&self, ty: PlaceTy<'tcx>) -> Vec<Region> {
        let mut collector = TyRegionCollectFolder::new(self.env.tcx());
        if let Some(_) = ty.variant_index {
            panic!("find_region_variables_of_place_type: don't support enums");
        }

        ty.ty.fold_with(&mut collector);
        collector.get_regions()
    }

    /// Generate an annotation on an expression needed to update the region name map.
    fn generate_strong_update_annot(&self, ty: PlaceTy<'tcx>) -> Option<radium::Annotation> {
        let (interesting, tree) = self.generate_strong_update_annot_rec(ty.ty);
        if interesting { Some(radium::Annotation::GetLftNames(tree)) } else { None }
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
    fn is_spec_closure_local(&self, l: Local) -> Result<Option<DefId>, TranslationError> {
        // check if we should ignore this
        let local_type = self.get_type_of_local(&l)?;
        if let TyKind::Closure(did, _) = local_type.kind() {
            Ok(self
                .procedure_registry
                .lookup_function_mode(did)
                .and_then(|m| if m.is_ignore() { Some(*did) } else { None }))
        } else {
            Ok(None)
        }
    }

    fn region_to_region_vid(&self, r: ty::Region<'tcx>) -> facts::Region {
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
        incls: HashSet<(Region, Region, PointIndex)>,
    ) -> Vec<radium::Annotation> {
        // before executing the assignment, first enforce dynamic inclusions
        info!("Generating dynamic inclusions {:?}", incls);
        let mut stmt_annots = Vec::new();
        for (r1, r2, p) in &incls {
            if !incls.contains(&(*r2, *r1, *p)) {
                self.generate_dyn_inclusion(&mut stmt_annots, *r1, *r2, *p);
            } else {
                warn!("Skipping impossible dynamic inclusion {:?} ⊑ {:?} at {:?}", r1, r2, p);
            }
        }
        stmt_annots
    }

    /// Get the annotations due to borrows appearing on the RHS of an assignment.
    fn get_assignment_loan_annots(
        &mut self,
        loc: Location,
        rhs: &Rvalue<'tcx>,
    ) -> Result<Vec<radium::Annotation>, TranslationError> {
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

            let region = self.region_to_region_vid(*region);

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
        Ok(stmt_annots)
    }

    /// Compute the annotations for an assignment: an annotation for the rhs value, and a list of
    /// annotations to prepend to the statement, and a list of annotations to put after the
    /// statement.
    fn get_assignment_annots(
        &mut self,
        loc: Location,
        lhs: &Place<'tcx>,
        _rhs_ty: Ty<'tcx>,
    ) -> Result<
        (Option<radium::Annotation>, Vec<radium::Annotation>, Vec<radium::Annotation>),
        TranslationError,
    > {
        // check if the place is strongly writeable
        let strongly_writeable = !self.check_place_below_reference(lhs)?;
        let plc_ty = self.get_type_of_place(lhs)?;

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
        let new_dyn_inclusions = self.generate_dyn_inclusions(new_dyn_inclusions);
        Ok((expr_annot, new_dyn_inclusions, stmt_annot))
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
    ) -> Result<radium::Stmt, TranslationError> {
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

                    if let Some(_) = self.is_spec_closure_local(plc.local)? {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    } else if let Some(rewritten_ty) = self.checked_op_temporaries.get(&plc.local) {
                        // if this is a checked op, be sure to remember it
                        info!("rewriting assignment to checked op: {:?}", plc);

                        let synty = self.ty_translator.translate_type_to_syn_type(&rewritten_ty)?;

                        let translated_val = self.translate_rvalue(loc, val)?;
                        let translated_place = self.translate_place(plc)?;

                        // this should be a temporary
                        assert!(plc.projection.is_empty());

                        let ot = self.ty_translator.translate_syn_type_to_op_type(&synty);
                        cont_stmt = radium::Stmt::Assign {
                            ot,
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                    } else {
                        let plc_ty = self.get_type_of_place(plc)?;
                        let rhs_ty = val.ty(&self.proc.get_mir().local_decls, self.env.tcx());

                        let borrow_annots = self.get_assignment_loan_annots(loc, val)?;
                        let (expr_annot, pre_stmt_annots, post_stmt_annots) =
                            self.get_assignment_annots(loc, plc, rhs_ty)?;

                        // TODO; maybe move this to rvalue
                        let composite_annots = self.get_composite_rvalue_creation_annots(loc, rhs_ty);

                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            post_stmt_annots,
                            Some("post-assignment".to_string()),
                        );

                        let translated_val = radium::Expr::with_optional_annotation(
                            self.translate_rvalue(loc, val)?,
                            expr_annot,
                            Some("assignment".to_string()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.ty_translator.translate_type_to_syn_type(&plc_ty.ty)?;
                        let ot = self.ty_translator.translate_syn_type_to_op_type(&synty);
                        cont_stmt = radium::Stmt::Assign {
                            ot,
                            e1: translated_place,
                            e2: translated_val,
                            s: Box::new(cont_stmt),
                        };
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            pre_stmt_annots,
                            Some("assignment".to_string()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            borrow_annots,
                            Some("borrow".to_string()),
                        );
                        cont_stmt = radium::Stmt::with_annotations(
                            cont_stmt,
                            composite_annots,
                            Some("composite".to_string()),
                        );
                    }
                },
                StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                    ()
                },
                StatementKind::SetDiscriminant {
                    place: _place,
                    variant_index: _variant_index,
                } =>
                // TODO
                {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "TODO: implement SetDiscriminant".to_string(),
                    });
                },
                StatementKind::PlaceMention(place) => {
                    // TODO: this is missed UB
                    info!("Ignoring PlaceMention: {:?}", place);
                    ()
                },
                StatementKind::Intrinsic(_intrinsic) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "TODO: implement Intrinsic".to_string(),
                    });
                },
                StatementKind::ConstEvalCounter =>
                // no-op
                {
                    ()
                },
                StatementKind::StorageLive(_) =>
                // just ignore
                {
                    ()
                },
                StatementKind::StorageDead(_) =>
                // just ignore
                {
                    ()
                },
                StatementKind::Deinit(_) =>
                // TODO: find out where this is emitted
                {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "Unsupported statement: Deinit".to_string(),
                    });
                },
                StatementKind::Retag(_, _) =>
                // just ignore retags
                {
                    ()
                },
                StatementKind::AscribeUserType(_, _) =>
                // don't need that info
                {
                    ()
                },
                StatementKind::Coverage(_) =>
                // don't need that
                {
                    ()
                },
                StatementKind::Nop =>
                // ignore
                {
                    ()
                },
            }
            cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.into_iter());
        }

        Ok(cont_stmt)
    }

    /// Translate a BorrowKind.
    fn translate_borrow_kind(&self, kind: &BorrowKind) -> Result<radium::BorKind, TranslationError> {
        match kind {
            BorrowKind::Shared => Ok(radium::BorKind::Shared),
            BorrowKind::Shallow =>
            // TODO: figure out what to do with this
            // arises in match lowering
            {
                Err(TranslationError::UnsupportedFeature {
                    description: "Do not support Shallow borrows currently".to_string(),
                })
            },
            BorrowKind::Mut { .. } => {
                // TODO: handle two-phase borrows?
                Ok(radium::BorKind::Mutable)
            },
        }
    }

    const fn translate_mutability(&self, mt: &Mutability) -> Result<radium::Mutability, TranslationError> {
        match mt {
            Mutability::Mut => Ok(radium::Mutability::Mut),
            Mutability::Not => Ok(radium::Mutability::Shared),
        }
    }

    /// Get the inner type of a type to which we can apply the offset operator.
    fn get_offset_ty(&self, ty: Ty<'tcx>) -> Result<Ty<'tcx>, TranslationError> {
        match ty.kind() {
            TyKind::Array(t, _) => Ok(*t),
            TyKind::Slice(t) => Ok(*t),
            TyKind::RawPtr(tm) => Ok(tm.ty),
            TyKind::Ref(_, t, _) => Ok(*t),
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
    ) -> Result<radium::Binop, TranslationError> {
        match op {
            BinOp::AddUnchecked => Ok(radium::Binop::AddOp),
            BinOp::SubUnchecked => Ok(radium::Binop::SubOp),
            BinOp::MulUnchecked => Ok(radium::Binop::MulOp),
            BinOp::ShlUnchecked => Ok(radium::Binop::ShlOp),
            BinOp::ShrUnchecked => Ok(radium::Binop::ShrOp),
            BinOp::Add => Ok(radium::Binop::AddOp),
            BinOp::Sub => Ok(radium::Binop::SubOp),
            BinOp::Mul => Ok(radium::Binop::MulOp),
            BinOp::Div => Ok(radium::Binop::DivOp),
            BinOp::Rem => Ok(radium::Binop::ModOp),
            BinOp::BitXor => Ok(radium::Binop::BitXorOp),
            BinOp::BitAnd => Ok(radium::Binop::BitAndOp),
            BinOp::BitOr => Ok(radium::Binop::BitOrOp),
            BinOp::Shl => Ok(radium::Binop::ShlOp),
            BinOp::Shr => Ok(radium::Binop::ShrOp),
            BinOp::Eq => Ok(radium::Binop::EqOp),
            BinOp::Lt => Ok(radium::Binop::LtOp),
            BinOp::Le => Ok(radium::Binop::LeOp),
            BinOp::Ne => Ok(radium::Binop::NeOp),
            BinOp::Ge => Ok(radium::Binop::GeOp),
            BinOp::Gt => Ok(radium::Binop::GtOp),
            BinOp::Offset => {
                // we need to get the layout of the thing we're offsetting
                // try to get the type of e1.
                let e1_ty = self.get_type_of_operand(e1)?;
                let off_ty = self.get_offset_ty(e1_ty)?;
                let st = self.ty_translator.translate_type_to_syn_type(&off_ty)?;
                let ly = self.ty_translator.translate_syn_type_to_layout(&st);
                Ok(radium::Binop::PtrOffsetOp(ly))
            },
        }
    }

    /// Translate checked binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_checked_binop(&self, op: BinOp) -> Result<radium::Binop, TranslationError> {
        match op {
            BinOp::Add => Ok(radium::Binop::CheckedAddOp),
            BinOp::Sub => Ok(radium::Binop::CheckedSubOp),
            BinOp::Mul => Ok(radium::Binop::CheckedMulOp),
            BinOp::Shl => Err(TranslationError::UnsupportedFeature {
                description: "checked Shl is not currently supported".to_string(),
            }),
            BinOp::Shr => Err(TranslationError::UnsupportedFeature {
                description: "checked Shr is not currently supported".to_string(),
            }),
            _ => Err(TranslationError::UnknownError(
                "unexpected checked binop that is not Add, Sub, Mul, Shl, or Shr".to_string(),
            )),
        }
    }

    /// Translate unary operators.
    fn translate_unop(&self, op: UnOp, ty: &Ty<'tcx>) -> Result<radium::Unop, TranslationError> {
        match op {
            UnOp::Not => match ty.kind() {
                ty::TyKind::Bool => Ok(radium::Unop::NotBoolOp),
                ty::TyKind::Int(_) => Ok(radium::Unop::NotIntOp),
                ty::TyKind::Uint(_) => Ok(radium::Unop::NotIntOp),
                _ => Err(TranslationError::UnknownError(
                    "application of UnOp::Not to non-{Int, Bool}".to_string(),
                )),
            },
            UnOp::Neg => Ok(radium::Unop::NegOp),
        }
    }

    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(
        &self,
        bk: BorrowKind,
        pl: &Place<'tcx>,
    ) -> Result<Option<radium::RustType>, TranslationError> {
        if let BorrowKind::Mut { .. } = bk {
            let ty = self.get_type_of_place(pl)?;
            // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
            let translated_ty = self.ty_translator.translate_type(&ty.ty)?;
            let annot_ty = radium::RustType::of_type(&translated_ty, &[]);
            Ok(Some(annot_ty))
        } else {
            Ok(None)
        }
    }

    /// Translates an Rvalue.
    fn translate_rvalue(
        &mut self,
        loc: Location,
        rval: &Rvalue<'tcx>,
    ) -> Result<radium::Expr, TranslationError> {
        match rval {
            Rvalue::Use(op) => {
                // converts an lvalue to an rvalue
                self.translate_operand(op, true)
            },

            Rvalue::Ref(region, bk, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_bk = self.translate_borrow_kind(bk)?;
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
                    let region = self.region_to_region_vid(*region);
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
                let translated_mt = self.translate_mutability(mt)?;

                Ok(radium::Expr::AddressOf {
                    mt: translated_mt,
                    e: Box::new(translated_pl),
                })
            },

            Rvalue::BinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1)?;
                let e2_ty = self.get_type_of_operand(e2)?;
                let e1_st = self.ty_translator.translate_type_to_syn_type(&e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(&e2_ty)?;
                let e1_ot = self.ty_translator.translate_syn_type_to_op_type(&e1_st);
                let e2_ot = self.ty_translator.translate_syn_type_to_op_type(&e2_st);

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = self.translate_binop(*op, &operands.as_ref().0, &operands.as_ref().1)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_ot,
                    ot2: e2_ot,
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            Rvalue::CheckedBinaryOp(op, operands) => {
                let e1 = &operands.as_ref().0;
                let e2 = &operands.as_ref().1;

                let e1_ty = self.get_type_of_operand(e1)?;
                let e2_ty = self.get_type_of_operand(e2)?;
                let e1_st = self.ty_translator.translate_type_to_syn_type(&e1_ty)?;
                let e2_st = self.ty_translator.translate_type_to_syn_type(&e2_ty)?;
                let e1_ot = self.ty_translator.translate_syn_type_to_op_type(&e1_st);
                let e2_ot = self.ty_translator.translate_syn_type_to_op_type(&e2_st);

                let translated_e1 = self.translate_operand(e1, true)?;
                let translated_e2 = self.translate_operand(e2, true)?;
                let translated_op = self.translate_checked_binop(*op)?;

                Ok(radium::Expr::BinOp {
                    o: translated_op,
                    ot1: e1_ot,
                    ot2: e2_ot,
                    e1: Box::new(translated_e1),
                    e2: Box::new(translated_e2),
                })
            },

            Rvalue::UnaryOp(op, operand) => {
                let translated_e1 = self.translate_operand(operand, true)?;
                let e1_ty = self.get_type_of_operand(operand)?;
                let e1_st = self.ty_translator.translate_type_to_syn_type(&e1_ty)?;
                let e1_ot = self.ty_translator.translate_syn_type_to_op_type(&e1_st);
                let translated_op = self.translate_unop(*op, &e1_ty)?;

                Ok(radium::Expr::UnOp {
                    o: translated_op,
                    ot: e1_ot,
                    e: Box::new(translated_e1),
                })
            },

            Rvalue::NullaryOp(op, _ty) => {
                // TODO: SizeOf
                Err(TranslationError::UnsupportedFeature {
                    description: "nullary ops (AlignOf, Sizeof) are not supported currently".to_string(),
                })
            },

            Rvalue::Discriminant(pl) => {
                let ty = self.get_type_of_place(pl)?;
                let translated_pl = self.translate_place(pl)?;
                info!("getting discriminant of {:?} at type {:?}", pl, ty);

                let ty::TyKind::Adt(adt_def, args) = ty.ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "We do not support discriminant accesses on non-enum types: {:?}; got type {:?}",
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
                let translated_it = self.ty_translator.translate_type(&it)?;

                let radium::Type::Int(translated_it) = translated_it else {
                    return Err(TranslationError::UnknownError(format!(
                        "type of discriminant is not an integer type {:?}",
                        it
                    )));
                };

                let ot = radium::OpType::IntOp(translated_it);

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
                    let type_of_o = self.get_type_of_operand(o)?;
                    translated_ops.push(translated_o);
                    operand_types.push(type_of_o);
                }

                match *kind {
                    box mir::AggregateKind::Tuple => {
                        if operand_types.is_empty() {
                            // translate to unit literal
                            return Ok(radium::Expr::Literal(radium::Literal::LitZST));
                        }

                        let struct_use =
                            self.ty_translator.generate_tuple_use(operand_types.iter().map(|r| *r))?;
                        let sl = struct_use.generate_raw_syn_type_term();
                        let initializers: Vec<_> =
                            translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                        Ok(radium::Expr::StructInitE {
                            sls: radium::CoqAppTerm::new_lhs(sl.to_string()),
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
                                return Ok(radium::Expr::Literal(radium::Literal::LitZST));
                            };

                            let sl = struct_use.generate_raw_syn_type_term();
                            let initializers: Vec<_> = translated_ops
                                .into_iter()
                                .zip(variant.fields.iter())
                                .map(|(o, field)| (field.name.to_string(), o))
                                .collect();

                            return Ok(radium::Expr::StructInitE {
                                sls: radium::CoqAppTerm::new_lhs(sl.to_string()),
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
                                sls: radium::CoqAppTerm::new_lhs(sl.to_string()),
                                components: initializers,
                            };

                            let enum_use = self.ty_translator.generate_enum_use(adt_def, args)?;
                            let els = enum_use.generate_raw_syn_type_term();

                            info!("generating enum annotation for type {:?}", enum_use);
                            let ty = radium::RustType::of_type(&radium::Type::Literal(enum_use), &[]);
                            let variant_name = variant_def.name.to_string();

                            return Ok(radium::Expr::EnumInitE {
                                els: radium::CoqAppTerm::new_lhs(els.to_string()),
                                variant: variant_name,
                                ty,
                                initializer: Box::new(variant_e),
                            });
                        }

                        // TODO
                        Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "TODO: implement Aggregate rvalue for other adts: {:?}",
                                rval
                            ),
                        })
                    },
                    box mir::AggregateKind::Closure(def, _args) => {
                        trace!("Translating Closure aggregate value for {:?}", def);

                        // We basically translate this to a tuple
                        if operand_types.is_empty() {
                            // translate to unit literal
                            return Ok(radium::Expr::Literal(radium::Literal::LitZST));
                        }

                        let struct_use =
                            self.ty_translator.generate_tuple_use(operand_types.iter().map(|r| *r))?;
                        let sl = struct_use.generate_raw_syn_type_term();

                        let initializers: Vec<_> =
                            translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                        Ok(radium::Expr::StructInitE {
                            sls: radium::CoqAppTerm::new_lhs(sl.to_string()),
                            components: initializers,
                        })
                    },

                    _ => {
                        // TODO
                        Err(TranslationError::UnsupportedFeature {
                            description: format!("TODO: implement Aggregate rvalue: {:?}", rval),
                        })
                    },
                }
            },

            Rvalue::Cast(kind, op, ty) => {
                let op_ty = self.get_type_of_operand(op)?;
                let translated_op = self.translate_operand(op, true)?;

                match kind {
                    mir::CastKind::PointerExposeAddress => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported rvalue: {:?}", rval),
                    }),

                    mir::CastKind::PointerFromExposedAddress => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported rvalue: {:?}", rval),
                    }),

                    mir::CastKind::PointerCoercion(x) => {
                        match x {
                            ty::adjustment::PointerCoercion::MutToConstPointer => {
                                // this is a NOP in our model
                                Ok(translated_op)
                            },
                            ty::adjustment::PointerCoercion::ArrayToPointer => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported rvalue: {:?}", rval),
                                })
                            },
                            ty::adjustment::PointerCoercion::ClosureFnPointer(_) => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported rvalue: {:?}", rval),
                                })
                            },
                            ty::adjustment::PointerCoercion::ReifyFnPointer => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported rvalue: {:?}", rval),
                                })
                            },
                            ty::adjustment::PointerCoercion::UnsafeFnPointer => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported rvalue: {:?}", rval),
                                })
                            },
                            ty::adjustment::PointerCoercion::Unsize => {
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported rvalue: {:?}", rval),
                                })
                            },
                        }
                    },

                    mir::CastKind::DynStar => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported dyn* cast"),
                    }),

                    mir::CastKind::IntToInt => {
                        // TODO
                        Err(TranslationError::Unimplemented {
                            description: format!("unsupported int-to-int cast"),
                        })
                    },

                    mir::CastKind::IntToFloat => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported int-to-float cast"),
                    }),

                    mir::CastKind::FloatToInt => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported float-to-int cast"),
                    }),

                    mir::CastKind::FloatToFloat => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported float-to-float cast"),
                    }),

                    mir::CastKind::PtrToPtr => {
                        match (op_ty.kind(), ty.kind()) {
                            (TyKind::RawPtr(_), TyKind::RawPtr(_)) => {
                                // Casts between raw pointers are NOPs for us
                                Ok(translated_op)
                            },
                            _ => {
                                // TODO: any other cases we should handle?
                                Err(TranslationError::UnsupportedFeature {
                                    description: format!("unsupported ptr-to-ptr cast: {:?}", rval),
                                })
                            },
                        }
                    },

                    mir::CastKind::FnPtrToPtr => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported fnptr-to-ptr cast: {:?}", rval),
                    }),

                    mir::CastKind::Transmute => Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported transmute cast: {:?}", rval),
                    }),
                }
            },

            Rvalue::Len(..) => Err(TranslationError::UnsupportedFeature {
                description: format!("unsupported rvalue: {:?}", rval),
            }),

            Rvalue::Repeat(..) => Err(TranslationError::UnsupportedFeature {
                description: format!("unsupported rvalue: {:?}", rval),
            }),

            Rvalue::ThreadLocalRef(..) => Err(TranslationError::UnsupportedFeature {
                description: format!("unsupported rvalue: {:?}", rval),
            }),

            Rvalue::ShallowInitBox(_, _) => Err(TranslationError::UnsupportedFeature {
                description: format!("unsupported rvalue: {:?}", rval),
            }),

            Rvalue::CopyForDeref(_) => Err(TranslationError::UnsupportedFeature {
                description: format!("unsupported rvalue: {:?}", rval),
            }),
        }
    }

    /// Make a trivial place accessing `local`.
    fn make_local_place(&self, local: &Local) -> Place<'tcx> {
        Place {
            local: *local,
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
    ) -> Result<radium::Expr, TranslationError> {
        match op {
            // In Caesium: typed_place needs deref (not use) for place accesses.
            // use is used top-level to convert an lvalue to an rvalue, which is why we use it here.
            Operand::Copy(ref place) | Operand::Move(ref place) => {
                // check if this goes to a temporary of a checked op
                let translated_place;
                let ty;
                if self.checked_op_temporaries.contains_key(&place.local) {
                    assert!(place.projection.len() == 1);
                    let proj = place.projection[0];
                    match proj {
                        ProjectionElem::Field(f, _0) => {
                            if f.index() == 0 {
                                // access to the result of the op
                                let new_place = self.make_local_place(&place.local);
                                translated_place = self.translate_place(&new_place)?;
                                ty = self.get_type_of_place(place)?;
                            } else {
                                // make this a constant false -- our semantics directly checks for overflows
                                // and otherwise throws UB.
                                translated_place = radium::Expr::Literal(radium::Literal::LitBool(false));
                                //ty = self.get_type_of_place(place)?;
                                return Ok(translated_place);
                            }
                        },
                        _ => {
                            panic!("invariant violation for access to checked op temporary");
                        },
                    }
                } else {
                    translated_place = self.translate_place(place)?;
                    ty = self.get_type_of_place(place)?;
                }

                let st = self.ty_translator.translate_type_to_syn_type(&ty.ty)?;
                let ot = self.ty_translator.translate_syn_type_to_op_type(&st);
                if to_rvalue {
                    Ok(radium::Expr::Use {
                        ot,
                        e: Box::new(translated_place),
                    })
                } else {
                    Ok(translated_place)
                }
            },
            Operand::Constant(ref constant) => {
                // TODO: possibly need different handling of the rvalue flag
                // when this also handles string literals etc.
                return self.translate_constant(constant.as_ref());
            },
        }
    }

    fn translate_fn_def_use(&mut self, ty: Ty<'tcx>) -> Result<radium::Expr, TranslationError> {
        match ty.kind() {
            TyKind::FnDef(defid, params) => {
                let key: ty::ParamEnv<'tcx> = self.env.tcx().param_env(self.proc.get_id());
                if self.env.tcx().trait_of_item(*defid).is_some() {
                    if let Some((resolved_did, resolved_params, kind)) =
                        crate::traits::resolve_assoc_item(self.env.tcx(), key, *defid, params)
                    {
                        info!(
                            "Resolved trait method {:?} as {:?} with substs {:?} and kind {:?}",
                            defid, resolved_did, resolved_params, kind
                        );
                        match kind {
                            crate::traits::TraitResolutionKind::UserDefined => {
                                let param_name =
                                    self.register_use_procedure(&resolved_did, resolved_params)?;
                                Ok(radium::Expr::MetaParam(param_name))
                            },
                            crate::traits::TraitResolutionKind::Param => {
                                Err(TranslationError::Unimplemented {
                                    description: format!("Implement trait invocation for Param"),
                                })
                            },
                            crate::traits::TraitResolutionKind::Closure => {
                                // TODO: here, we should first generate an instance of the trait
                                //self.env.tcx().
                                // mir_shims(rustc_middle::ty::InstanceDef::Item(resolved_did));
                                // the args are just the closure args. We can ignore them.
                                let _clos_args = resolved_params.as_closure();
                                let param_name =
                                    self.register_use_procedure(&resolved_did, ty::List::empty())?;
                                Ok(radium::Expr::MetaParam(param_name))
                                //Err(TranslationError::Unimplemented { description: format!("Implement trait
                                // invocation for Closure") })
                            },
                        }
                    } else {
                        Err(TranslationError::TraitResolution(format!("Could not resolve trait {:?}", defid)))
                    }
                } else {
                    // track that we are using this function and generate the Coq location name
                    let param_name = self.register_use_procedure(defid, params)?;
                    Ok(radium::Expr::MetaParam(param_name))
                }
            },
            _ => Err(TranslationError::UnknownError("not a FnDef type".to_string())),
        }
    }

    /// Translate a scalar at a specific type to a radium::Expr.
    // TODO: Use `TryFrom` instead
    fn translate_scalar(&mut self, sc: &Scalar, ty: Ty<'tcx>) -> Result<radium::Expr, TranslationError> {
        // TODO: Use `TryFrom` instead
        fn translate_literal<T, U>(
            sc: Result<T, U>,
            fptr: fn(T) -> radium::Literal,
        ) -> Result<radium::Expr, TranslationError> {
            sc.map_or(Err(TranslationError::InvalidLayout), |lit| Ok(radium::Expr::Literal(fptr(lit))))
        }

        match ty.kind() {
            TyKind::Int(it) => {
                match it {
                    ty::IntTy::I8 => translate_literal(sc.to_i8(), radium::Literal::LitI8),
                    ty::IntTy::I16 => translate_literal(sc.to_i16(), radium::Literal::LitI16),
                    ty::IntTy::I32 => translate_literal(sc.to_i32(), radium::Literal::LitI32),
                    ty::IntTy::I64 => translate_literal(sc.to_i64(), radium::Literal::LitI64),
                    ty::IntTy::I128 => translate_literal(sc.to_i128(), radium::Literal::LitI128),
                    // for radium, the pointer size is 8 bytes
                    ty::IntTy::Isize => translate_literal(sc.to_i64(), radium::Literal::LitI64),
                }
            },

            TyKind::Uint(it) => {
                match it {
                    ty::UintTy::U8 => translate_literal(sc.to_u8(), radium::Literal::LitU8),
                    ty::UintTy::U16 => translate_literal(sc.to_u16(), radium::Literal::LitU16),
                    ty::UintTy::U32 => translate_literal(sc.to_u32(), radium::Literal::LitU32),
                    ty::UintTy::U64 => translate_literal(sc.to_u64(), radium::Literal::LitU64),
                    ty::UintTy::U128 => translate_literal(sc.to_u128(), radium::Literal::LitU128),
                    // for radium, the pointer size is 8 bytes
                    ty::UintTy::Usize => translate_literal(sc.to_u64(), radium::Literal::LitU64),
                }
            },

            TyKind::Bool => translate_literal(sc.to_bool(), radium::Literal::LitBool),

            TyKind::FnDef(_, _) => self.translate_fn_def_use(ty),

            TyKind::Tuple(tys) => {
                if tys.is_empty() {
                    Ok(radium::Expr::Literal(radium::Literal::LitZST))
                } else {
                    Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "Currently do not support compound construction of tuples using literals: {:?}",
                            ty
                        ),
                    })
                }
            },

            TyKind::Ref(_, _, _) => match sc {
                Scalar::Int(_) => {
                    unreachable!();
                },
                Scalar::Ptr(pointer, _) => {
                    let glob_alloc = self.env.tcx().global_alloc(pointer.provenance);
                    match glob_alloc {
                        rustc_middle::mir::interpret::GlobalAlloc::Static(did) => {
                            info!(
                                "Found static GlobalAlloc {:?} for Ref scalar {:?} at type {:?}",
                                did, sc, ty
                            );
                            match self.const_registry.statics.get(&did) {
                                None => Err(TranslationError::UnknownError(format!(
                                    "Did not find a registered static for GlobalAlloc {:?} for scalar {:?} at type {:?}; registered: {:?}",
                                    glob_alloc, sc, ty, self.const_registry.statics
                                ))),
                                Some(s) => {
                                    self.collected_statics.insert(did);
                                    Ok(radium::Expr::Literal(radium::Literal::LitLoc(s.loc_name.clone())))
                                },
                            }
                        },
                        _ => Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "Unsupported GlobalAlloc {:?} for scalar {:?} at type {:?}",
                                glob_alloc, sc, ty
                            ),
                        }),
                    }
                },
            },

            _ => Err(TranslationError::UnsupportedFeature {
                description: format!("Unsupported layout for const value: {:?}", ty),
            }),
        }
    }

    /// Translate a Constant to a radium::Expr.
    fn translate_constant(&mut self, constant: &Constant<'tcx>) -> Result<radium::Expr, TranslationError> {
        match constant.literal {
            ConstantKind::Ty(v) => {
                let const_ty = v.ty();

                match v.kind() {
                    ConstKind::Value(ref v) => {
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
                        description: "Unsupported ConstKind".to_string(),
                    }),
                }
            },
            ConstantKind::Val(val, ty) => {
                match val {
                    ConstValue::Scalar(sc) => self.translate_scalar(&sc, ty),
                    ConstValue::ZeroSized => {
                        // TODO are there more special cases we need to handle somehow?
                        match ty.kind() {
                            TyKind::FnDef(_, _) => {
                                info!("Translating ZST val for function call target: {:?}", ty);
                                self.translate_fn_def_use(ty)
                            },
                            _ => Ok(radium::Expr::Literal(radium::Literal::LitZST)),
                        }
                    },
                    _ => {
                        // TODO: do we actually care about this case or is this just something that can
                        // appear as part of CTFE/MIRI?
                        Err(TranslationError::UnsupportedFeature {
                            description: format!("Unsupported Constant: ConstValue; {:?}", constant.literal),
                        })
                    },
                }
            },
            ConstantKind::Unevaluated(_, _) => Err(TranslationError::UnsupportedFeature {
                description: format!("Unsupported Constant: Unevaluated; {:?}", constant.literal),
            }),
        }
    }

    /// Translate a place to a Caesium lvalue.
    fn translate_place(&mut self, pl: &Place<'tcx>) -> Result<radium::Expr, TranslationError> {
        // Get the type of the underlying local. We will use this to
        // get the necessary layout information for dereferencing
        let mut cur_ty = self.get_type_of_local(&pl.local).map(PlaceTy::from_ty)?;

        let local_name = self
            .variable_map
            .get(&pl.local)
            .ok_or_else(|| TranslationError::UnknownVar(format!("{:?}", pl.local)))?;

        let mut acc_expr: radium::Expr = radium::Expr::Var(local_name.to_string());

        // iterate in evaluation order
        for ref it in pl.projection {
            match it {
                ProjectionElem::Deref => {
                    // use the type of the dereferencee
                    let st = self.ty_translator.translate_type_to_syn_type(&cur_ty.ty)?;
                    let ot = self.ty_translator.translate_syn_type_to_op_type(&st);
                    acc_expr = radium::Expr::Deref {
                        ot,
                        e: Box::new(acc_expr),
                    };
                },
                ProjectionElem::Field(f, _) => {
                    // `t` is the type of the field we are accessing!
                    let lit = self.ty_translator.generate_structlike_use(&cur_ty.ty, cur_ty.variant_index)?;
                    // TODO: does not do the right thing for accesses to fields of zero-sized objects.
                    let struct_sls = lit.map_or(radium::SynType::Unit, |x| x.generate_raw_syn_type_term());
                    let name = self.ty_translator.translator.get_field_name_of(
                        f,
                        cur_ty.ty,
                        cur_ty.variant_index.map(|a| a.as_usize()),
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
                        description: "places: implement index access".to_string(),
                    });
                },
                ProjectionElem::ConstantIndex { .. } => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement const index access".to_string(),
                    });
                },
                ProjectionElem::Subslice { .. } => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement subslicing".to_string(),
                    });
                },
                ProjectionElem::Downcast(_, variant_idx) => {
                    info!("Downcast of ty {:?} to {:?}", cur_ty, variant_idx);
                    if let ty::TyKind::Adt(def, args) = cur_ty.ty.kind() {
                        if def.is_enum() {
                            let enum_use = self.ty_translator.generate_enum_use(*def, args.iter())?;
                            let els = enum_use.generate_raw_syn_type_term();

                            let variant_name =
                                self.ty_translator.translator.get_variant_name_of(cur_ty.ty, *variant_idx)?;

                            acc_expr = radium::Expr::EnumData {
                                els: els.to_string(),
                                variant: variant_name,
                                e: Box::new(acc_expr),
                            }
                        } else {
                            return Err(TranslationError::UnknownError(
                                "places: ADT downcasting on non-enum type".to_string(),
                            ));
                        }
                    } else {
                        return Err(TranslationError::UnknownError(
                            "places: ADT downcasting on non-enum type".to_string(),
                        ));
                    }
                },
                ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement opaque casts".to_string(),
                    });
                },
            };
            // update cur_ty
            cur_ty = cur_ty.projection_ty(self.env.tcx(), *it);
        }
        info!("translating place {:?} to {:?}", pl, acc_expr);
        Ok(acc_expr)
    }

    /// Get the type of a local in a body.
    fn get_type_of_local(&self, local: &Local) -> Result<Ty<'tcx>, TranslationError> {
        self.proc
            .get_mir()
            .local_decls
            .get(*local)
            .map(|decl| decl.ty)
            .ok_or_else(|| TranslationError::UnknownVar("".to_string()))
    }

    /// Get the type of a place expression.
    fn get_type_of_place(&self, pl: &Place<'tcx>) -> Result<PlaceTy<'tcx>, TranslationError> {
        Ok(pl.ty(&self.proc.get_mir().local_decls, self.env.tcx()))
    }

    /// Get the type of a const.
    fn get_type_of_const(&self, cst: &Constant<'tcx>) -> Result<Ty<'tcx>, TranslationError> {
        match cst.literal {
            ConstantKind::Ty(cst) => Ok(cst.ty()),
            ConstantKind::Val(_, ty) => Ok(ty),
            ConstantKind::Unevaluated(_, ty) => Ok(ty),
        }
    }

    /// Get the type of an operand.
    fn get_type_of_operand(&self, op: &Operand<'tcx>) -> Result<Ty<'tcx>, TranslationError> {
        Ok(op.ty(&self.proc.get_mir().local_decls, self.env.tcx()))
    }
}
