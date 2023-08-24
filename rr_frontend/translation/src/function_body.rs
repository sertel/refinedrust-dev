// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info};

use rustc_ast::ast::Attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty as ty;
use rustc_middle::ty::{Ty, TyKind, ConstKind};
use rustc_middle::mir;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::tcx::PlaceTy;
use rustc_middle::mir::{Location, StatementKind, BinOp, UnOp, Rvalue, Place, VarDebugInfoContents, LocalKind, Local, BasicBlock, BasicBlockData, Terminator, Body, Constant, TerminatorKind, Operand, ConstantKind, ProjectionElem, BorrowKind, Mutability};
use crate::rustc_middle::ty::TypeFoldable;

use std::collections::{HashMap, HashSet};

use crate::environment::borrowck::facts as facts;
use crate::environment::procedure::Procedure;
use crate::environment::polonius_info as info;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::Environment;

use crate::checked_op_analysis::CheckedOpLocalAnalysis;
use crate::caesium;

use crate::verbose_function_spec_parser::{FunctionSpecParser, VerboseFunctionSpecParser};

use crate::rrconfig as rrconfig;

use crate::tyvars::*;
pub use crate::base::*;
use crate::type_translator::*;
use crate::inclusion_tracker::*;


/**
 * Tracks the functions we translated and the Coq names they are available under.
 * To account for dependencies between functions, we may register translated names before we have
 * actually translated the function.
 */
pub struct ProcedureScope<'def> {
    /// maps the defid to (code_name, spec_name, name)
    name_map: HashMap<DefId, (String, String)>,
    /// track the actually translated functions
    translated_functions: HashMap<DefId, caesium::Function<'def>>,
}

impl<'def> ProcedureScope<'def> {
    pub fn new() -> Self {
        Self {
            name_map: HashMap::new(),
            translated_functions: HashMap::new(),
        }
    }

    /// Lookup the Coq spec name for a function.
    pub fn lookup_function_spec_name(&self, did: &DefId) -> Option<&str> {
        self.name_map.get(did).map(|(b, _)| &b[..])
    }

    /// Lookup the name for a function.
    pub fn lookup_function_mangled_name(&self, did: &DefId) -> Option<&str> {
        //info!("lookup up function {:?} in map {:?}", did, self.name_map);
        self.name_map.get(did).map(|(_, c)| &c[..])
    }

    /// Register a function.
    pub fn register_function(&mut self, did: &DefId, spec_name: &str, name: &str) {
        assert!(self.name_map.insert(*did, (spec_name.to_string(), name.to_string())).is_none());
    }

    /// Provide the code for a translated function.
    pub fn provide_translated_function(&mut self, did: &DefId, trf: caesium::Function<'def>) {
        assert!(self.name_map.get(did).is_some());
        assert!(self.translated_functions.insert(*did, trf).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub fn iter_code(&self) -> std::collections::hash_map::Iter<'_, DefId, caesium::Function<'def>> {
        self.translated_functions.iter()
    }
}


/**
 * Struct that keeps track of all information necessary to translate a MIR Body to a caesium::Function.
 * `'a` is the lifetime of the translator and ends after translation has finished.
 * `'def` is the lifetime of the generated code (the code may refer to struct defs).
 * `'tcx' is the lifetime of the rustc tctx.
 */
pub struct BodyTranslator<'a, 'def, 'tcx> {
    env: &'def Environment<'tcx>,
    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// maps locals to variable names
    variable_map: HashMap<Local, String>,
    /// the Caesium function buildder
    translated_fn: caesium::FunctionBuilder<'def>,
    /// name of the return variable
    return_name: String,
    /// syntactic type of the thing to return
    return_synty: caesium::SynType,
    /// all the types used in this function
    collected_types: HashSet<Ty<'tcx>>,
    /// all the other procedures used by this function, and:
    /// (code_loc_parameter_name, spec_name, type_inst, syntype_of_all_args)
    collected_procedures: HashMap<(DefId, FnGenericKey<'tcx>), (String, String, Vec<caesium::Type<'def>>, Vec<caesium::SynType>)>,

    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a ProcedureScope<'def>,
    /// attributes on this function
    attrs: &'a[Attribute],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// local lifetimes: the LHS is the lifetime name, the RHS are the super lifetimes
    local_lifetimes: Vec<(caesium::specs::Lft, Vec<caesium::specs::Lft>)>,
    /// data structures for tracking which basic blocks still need to be translated
    /// (we only translate the basic blocks which are actually reachable, in particular when
    /// skipping unwinding)
    bb_queue: Vec<BasicBlock>,
    /// set of already processed blocks
    processed_bbs: HashSet<BasicBlock>,
    /// translator for types
    ty_translator: &'a TypeTranslator<'def, 'tcx>,

    /// defids of purely spec fns.
    spec_fns: &'a HashSet<DefId>,
    /// map of loop heads to their optional spec closure defid
    loop_specs: HashMap<BasicBlock, Option<DefId>>,

    /// relevant locals: (local, name, type)
    fn_locals: Vec<(Local, String, caesium::Type<'def>)>,

    /// inputs of the function, with both early and late bound regions substituted with their
    /// Polonius ReVar
    inputs: Vec<Ty<'tcx>>,
    /// output of the function, similarly with substituted regions
    output: Ty<'tcx>,

    /// result temporaries of checked ops that we rewrite
    /// we assume that this place is typed at (result_type, bool)
    /// and rewrite accesses to the first component to directly use the place,
    /// while rewriting accesses to the second component to true.
    /// TODO: once we handle panics properly, we should use a different translation.
    /// NOTE: we only rewrite for uses, as these are the only places these are used.
    checked_op_temporaries: HashMap<Local, Ty<'tcx>>,
}

impl<'a, 'def : 'a, 'tcx : 'def> BodyTranslator<'a, 'def, 'tcx> {

    /// Generate a unique string identifier for a basic block.
    /// This function is deterministic, so subsequent calls with the same `BasicBlock` will always
    /// generate the same name.
    fn make_bb_name(bb_idx: &BasicBlock) -> String {
        // NOTE: initial bb name needs to line up with caesium::FunctionCode::initial_bb!
        let mut bb_name = "_bb".to_string();
        bb_name.push_str(&bb_idx.index().to_string());
        bb_name
    }

    /// Generate a string identifier for a Local.
    /// Tries to find the Rust source code name of the local,
    /// otherwise simply enumerates.
    /// This function is deterministic, so subsequent calls with the same `Local` will always
    /// generate the same name.
    fn make_local_name(mir_body: &Body<'tcx>, local: &Local) -> String {
        if let Some(mir_name) = Self::find_name_for_local(mir_body, local) {
            strip_coq_ident(&mir_name)
        }
        else {
            let mut name = "__".to_string();
            name.push_str(&local.index().to_string());
            name
        }
    }

    /// Find a source name for a local of a MIR body, if possible.
    fn find_name_for_local(body : &mir::Body<'tcx>, local : &mir::Local) -> Option<String> {
        let debug_info = &body.var_debug_info;
        for dbg in debug_info {
            let name = &dbg.name;
            let val = &dbg.value;
            match *val {
                VarDebugInfoContents::Place(l) => {
                    // TODO: make sure that l.projection is empty?
                    if l.local == *local {
                        return Some(name.as_str().to_string());
                    }
                },
                VarDebugInfoContents::Const(_) => {
                    // is this case used when constant propagation happens during MIR construction?
                },
                VarDebugInfoContents::Composite { ty: _, fragments: _ } => {
                    // Not sure
                },
            }
        }

        return None;
    }

    /// Generate a key for generics to index into our map of other required procedures.
    fn generate_procedure_inst_key(&self, ty_params: ty::GenericArgsRef<'tcx>) -> Result<FnGenericKey<'tcx>, TranslationError> {
        // erase parameters to their syntactic types
        let mut key = Vec::new();
        let mut region_eraser = TyRegionEraseFolder::new(self.env.tcx());
        for p in ty_params.iter() {
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
                    return Err(TranslationError::UnsupportedFeature{description:
                        "RefinedRust does not support const generics".to_string()})
                },
            }
        }
        Ok(key)
    }

    /// Internally register that we have used a procedure with a particular instantiation of generics, and return the code parameter name.
    fn register_use_procedure(&mut self, did: &DefId, ty_params: ty::GenericArgsRef<'tcx>) -> Result<String, TranslationError> {
        let key = self.generate_procedure_inst_key(ty_params)?;

        let tup = (*did, key);
        if let Some((n, ..)) = self.collected_procedures.get(&tup) {
            Ok(format!("{}", n))
        }
        else {
            // lookup the name in the procedure registry

            let name = self.procedure_registry.lookup_function_mangled_name(did).ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", did)))?;
            let spec_name = self.procedure_registry.lookup_function_spec_name(did).ok_or_else(|| TranslationError::UnknownProcedure(format!("{:?}", did)))?;

            let mut mangled_name = name.to_string();
            let mut translated_params = Vec::new();
            let generic_env = &*self.ty_translator.generic_scope.borrow();

            // TODO: maybe come up with some better way to generate names
            for p in tup.1.iter() {
                mangled_name.push_str(format!("_{}", p).as_str());

                let mut translated_ty = self.ty_translator.translate_type(p)?;
                // we need to substitute in the variables according to the function scope
                translated_ty.subst(generic_env.as_slice());

                translated_params.push(translated_ty);
            }
            let mangled_name = strip_coq_ident(&mangled_name);

            // also gather all the layouts of the arguments.
            let full_ty: ty::EarlyBinder<Ty<'tcx>> = self.env.tcx().type_of(*did);
            let full_ty: Ty<'tcx> = full_ty.instantiate_identity();
            let sig = full_ty.fn_sig(self.env.tcx());

            let inputs = sig.inputs().skip_binder();
            let mut syntypes = Vec::new();
            //info!("substs: {:?}, inputs {:?} ", ty_params, inputs);
            for i in inputs.iter() {
                // need to wrap it, because there's no Subst instance for Ty
                let i = ty::EarlyBinder::bind(*i);
                let ty = i.instantiate(self.env.tcx(), ty_params);
                let t = self.ty_translator.translate_type_to_syn_type(&ty)?;
                syntypes.push(t);
            }

            let loc_name = format!("{}_loc", mangled_name);
            info!("Registered procedure instance {} of {:?} with {:?} and layouts {:?}", mangled_name, did, translated_params, syntypes);
            self.collected_procedures.insert(tup, (loc_name.clone(), spec_name.to_string(), translated_params, syntypes));
            Ok(loc_name)
        }
    }

    pub fn dump_body(body: &Body) {
        // TODO: print to file
        let basic_blocks = &body.basic_blocks;
        for (bb_idx, bb) in basic_blocks.iter_enumerated() {
            Self::dump_basic_block(&bb_idx, bb);
        };
    }

    /// Translate the body of a function.
    pub fn new(env: &'def Environment<'tcx>, fname: String, proc: Procedure<'tcx>, attrs: &'a [Attribute], ty_translator: &'def TypeTranslator<'def, 'tcx>, proc_registry: &'a ProcedureScope<'def>, spec_fns: &'a HashSet<DefId>) -> Result<Self , TranslationError> {
        let fname = strip_coq_ident(&fname);
        let mut translated_fn = caesium::FunctionBuilder::new(&fname);

        // TODO can we avoid the leak
        let proc: &'def Procedure = &*Box::leak(Box::new(proc));

        let mut return_synty = caesium::SynType::Unit; // default
        let body = proc.get_mir();
        // dump debug info
        Self::dump_body(body);

        let ty: ty::EarlyBinder<Ty<'tcx>> = env.tcx().type_of(proc.get_id());
        let ty = ty.instantiate_identity();
        let (sig, substs) = match ty.kind() {
            TyKind::FnDef(_def, args) => {
                assert!(ty.is_fn());
                let sig = ty.fn_sig(env.tcx());
                (sig, args)
            }
            _ => panic!("can not handle non-fns")
        };

        match PoloniusInfo::new(env, proc) {
            Ok(info) => {
                // TODO: avoid leak
                let info: &'def PoloniusInfo = &*Box::leak(Box::new(info));

                let params = proc.get_type_params();

                // dump graphviz files
                // color code: red: dying loan, pink: becoming a zombie; green: is zombie
                crate::environment::dump_borrowck_info(&*env, &proc.get_id(), &info);


                let mut universal_lifetimes = Vec::new();
                let mut user_lifetime_names = Vec::new();

                // we create a substitution that replaces early bound regions with their Polonius
                // region variables
                let mut subst_early_bounds: Vec<ty::GenericArg<'tcx>> = Vec::new();
                let mut num_early_bounds = 0;
                for a in substs.iter() {
                    match a.unpack() {
                        ty::GenericArgKind::Lifetime(r) => {
                            // skip over 0 = static
                            let revar = ty::Region::new_var(env.tcx(), ty::RegionVid::from_u32(num_early_bounds + 1));
                            num_early_bounds += 1;
                            subst_early_bounds.push(ty::GenericArg::from(revar));

                            match *r {
                                ty::RegionKind::ReEarlyBound(r) => {
                                    universal_lifetimes.push(strip_coq_ident(&format!("ulft_{}", r.name.to_string())));
                                    user_lifetime_names.push(Some(strip_coq_ident(r.name.as_str())));
                                },
                                _ => {
                                    universal_lifetimes.push(format!("ulft{}", num_early_bounds));
                                    user_lifetime_names.push(None);
                                },
                            }
                            //println!("early region {}", r);
                        },
                        _ => {
                            subst_early_bounds.push(a);
                        },
                    }
                }
                let subst_early_bounds = env.tcx().mk_args(&subst_early_bounds);

                // add names for late bound region variables
                let mut num_late_bounds = 0;
                for b in sig.bound_vars().iter() {
                    match b {
                        ty::BoundVariableKind::Region(r) => {
                            match r {
                                ty::BoundRegionKind::BrNamed(_, sym) => {
                                    universal_lifetimes.push(strip_coq_ident(&format!("ulft_{}", sym.to_string())));
                                    user_lifetime_names.push(Some(strip_coq_ident(sym.as_str())));
                                },
                                ty::BoundRegionKind::BrAnon(_) => {
                                    universal_lifetimes.push(format!("ulft{}", num_early_bounds + num_late_bounds + 1));
                                    user_lifetime_names.push(None);
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
                let mut folder =
                    |_| {
                        let cur_index = next_index;
                        next_index += 1;
                        ty::Region::new_var(env.tcx(),ty::RegionVid::from_u32(cur_index))
                    };
                let (late_sig, _late_region_map) = env.tcx().replace_late_bound_regions(sig, &mut folder);

                let inputs: Vec<_> = late_sig.inputs().iter().map(|ty| {
                    let wrapped_ty = ty::EarlyBinder::bind(*ty);
                    wrapped_ty.instantiate(env.tcx(), subst_early_bounds) }).collect();
                let output = ty::EarlyBinder::bind(late_sig.output());
                let output = output.instantiate(env.tcx(), subst_early_bounds);

                info!("Have lifetime parameters: {:?} {:?}", universal_lifetimes, user_lifetime_names);

                // add universal lifetimes to the spec
                for (lft, name) in universal_lifetimes.iter().zip(user_lifetime_names.into_iter()) {
                    //let lft = info::AtomicRegion::Universal(info::UniversalRegionKind::Local, ty::RegionVid::from_u32(1+r));
                    translated_fn.add_universal_lifetime(name, lft.to_string()).map_err(|e| TranslationError::UnknownError(e))?;
                }

                let mut inclusion_tracker = InclusionTracker::new(info);
                // add placeholder subsets
                let initial_point: facts::Point = facts::Point {location: BasicBlock::from_u32(0).start_location(), typ: facts::PointType::Start};
                for (r1, r2) in info.borrowck_in_facts.known_placeholder_subset.iter() {
                    inclusion_tracker.add_static_inclusion(*r1, *r2, info.interner.get_point_index(&initial_point));
                }

                // enter the procedure
                ty_translator.enter_procedure(&params, universal_lifetimes)?;
                // add generic args to the fn
                let generics = ty_translator.generic_scope.borrow();
                for t in generics.iter() {
                    if let Some(t) = t {
                        translated_fn.add_generic_type(&t);
                    }
                }

                // analyze which locals are used for the result of checked-ops, because we will
                // override their types (eliminating the tuples)
                let mut checked_op_analyzer = CheckedOpLocalAnalysis::new(env.tcx(), body);
                checked_op_analyzer.analyze();
                let checked_op_locals = checked_op_analyzer.results();

                // we collect the types used for locals to generate the right requirements on refinements of mutable
                // references
                // TODO: remove
                let mut collected_types = HashSet::new();

                // map to translate between locals and the string names we use in caesium::
                let mut caesium_name_map: HashMap<Local, String> = HashMap::new();

                let local_decls = &body.local_decls;
                info!("Have {} local decls\n", local_decls.len());

                let mut fn_locals = Vec::new();
                let mut opt_return_name = Err(TranslationError::UnknownError("could not find local for return value".to_string()));
                // go over local_decls and create the right caesium:: stack layout
                for (local, local_decl) in local_decls.iter_enumerated() {
                    let kind = body.local_kind(local);
                    let ty : &Ty<'tcx>;
                    if let Some(rewritten_ty) = checked_op_locals.get(&local) {
                        ty = rewritten_ty;
                    }
                    else {
                        ty = &local_decl.ty;
                    }

                    // check if the type is of a spec fn -- in this case, we can skip this temporary
                    if let TyKind::Closure(id, _) = ty.kind() {
                        if spec_fns.contains(&id) {
                            // this is a spec fn
                            info!("skipping local which has specfn closure type: {:?}", local);
                            continue;
                        }
                    }

                    // type:
                    let tr_ty = ty_translator.translate_type(ty)?;
                    let mut st = tr_ty.get_syn_type();
                    st.subst(ty_translator.synty_scope.borrow().as_ref());

                    let name = Self::make_local_name(body, &local);
                    caesium_name_map.insert(local, name.to_string());

                    fn_locals.push((local, name.clone(), tr_ty));

                    match kind {
                        LocalKind::Arg => translated_fn.code.add_argument(&name, st),
                        //LocalKind::Var => translated_fn.code.add_local(&name, st),
                        LocalKind::Temp => translated_fn.code.add_local(&name, st),
                        LocalKind::ReturnPointer => {
                            return_synty = st.clone();
                            translated_fn.code.add_local(&name, st);
                            opt_return_name = Ok(name);
                        }
                    }

                    collected_types.insert(*ty);
                }
                // create the function
                let return_name = opt_return_name?;

                /*
                info!("function uses the following types for its local computation");
                for ty in collected_types.iter() {
                    info!("{:?}", *ty);
                }
                info!("\n");
                */

                let t = BodyTranslator {env, proc, info,
                    variable_map: caesium_name_map,
                    translated_fn,
                    return_name, return_synty,
                    collected_types, inclusion_tracker,
                    collected_procedures: HashMap::new(),
                    procedure_registry: proc_registry,
                    attrs,
                    local_lifetimes: Vec::new(),
                    spec_fns,
                    bb_queue: Vec::new(),
                    processed_bbs: HashSet::new(),
                    ty_translator,
                    loop_specs: HashMap::new(),
                    fn_locals,
                    inputs, output,
                    checked_op_temporaries: checked_op_locals,
                };
                Ok(t)
            },
            Err(err) => {
                Err(TranslationError::UnknownError(format!("{:?}", err)))
            }
        }
    }

    /// Parse and process attributes of this function.
    pub fn process_attrs(&mut self) -> Result<(), TranslationError> {
        let a = self.attrs;
        let v = crate::utils::filter_tool_attrs(a);
        let inputs = &self.inputs;
        let output = &self.output;

        info!("inputs: {:?}, output: {:?}", inputs, output);
        let mut translated_arg_types: Vec<caesium::Type<'def>> = Vec::new();
        let generic_env = &*self.ty_translator.generic_scope.borrow();
        for arg in inputs.iter() {
            let mut translated: caesium::Type<'def> = self.ty_translator.translate_type(arg)?;
            translated.subst(generic_env.as_slice());
            translated_arg_types.push(translated);
        }
        let mut translated_ret_type: caesium::Type<'def> = self.ty_translator.translate_type(output)?;
        translated_ret_type.subst(generic_env.as_slice());
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let rfnty_scope = self.ty_translator.rfnty_scope.borrow();

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                let mut parser: VerboseFunctionSpecParser<'_, 'def> = VerboseFunctionSpecParser::new(&translated_arg_types, &translated_ret_type, &rfnty_scope);
                parser.parse_function_spec(v.as_slice(), &mut self.translated_fn).map_err(|e| TranslationError::AttributeError(e))?;
                Ok(())
            },
            _ => {
                Err(TranslationError::UnknownAttributeParser(parser))
            },
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


    /// Enqueues a basic block for processing, if it has not already been processed,
    /// and marks it as having been processed.
    fn enqueue_basic_block(&mut self, bb: BasicBlock) {
        if !self.processed_bbs.contains(&bb) {
            self.bb_queue.push(bb);
            self.processed_bbs.insert(bb);
        }
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

        let root_location = Location {block: BasicBlock::from_u32(0), statement_index: 0};
        let root_point = self.info.interner.get_point_index(&facts::Point {location: root_location, typ: facts::PointType::Start});

        let mut initial_arg_mapping = Vec::new();
        for (r1, r2, _) in subset_base.iter() {
            let r1_kind = self.info.get_region_kind(*r1);
            if let info::RegionKind::Universal(info::UniversalRegionKind::Local) = r1_kind {
                // this is a constraint we care about here, add it
                if !self.inclusion_tracker.check_inclusion(*r1, *r2, root_point) {
                    self.inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
                    self.inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);
                    let lft1 = info::AtomicRegion::Universal(info::UniversalRegionKind::Local, *r1);
                    let lft2 = info::AtomicRegion::PlaceRegion(*r2);
                    initial_arg_mapping.push((lft1, lft2));
                }
            }
        }
        initial_arg_mapping
    }

    // TODO refactor/ move
    fn to_universal_lft(&self, k: info::UniversalRegionKind, r: Region) -> caesium::UniversalLft {
        match k {
            info::UniversalRegionKind::Function => caesium::UniversalLft::Function,
            info::UniversalRegionKind::Static => caesium::UniversalLft::Static,
            info::UniversalRegionKind::Local => {
                caesium::UniversalLft::Local(self.ty_translator.lookup_universal_lifetime(r).unwrap())
            },
            info::UniversalRegionKind::External => {
                caesium::UniversalLft::External(self.ty_translator.lookup_universal_lifetime(r).unwrap())
            }
        }
    }

    /// Format an atomic region, using the naming info for universal lifetimes available in the current context.
    fn format_atomic_region(&self, r: &info::AtomicRegion) -> String {
        match r {
            info::AtomicRegion::Loan(_, r) => {
                format!("llft{}", r.index())
            },
            info::AtomicRegion::Universal(_, r) => {
                match self.ty_translator.lookup_universal_lifetime(*r) {
                    Some(s) => s,
                    None => format!("ulft{}", r.index()),
                }
            },
            info::AtomicRegion::PlaceRegion(r) => {
                format!("plft{}", r.index())
            },
            info::AtomicRegion::Unknown(r) => {
                format!("lft{}", r.index())
            },
        }
    }

    /// Filter the "interesting" constraints between universal lifetimes that need to hold
    /// (this does not include the constraints that need to hold for all universal lifetimes,
    /// e.g. that they outlive the function lifetime and are outlived by 'static).
    fn get_relevant_universal_constraints(&mut self) -> Vec<(caesium::UniversalLft, caesium::UniversalLft)> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let placeholder_subset = &input_facts.known_placeholder_subset;

        let root_location = Location {block: BasicBlock::from_u32(0), statement_index: 0};
        let root_point = self.info.interner.get_point_index(&facts::Point {location: root_location, typ: facts::PointType::Start});

        let mut universal_constraints = Vec::new();

        for (r1, r2) in placeholder_subset.iter() {
            if let info::RegionKind::Universal(uk1) = info.get_region_kind(*r1) {
                if let info::RegionKind::Universal(uk2) = info.get_region_kind(*r2) {
                    // if LHS is static, ignore.
                    if uk1 == info::UniversalRegionKind::Static {
                        continue
                    }
                    // if RHS is the function lifetime, ignore
                    if uk2 == info::UniversalRegionKind::Function {
                        continue
                    }
                    // else, add this constraint
                    // for the purpose of this analysis, it is fine to treat it as a dynamic inclusion
                    self.inclusion_tracker.add_dynamic_inclusion(*r1, *r2, root_point);
                    universal_constraints.push((self.to_universal_lft(uk1, *r2), self.to_universal_lft(uk2, *r1)));
                }
            }
        }
        universal_constraints
    }

    /// Main translation function that actually does the translation and returns a caesium::Function
    /// if successful.
    pub fn translate(mut self) -> Result<caesium::Function<'def>, TranslationError> {
        let loop_info = self.proc.loop_info();
        info!("loop heads: {:?}", loop_info.loop_heads);
        for (head, bodies) in loop_info.loop_bodies.iter() {
            info!("loop {:?} -> {:?}", head, bodies);
        }


        // add lifetime parameters to the map
        let initial_constraints = self.get_initial_universal_arg_constraints();
        info!("initial constraints: {:?}", initial_constraints);

        // add universal constraints
        let universal_constraints = self.get_relevant_universal_constraints();
        info!("univeral constraints: {:?}", universal_constraints);
        for (lft1, lft2) in universal_constraints.into_iter() {
            self.translated_fn.add_universal_lifetime_constraint(lft1, lft2).map_err(|e| TranslationError::UnknownError(e))?;
        }

        // translate the function's basic blocks
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // first translate the initial basic block; we add some additional annotations to the front
        let initial_bb_idx = BasicBlock::from_u32(0);
        if let Some(bb) = basic_blocks.get(initial_bb_idx) {
            let mut translated_bb = self.translate_basic_block(initial_bb_idx, bb)?;
            // push annotation for initial constraints that relate argument's place regions to universals
            for (r1, r2) in initial_constraints.iter() {
                translated_bb = caesium::Stmt::Annot{
                    a: caesium::Annotation::CopyLftName(self.format_atomic_region(r1), self.format_atomic_region(r2)),
                    s: Box::new(translated_bb)
                };
            }
            let bb_name = Self::make_bb_name(&initial_bb_idx);
            self.translated_fn.code.add_basic_block(bb_name, translated_bb);
        }
        else {
            info!("No basic blocks");
        }

        while let Some(bb_idx) = self.bb_queue.pop() {
            let ref bb = basic_blocks[bb_idx];
            let translated_bb = self.translate_basic_block(bb_idx, bb)?;
            let bb_name = Self::make_bb_name(&bb_idx);
            self.translated_fn.code.add_basic_block(bb_name, translated_bb);
        }

        // assume that all generics are layoutable
        {
            let scope = self.ty_translator.generic_scope.borrow();
            for g in scope.iter() {
                if let Some(ty) = g {
                    let synty = ty.get_syn_type();
                    self.translated_fn.assume_synty_layoutable(synty);
                }
            }
        }
        // assume that all used structs are layoutable
        for (_, g) in self.ty_translator.struct_uses.borrow().iter() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }
        // assume that all used enums are layoutable
        for (_, g) in self.ty_translator.enum_uses.borrow().iter() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }
        // assume that all used tuples are layoutable
        for g in self.ty_translator.tuple_uses.borrow().iter() {
            self.translated_fn.assume_synty_layoutable(g.generate_syn_type_term());
        }

        // TODO: process self.loop_specs
        // - collect the relevant bb -> def_id mappings for this function (so we can eventually generate the definition)
        // - have a function that takes the def_id and then parses the attributes into a loop invariant
        for (head, did) in self.loop_specs.iter() {
            let spec = self.parse_attributes_on_loop_spec_closure(head, did);
            self.translated_fn.register_loop_invariant(Self::make_bb_name(head), spec);
        }

        // process attributes
        self.process_attrs()?;


        // generate dependencies on other procedures.
        for (_, (loc_name, spec_name, params, sts)) in self.collected_procedures.iter() {
            self.translated_fn.require_function(loc_name.clone(), spec_name.clone(), params.clone(), sts.clone());
        }

        self.ty_translator.leave_procedure();
        Ok(self.translated_fn.into())
    }

    /// Parse the attributes on spec closure `did` as loop annotations and add it as an invariant
    /// to the generated code.
    fn parse_attributes_on_loop_spec_closure(&self, loop_head: &BasicBlock, did: &Option<DefId>) -> caesium::LoopSpec {

        // for now: just make invariants True.

        // need to do:
        // - find out the locals in the right order, make parameter names for them.
        //   based on their type and initialization status, get the refinement type.
        // - output/pretty-print this map when generating the typing proof of each function. [done]
        //  + should not be a separate definition, but rather a "set (.. := ...)" with a marker
        //    type so automation can find it.

        // representation of loop invariants:
        // - introduce parameters for them.

        let mut rfn_binders = Vec::new();
        let prop_body = caesium::IProp::True;

        // determine invariant on initialization:
        // - we need this both for the refinement invariant (though this could be removed if we make uninit generic over the refinement)
        // - in order to establish the initialization invariant in each loop iteration, since we don't have proper subtyping for uninit
        //   => maybe we could fix this too by making uninit variant in the refinement type? then we could have proper subtyping lemmas.
        //  + to bring it to the right refinement type initially, maybe have some automation /
        //  annotation
        // TODO: consider changing it like that.
        //
        // Note that StorageDead will not help us for determining initialization/ making it invariant, since it only applies to full stack slots, not individual paths.
        // one thing that makes it more complicated in the frontend: initialization may in practice also be path-dependent.
        //  - this does not cause issues with posing a too strong loop invariant,
        //  - but this poses an issue for annotations
        //
        //

        // get locals
        for (_l, name, ty) in self.fn_locals.iter() {
            // get the refinement type
            let rfnty_scope = self.ty_translator.rfnty_scope.borrow();
            let mut rfn_ty = ty.get_rfn_type(&rfnty_scope);
            // wrap it in place_rfn, since we reason about places
            rfn_ty = caesium::CoqType::PlaceRfn(Box::new(rfn_ty));


            // determine their initialization status
            //let initialized = true; // TODO
            // determine the actual refinement type for the current initialization status.

            let rfn_name = caesium::CoqName::Named(format!("r_{}", name));
            rfn_binders.push(caesium::CoqBinder::new(rfn_name, rfn_ty));
        }

        // TODO what do we do about stuff connecting borrows?
        if let Some(did) = did {
            let attrs = self.env.get_attributes(*did);
            info!("attrs for loop {:?}: {:?}", loop_head, attrs);
        }
        else {
            info!("no attrs for loop {:?}", loop_head);
        }

        let pred = caesium::IPropPredicate::new(rfn_binders, prop_body);
        caesium::LoopSpec { func_predicate: pred }
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

    /// Get the region variables of a type (we assume that region variables have not been erased
    /// yet after the borrow checker ran) and append them to `ret`.
    fn get_ty_region_variables(&self, ty: Ty<'tcx>, ret: &mut Vec<Region>) {
        match ty.kind() {
            TyKind::Ref(reg, _, _) => {
                if let ty::RegionKind::ReVar(reg2) = reg.kind() {
                    ret.push(reg2);
                }
            },
            TyKind::Tuple(_) => {
                for ty0 in ty.tuple_fields() {
                    self.get_ty_region_variables(ty0, ret);
                }
            },
            // TODO also descend below structs/adts/box, like the borrowcheck does.
            _ => {

            },
        }
    }

    /// Determine relevant constraints that should be enforced in the RR type system on an assignment.
    fn get_relevant_assignment_subset_constraints(&mut self, _lhs_ty: &PlaceTy<'tcx>, _rhs_ty: Ty<'tcx>, strong_update: bool, loc: Location) -> Vec<(Region, Region, PointIndex)> {
        let info = &self.info;
        let input_facts = &info.borrowck_in_facts;
        let subset_base = &input_facts.subset_base;

        let mut constraints = Vec::new();
        // Polonius subset constraint are spawned for the midpoint
        let midpoint = self.info.interner.get_point_index(&facts::Point {location: loc, typ: facts::PointType::Mid});


        if strong_update {
            // for strong update: emit mutual equalities
            // TODO: alternative implementation: structurally compare regions in LHS type and RHS type
            for (s1, s2, point) in subset_base.iter() {
                if *point == midpoint {
                    // take this constraint and the reverse constraint
                    constraints.push((*s1, *s2, *point));
                    constraints.push((*s2, *s1, *point));
                }
            }
        }
        else {
            // for weak updates: should mirror the constraints generated by Polonius
            for (s1, s2, point) in subset_base.iter() {
                if *point == midpoint {
                    // take this constraint
                    // TODO should there be exceptions to this?

                    if !self.inclusion_tracker.check_inclusion(*s1, *s2, *point) {
                        // only add it if it does not hold already, since we will enforce this
                        // constraint dynamically.
                        constraints.push((*s1, *s2, *point));
                    }
                }
            }
        }

        constraints
    }

    /// Generate a dynamic inclusion of r1 in r2 at point p. Prepends annotations for doing so to `cont`.
    fn generate_dyn_inclusion(&mut self, r1: Region, r2: Region, p: PointIndex, cont: caesium::Stmt) -> caesium::Stmt {
        // check if inclusion already holds
        if self.inclusion_tracker.check_inclusion(r1, r2, p) {
            // inclusion already holds, done
            cont
        }
        else {
            // check if the reverse inclusion already holds
            if self.inclusion_tracker.check_inclusion(r2, r1, p) {
                // our invariant is that this must be a static inclusion
                assert!(self.inclusion_tracker.check_static_inclusion(r2, r1, p));

                self.inclusion_tracker.add_dynamic_inclusion(r1, r2, p);

                // we generate an extendlft instruction
                // for this, we need to figure out a path to make this inclusion true, i.e. we need
                // an explanation of why it is syntactically included.
                // TODO: for now, we just assume that r1 ⊑ₗ [r2] (in terms of Coq lifetime inclusion)
                caesium::Stmt::Annot{ a: caesium::Annotation::ExtendLft(self.format_atomic_region(&info::AtomicRegion::PlaceRegion(r1))), s: Box::new(cont)}
            }
            else {
                self.inclusion_tracker.add_dynamic_inclusion(r1, r2, p);
                // we generate a dynamic inclusion instruction
                // we flip this around because the annotations are talking about lifetimes, which are oriented the other way around.
                caesium::Stmt::Annot{ a:
                    caesium::Annotation::DynIncludeLft(self.format_atomic_region(&info::AtomicRegion::PlaceRegion(r2)), self.format_atomic_region(&info::AtomicRegion::PlaceRegion(r1))),
                    s: Box::new(cont) }
            }
        }
    }


    /// Split the type of a function operand of a call expression to a base type and an instantiation for
    /// generics.
    fn call_expr_op_split_inst(&self, op: &Operand<'tcx>) -> Result<(DefId, ty::PolyFnSig<'tcx>, ty::GenericArgsRef<'tcx>), TranslationError> {
        match op {
            Operand::Constant(box Constant {literal, ..}) => {
                match literal {
                    ConstantKind::Ty(c) => {
                        match c.ty().kind() {
                            TyKind::FnDef(def, args) => {
                                let ty: Ty<'tcx> = self.env.tcx().type_of(def).instantiate_identity();
                                assert!(ty.is_fn());
                                let sig = ty.fn_sig(self.env.tcx());
                                //let inputs = sig.inputs().skip_binder();
                                //let output = sig.output().skip_binder();
                                Ok((*def, sig, args))
                            }
                            // TODO handle FnPtr
                            _ => Err(TranslationError::Unimplemented{description: "implement function pointers".to_string()}),
                        }
                    },
                    ConstantKind::Val(_, ty) => {
                        match ty.kind() {
                            TyKind::FnDef(def, args) => {
                                let ty: Ty<'tcx> = self.env.tcx().type_of(def).instantiate_identity();
                                assert!(ty.is_fn());
                                let sig = ty.fn_sig(self.env.tcx());
                                //let inputs = sig.inputs().skip_binder();
                                //let output = sig.output().skip_binder();
                                Ok((*def, sig, args))
                            }
                            // TODO handle FnPtr
                            _ => Err(TranslationError::Unimplemented{description: "implement function pointers".to_string()}),
                        }
                    },
                    ConstantKind::Unevaluated(_, _) => {
                        Err(TranslationError::Unimplemented{description: "implement ConstantKind::Unevaluated".to_string()})
                    }
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
        for body in bodies.iter() {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in data.statements.iter() {
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
    fn translate_goto_like(&mut self, _loc: &Location, target: &BasicBlock) -> Result<caesium::Stmt, TranslationError> {
        self.enqueue_basic_block(*target);
        let res_stmt = caesium::Stmt::GotoBlock(Self::make_bb_name(target));

        let loop_info = self.proc.loop_info();
        if loop_info.is_loop_head(*target) {
            if !self.loop_specs.contains_key(target) {
                let spec_defid = self.find_loop_spec_closure(*target)?;
                self.loop_specs.insert(*target, spec_defid);
            }
        }

        Ok(res_stmt)
    }

    /// Check if a call goes to std::rt::begin_panic
    fn is_call_destination_panic(&mut self, func: &Operand) -> Result<bool, TranslationError> {
        match func {
            Operand::Constant(box c) => {
                match c.literal {
                    ConstantKind::Val(_, ty) => {
                        match ty.kind() {
                            TyKind::FnDef(did, _) => {
                                let panic_id1 = crate::utils::try_resolve_did(self.env.tcx(), &["std", "panicking", "begin_panic"]).unwrap();
                                let panic_id2 = crate::utils::try_resolve_did(self.env.tcx(), &["core", "panicking", "panic"]).unwrap();
                                Ok(panic_id1 == *did || panic_id2 == *did)
                            },
                            _ => Ok(false),
                        }

                    },
                    _ => Ok(false)
                }
            },
            _ => Ok(false)
        }
    }

    /// Registers a drop shim for a particular type for the translation.
    fn register_drop_shim_for(&self, _ty: Ty<'tcx>) {
        // TODO!
        //let drop_in_place_did: DefId = crate::utils::try_resolve_did(self.env.tcx(), &["std", "ptr", "drop_in_place"]).unwrap();

        //let x: ty::InstanceDef = ty::InstanceDef::DropGlue(drop_in_place_did, Some(ty));
        //let body: &'tcx mir::Body = self.env.tcx().mir_shims(x);

        //info!("Generated drop shim for {:?}", ty);
        //Self::dump_body(body);
    }


    /// Translate a terminator.
    /// We pass the dying loans during this terminator. They need to be added at the right
    /// intermediate point.
    fn translate_terminator(&mut self, term : &Terminator<'tcx>, loc: Location, dying_loans: Vec<facts::Loan>) -> Result<caesium::Stmt, TranslationError> {
        // get optional hir-id
        //println!("Terminator info: {:?} for {:?}", term.source_info, term.kind);
        //let maybe_hir_id = term.source_info.scope.lint_root(&self.proc.get_mir().source_scopes);
        //println!("Terminator has hir-id: {:?}", maybe_hir_id);
        //let attrs = maybe_hir_id.map(|hid| self.env.tcx().hir().attrs(hid));
        //println!("Terminator has attributers: {:?}", attrs);
        //self.env.tcx().hir().krate_attrs();

        let startpoint = self.info.interner.get_point_index(&facts::Point {location: loc, typ: facts::PointType::Start});
        let midpoint = self.info.interner.get_point_index(&facts::Point {location: loc, typ: facts::PointType::Mid});

        let mut res_stmt;
        match term.kind {
            TerminatorKind::UnwindResume => {
                return Err(TranslationError::Unimplemented { description: "implement UnwindResume".to_string() })
            },
            TerminatorKind::UnwindTerminate => {
                return Err(TranslationError::Unimplemented { description: "implement UnwindTerminate".to_string() })
            },
            TerminatorKind::Goto {ref target} => {
                res_stmt = self.translate_goto_like(&loc, target)?;
            },
            TerminatorKind::Call {ref func, ref args, ref destination, ref target, .. } => {
                let is_panic = self.is_call_destination_panic(func)?;
                if is_panic {
                    info!("Replacing call to std::panicking::begin_panic with Stuck");
                    return Ok(caesium::Stmt::Stuck);
                }


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

                // first identify substitutions for the early-bound regions
                let (target_did, sig, substs) = self.call_expr_op_split_inst(func)?;
                info!("calling function {:?}", target_did);
                let mut early_regions = Vec::new();
                info!("call substs: {:?} = {:?}, {:?}", func, sig, substs);
                for a in substs.iter() {
                    match a.unpack() {
                        ty::GenericArgKind::Lifetime(r) => {
                            match r.kind() {
                                ty::RegionKind::ReVar(r) => early_regions.push(r),
                                _ => (),
                            }
                        }
                        _ => (),
                    }
                }
                info!("call region instantiations (early): {:?}", early_regions);

                // this is a hack to identify the inference variables introduced for the
                // call's late-bound universals.
                // TODO: Can we get this information in a less hacky way?

                // go over all region constraints initiated at this location
                let new_constraints = self.info.get_new_subset_constraints_at_point(midpoint);
                let mut new_regions = HashSet::new();
                let mut relevant_constraints = Vec::new();
                for (r1, r2) in new_constraints.iter() {
                    if let info::RegionKind::Unknown = self.info.get_region_kind(*r1) {
                        // this is probably a inference variable for the call
                        new_regions.insert(*r1);
                        relevant_constraints.push((*r1, *r2));
                    }
                    if let info::RegionKind::Unknown = self.info.get_region_kind(*r2) {
                        new_regions.insert(*r2);
                        relevant_constraints.push((*r1, *r2));
                    }
                }
                // first sort this to enable cycle resolution
                let mut new_regions_sorted: Vec<Region> = new_regions.iter().cloned().collect();
                new_regions_sorted.sort();

                // identify the late-bound regions
                let mut late_regions = Vec::new();
                for r in new_regions_sorted.iter() {
                    if !early_regions.contains(r) {
                        late_regions.push(*r);
                    }
                }
                info!("call region instantiations (late): {:?}", late_regions);

                // recover a mapping for the late bound regions
                // this traverses the type in exactly the same way as the borrow checker
                // (in rustc_borrowck/src/type_check/mod.rs, Call case),
                // to make sure this lines up.
                let mut next_index = 0;
                let mut folder =
                    |_| {
                        // this closure will be called when the folder needs a fresh variable.
                        // we just hand out the late bound regions in sequence
                        let v = late_regions.get(next_index).unwrap();
                        next_index += 1;
                        ty::Region::new_var(self.env.tcx(), *v)
                    };
                let (late_sig, late_region_map) = self.env.tcx().replace_late_bound_regions(sig, &mut folder);
                info!("recovered late map: {:?}, sig: {}", late_region_map, late_sig);

                // fully substitute the types (late parameters are already substituted, now subst early parameters)
                let subst_inputs: Vec<Ty<'tcx>> = late_sig.inputs().iter().map(|ty| {
                    let wrapped_ty = ty::EarlyBinder::bind(*ty);
                    wrapped_ty.instantiate(self.env.tcx(), substs) }).collect();
                let output = ty::EarlyBinder::bind(late_sig.output());
                let _subst_output = output.instantiate(self.env.tcx(), substs);


                // solve the constraints for the new_regions
                // we first identify what kinds of constraints these new regions are subject to
                #[derive(Debug)]
                enum CallRegionKind {
                    // this is just an intersection of local regions.
                    Intersection(HashSet<Region>),
                    // this is equal to a specific region
                    EqR(Region)
                }
                // Notes:
                // - if two of the call regions need to be equal due to constraints on the function,
                //   we define the one with the larger id in terms of the other one
                // - we ignore unidirectional subset constraints between call regions
                //   (these do not help in finding a solution if we take the transitive closure beforehand)
                // - if a call region needs to be equal to a local region, we directly define
                //   it in terms of the local region
                // - otherwise, it will be an intersection of local regions
                let mut new_regions_classification = HashMap::new();
                // compute transitive closure of constraints
                let relevant_constraints = info::compute_transitive_closure(relevant_constraints);
                for r in new_regions_sorted.iter() {
                    for (r1, r2) in relevant_constraints.iter() {
                        if *r2 == *r {
                            // i.e. (flipping it around when we are talking about lifetimes),
                            // r needs to be a sublft of r1
                            if relevant_constraints.contains(&(*r2, *r1)){
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
                            else {
                                // the intersection also needs to contain r1
                                if new_regions.contains(r1) {
                                    // we do not need this constraint, since we already computed the transitive closure.
                                    continue;
                                }
                                let kind = new_regions_classification.entry(*r).or_insert(CallRegionKind::Intersection(HashSet::new()));
                                match kind {
                                    CallRegionKind::Intersection(s) => {
                                        s.insert(*r1);
                                    }
                                    _ => panic!("unreachable"),
                                }
                            }
                        }
                    }
                }
                info!("call arg classification: {:?}", new_regions_classification);

                // update the inclusion tracker with the new regions we have introduced
                // We just add the inclusions and ignore that we resolve it in a "tight" way.
                // the cases where we need the reverse inclusion should be really rare.
                for (r, c) in new_regions_classification.iter() {
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

                // translate the arguments
                let func_expr = self.translate_operand(func, false)?;
                let mut translated_args = Vec::new();
                for (arg, _to_ty) in args.iter().zip(subst_inputs) {
                    // to_ty is the type the function expects

                    //let ty = arg.ty(&self.proc.get_mir().local_decls, self.env.tcx());
                    let translated_arg = self.translate_operand(arg, true)?;
                    translated_args.push(translated_arg);
                }

                // make the call lifetime instantiation list
                let mut lifetime_insts = Vec::new();
                for early in early_regions.iter() {
                    let lft = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(*early));
                    lifetime_insts.push(lft);
                }
                for late in late_regions.iter() {
                    let lft = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(*late));
                    lifetime_insts.push(lft);
                }
                info!("Call lifetime instantiation: {:?}", lifetime_insts);

                //let name = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(r));

                // TODO: add annotations for the assignment
                // for that:
                // - get the type of the place
                // - enforce constraints as necessary. this might spawn dyninclusions with some of the new regions
                //   => In Coq, also the aliases should get proper endlft events to resolve the dyninclusions.
                // - update the name map
                let mut stmt = match target {
                    Some(ref target) => {
                        // assign stmt with call; then jump to bb
                        let place_ty = self.get_type_of_place(destination)?;
                        let place_st = self.ty_translator.translate_type_to_syn_type(&place_ty.ty)?;
                        let place_expr = self.translate_place(destination)?;

                        let mut cont_stmt = self.translate_goto_like(&loc, target)?;

                        // end loans before the goto.
                        // TODO: may cause duplications?
                        cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.into_iter());
                        let ot = self.ty_translator.translate_syn_type_to_op_type(&place_st);

                        caesium::Stmt::Assign{ot,
                                            e1: place_expr,
                                            e2 : caesium::Expr::Call {f : Box::new(func_expr), lfts: lifetime_insts, args: translated_args},
                                            s: Box::new(cont_stmt)}
                    },
                    None => {
                        // expr stmt with call; then stuck (we have not provided a continuation, after all)
                        caesium::Stmt::ExprS{e : caesium::Expr::Call {f : Box::new(func_expr), lfts: lifetime_insts, args: translated_args},
                                           s: Box::new(caesium::Stmt::Stuck)}
                    },
                };

                // add annotations to initialize the regions for the call.
                for (r, class) in new_regions_classification.iter() {
                    let lft = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(*r));
                    match class {
                        CallRegionKind::EqR(r2) => {
                            let lft2 = self.format_atomic_region(&self.info.mk_atomic_region(*r2));
                            stmt = caesium::Stmt::Annot{
                                a: caesium::Annotation::CopyLftName(lft2, lft),
                                s: Box::new(stmt)};
                        },
                        CallRegionKind::Intersection(rs) => {
                            if rs.len() == 0 {
                                panic!("unconstrained lifetime");
                            }
                            else if rs.len() == 1 {
                                // this is really just an equality constraint
                                for r2 in rs.iter() {
                                    let lft2 = self.format_atomic_region(&self.info.mk_atomic_region(*r2));
                                    stmt = caesium::Stmt::Annot{
                                        a: caesium::Annotation::CopyLftName(lft2, lft),
                                        s: Box::new(stmt)};
                                    break;
                                }
                            }
                            else {
                                // a proper intersection
                                let lfts: Vec<_> = rs.iter().map(|r| self.format_atomic_region(&self.info.mk_atomic_region(*r))).collect();
                                stmt = caesium::Stmt::Annot{
                                    a: caesium::Annotation::AliasLftIntersection(lft, lfts),
                                    s: Box::new(stmt)};
                            }
                        },
                    }
                }

                res_stmt = stmt;
            },
            TerminatorKind::Return => {
                // TODO: this requires additional handling for reborrows


                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated return place?
                // See also discussion at https://github.com/rust-lang/rust/issues/71117
                res_stmt = caesium::Stmt::Return(caesium::Expr::Use {
                    ot: self.ty_translator.translate_syn_type_to_op_type(&self.return_synty),
                    e: Box::new(caesium::Expr::Var(self.return_name.to_string()))});

                // TODO is this right?
                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
            },
            //TerminatorKind::Abort => {
                //res_stmt = caesium::Stmt::Stuck;
                //res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
            //},
            TerminatorKind::SwitchInt{ref discr, ref targets} => {
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
                    res_stmt = caesium::Stmt::If{e: operand, ot: caesium::OpType::BoolOp,
                        s1: Box::new(true_branch), s2: Box::new(false_branch)};

                    // TODO: is this right?
                    res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());
                }
                else {
                    //info!("switchint: {:?}", term.kind);
                    let operand = self.translate_operand(discr, true)?;
                    let ty = self.get_type_of_operand(discr)?;

                    let mut target_map: HashMap<u128, usize> = HashMap::new();
                    let mut translated_targets: Vec<caesium::Stmt> = Vec::new();
                    for (idx, (tgt, bb)) in targets.iter().enumerate() {
                        let bb: BasicBlock = bb;
                        let translated_target = self.translate_goto_like(&loc, &bb)?;

                        target_map.insert(tgt, idx);
                        translated_targets.push(translated_target);
                    }
                    let translated_default = self.translate_goto_like(&loc, &targets.otherwise())?;
                    // TODO: need to put endlfts infront of gotos?

                    let translated_ty = self.ty_translator.translate_type(&ty)?;
                    if let caesium::Type::Int(it) = translated_ty {
                        res_stmt = caesium::Stmt::Switch { e: operand, it, index_map: target_map, bs: translated_targets, def: Box::new(translated_default) };
                    }
                    else {
                        return Err(TranslationError::UnknownError("SwitchInt switching on non-integer type".to_string()))
                    }
                }
            },
            TerminatorKind::Assert{ref cond, expected, ref target, ..} => {
                // this translation gets stuck on failure
                let cond_translated = self.translate_operand(cond, true)?;
                let comp = caesium::Expr::BinOp { o: caesium::Binop::EqOp,
                    ot1: caesium::OpType::BoolOp,
                    ot2: caesium::OpType::BoolOp,
                    e1: Box::new(cond_translated),
                    e2: Box::new(caesium::Expr::Literal(caesium::Literal::LitBool(expected)))};

                res_stmt = self.translate_goto_like(&loc, target)?;

                // TODO: should we really have this?
                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());

                res_stmt = caesium::Stmt::AssertS {e: comp, s: Box::new(res_stmt)};
            },
            TerminatorKind::Drop{ref place, ref target, ..} => {
                let ty = self.get_type_of_place(place)?;
                self.register_drop_shim_for(ty.ty);

                let place_translated = self.translate_place(place)?;
                let _drope = caesium::Expr::DropE(Box::new(place_translated));

                res_stmt = self.translate_goto_like(&loc, target)?;

                res_stmt = self.prepend_endlfts(res_stmt, dying_loans.into_iter());

                //res_stmt = caesium::Stmt::ExprS { e: drope, s: Box::new(res_stmt)};
            },
            TerminatorKind::FalseEdge { real_target, .. } => {
                // just a goto for our purposes
                res_stmt = self.translate_goto_like(&loc, &real_target)?;
            },
            TerminatorKind::FalseUnwind { ref real_target, .. } => {
                // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
                res_stmt = self.translate_goto_like(&loc, real_target)?;
            },
            TerminatorKind::GeneratorDrop => {
                return Err(TranslationError::UnsupportedFeature{description: format!("Unsupported terminator {:?}", term)})
            },
            TerminatorKind::Yield { .. } => {
                return Err(TranslationError::UnsupportedFeature{description: format!("Unsupported terminator {:?}", term)})
            },
            TerminatorKind::Unreachable => {
                res_stmt = caesium::Stmt::Stuck;
            },
            TerminatorKind::InlineAsm { .. } => {
                return Err(TranslationError::UnsupportedFeature{description: format!("Unsupported terminator {:?}", term)})
            },
        };

        Ok(res_stmt)
    }

    /// Prepend endlft annotations for dying loans to a statement.
    fn prepend_endlfts<I>(&self, st: caesium::Stmt, dying: I) -> caesium::Stmt
        where I : ExactSizeIterator<Item = facts::Loan>
    {
        let mut cont_stmt = st;
        if dying.len() > 0 {
            //info!("Dying at {:?}: {:?}", loc, dying);
            for d in dying {
                let lft = self.info.atomic_region_of_loan(d);
                cont_stmt = caesium::Stmt::Annot {
                a: caesium::Annotation::EndLft(self.format_atomic_region(&lft)),
                s: Box::new(cont_stmt),
                };
            }
        }
        cont_stmt
    }

    /// Get predecessors in the CFG.
    fn get_loc_predecessors(&self, loc: Location) -> Vec<Location> {
        if loc.statement_index > 0 {
            let pred = Location { block: loc.block, statement_index: loc.statement_index - 1};
            vec![pred]
        }
        else {
            // check for gotos that go to this basic block
            let pred_bbs = self.proc.predecessors(loc.block);
            let basic_blocks = &self.proc.get_mir().basic_blocks;
            pred_bbs.iter().map(|bb| {
                let data = &basic_blocks[*bb];
                Location {block: *bb, statement_index: data.statements.len()}
            }).collect()
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
    fn generate_strong_update_annot(&self, ty: PlaceTy<'tcx>, mut expr: caesium::Expr) -> caesium::Expr {
        let (interesting, tree) = self.generate_strong_update_annot_rec(ty.ty);
        if interesting {
            expr = caesium::Expr::Annot{a: caesium::Annotation::GetLftNames(tree), e: Box::new(expr)};
        }

        expr
    }

    /// Returns a tree for giving names to Coq lifetimes based on RR types.
    /// The boolean indicates whether the tree is "interesting", i.e. whether it names at least one
    /// lifetime.
    fn generate_strong_update_annot_rec(&self, ty: Ty<'tcx>) -> (bool, caesium::LftNameTree) {
        // TODO for now this just handles nested references
        match ty.kind() {
            ty::TyKind::Ref(r, ty, _) => {
                match r.kind() {
                    ty::RegionKind::ReVar(r) => {
                        let name = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(r));
                        let (_, ty_tree) = self.generate_strong_update_annot_rec(*ty);
                        (true, caesium::LftNameTree::Ref(name, Box::new(ty_tree)))
                    },
                    _ => {
                        panic!("generate_strong_update_annot: expected region variable");
                    },
                }
            },
            _  => {
                (false, caesium::LftNameTree::Leaf)
            },
        }
    }

    /// Generate an annotation to adapt the type of `expr` to `target_ty` from type `current_ty` by
    /// means of shortening lifetimes.
    fn generate_shortenlft_annot(&self, target_ty: Ty<'tcx>, _current_ty: Ty<'tcx>, mut expr: caesium::Expr) -> caesium::Expr {
        // this is not so different from the strong update annotation
        let (interesting, tree) = self.generate_strong_update_annot_rec(target_ty);
        if interesting {
            expr = caesium::Expr::Annot{a: caesium::Annotation::ShortenLft(tree), e: Box::new(expr)};
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
        for (r1, r2, p) in subset_base.iter() {
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
            Ok(self.spec_fns.contains(did).then(|| *did))
        }
        else {
            Ok(None)
        }
    }

    fn region_to_region_vid(&self, r: ty::Region<'tcx>) -> facts::Region {
        match r.kind() {
            ty::RegionKind::ReVar(vid) => vid,
            _ => panic!(),
        }
    }

    /**
     * Translate a single basic block.
     */
    fn translate_basic_block(&mut self, bb_idx: BasicBlock, bb: &BasicBlockData<'tcx>) -> Result<caesium::Stmt, TranslationError> {
        // we translate from back to front, starting with the terminator, since Caesium statements
        // have a continuation (the next statement to execute)

        // first do the endlfts for the things right before the terminator
        let mut idx = bb.statements.len();
        let loc = Location { block: bb_idx, statement_index: idx};
        let dying = self.info.get_dying_loans(loc);
        // TODO zombie?
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        let mut cont_stmt: caesium::Stmt = self.translate_terminator(bb.terminator(), loc, dying)?;

        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying);
        //cont_stmt = self.prepend_endlfts(cont_stmt, loc, dying_zombie);

        for stmt in bb.statements.iter().rev() {
            idx -= 1;
            let loc = Location { block: bb_idx, statement_index: idx};

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
            cont_stmt = self.prepend_endlfts(cont_stmt, dying_loans.into_iter());

            //let dying = self.info.get_dying_loans(loc);
            //let dying_zombie = self.info.get_dying_zombie_loans(loc);
            //cont_stmt = self.prepend_endlfts(cont_stmt, dying_zombie);

            match &stmt.kind {
                StatementKind::Assign(b) => {
                    let (plc, val) = b.as_ref();

                    if let Some(_) = self.is_spec_closure_local(plc.local)? {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    }
                    else {
                        let mut translated_val = self.translate_rvalue(loc, val)?;
                        let translated_place = self.translate_place(plc)?;

                        // if this is a checked op, be sure to remember it
                        if let Some(rewritten_ty) = self.checked_op_temporaries.get(&plc.local) {
                            // this should be a temporary
                            assert!(plc.projection.is_empty());

                            let ty = rewritten_ty;

                            let synty = self.ty_translator.translate_type_to_syn_type(&ty)?;
                            let ot = self.ty_translator.translate_syn_type_to_op_type(&synty);
                            cont_stmt = caesium::Stmt::Assign{
                                ot,
                                e1: translated_place,
                                e2: translated_val,
                                s: Box::new(cont_stmt)
                            };
                        }
                        else {
                            let rhs_ty = val.ty(&self.proc.get_mir().local_decls, self.env.tcx());

                            // check if the place is strongly writeable
                            let strongly_writeable = !self.check_place_below_reference(plc)?;
                            let plc_ty = self.get_type_of_place(plc)?;

                            let new_dyn_inclusions;
                            if strongly_writeable {
                                // we are going to update the region mapping through annotations,
                                // and hence put up a barrier for propagation of region constraints

                                // structurally go over the type and find region variables.
                                // for each of the variables, issue a barrier.
                                // also track them together with the PlaceItems needed to reach them.
                                // from the latter, we can generate the necessary annotations
                                let regions = self.find_region_variables_of_place_type(plc_ty);

                                // put up a barrier at the Mid point
                                let barrier_point_index = self.info.interner.get_point_index(&facts::Point {location: loc, typ: facts::PointType::Mid});
                                for r in regions.iter() {
                                    self.inclusion_tracker.add_barrier(*r, barrier_point_index);
                                }
                                // get new constraints that should be enforced
                                let new_constraints = self.get_relevant_assignment_subset_constraints(&plc_ty, rhs_ty, true, loc);
                                for (r1, r2, p) in new_constraints.iter() {
                                    self.inclusion_tracker.add_static_inclusion(*r1, *r2, *p);
                                }

                                // similarly generate an annotation that encodes these constraints in the RR type system
                                translated_val = self.generate_strong_update_annot(plc_ty, translated_val);
                                new_dyn_inclusions = Vec::new();
                            }
                            else {
                                // need to filter out the constraints that are relevant here.
                                // incrementally go through them.
                                new_dyn_inclusions = self.get_relevant_assignment_subset_constraints(&plc_ty, rhs_ty, false, loc);
                            }

                            let synty = self.ty_translator.translate_type_to_syn_type(&plc_ty.ty)?;
                            let ot = self.ty_translator.translate_syn_type_to_op_type(&synty);
                            cont_stmt = caesium::Stmt::Assign{
                                ot,
                                e1: translated_place,
                                e2: translated_val,
                                s: Box::new(cont_stmt)
                            };

                            let loan_point = self.info.get_point(loc, facts::PointType::Mid);

                            // if we create a new loan here, start a new lifetime for it
                            if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
                                // TODO: is this fine for aggregates? I suppose, if I create a loan for an
                                // aggregate, I want to use the same atomic region for all of its components anyways.

                                let lft = self.info.atomic_region_of_loan(loan);
                                let r = lft.get_region();
                                let a = self.info.get_region_kind(r);

                                // get the static inclusions we need to generate here and add them to the inclusion tracker
                                let outliving = self.get_outliving_regions_on_loan(r, loan_point);

                                // add statement for issuing the loan
                                cont_stmt = caesium::Stmt::Annot{
                                    a: caesium::Annotation::StartLft(self.format_atomic_region(&lft), outliving.iter().map(|r| { self.format_atomic_region(&info::AtomicRegion::PlaceRegion(*r)) }).collect()),
                                    s: Box::new(cont_stmt)};

                                info!("Issuing loan at {:?} with kind {:?}: {:?}; outliving: {:?}", loc, a, loan, outliving);
                            }
                            else if let Rvalue::Ref(region, BorrowKind::Shared, _) = val {
                                // for shared reborrows, Polonius does not create a new loan, and so the previous
                                // case did not match.
                                // However, we still need to track the region created for the reborrow in an annotation.

                                let region = self.region_to_region_vid(*region);
                                let lft: info::AtomicRegion = info::AtomicRegion::PlaceRegion(region);

                                // find inclusion ?r1 ⊑ region -- we will actually enforce region = r1
                                let new_constrs: Vec<(facts::Region, facts::Region)> = self.info.get_new_subset_constraints_at_point(loan_point);
                                info!("Shared reborrow at {:?} with new constrs: {:?}", region, new_constrs);
                                let mut included_region = None;
                                for (r1, r2) in new_constrs.iter() {
                                    if *r2 == region {
                                        included_region= Some(r1);
                                        break;
                                    }
                                }
                                if let Some(r) = included_region {
                                    //info!("Found inclusion {:?}⊑  {:?}", r, region);
                                    let lft1 = self.info.mk_atomic_region(*r);
                                    cont_stmt = caesium::Stmt::Annot{
                                        a: caesium::Annotation::CopyLftName(self.format_atomic_region(&lft1), self.format_atomic_region(&lft)),
                                        s: Box::new(cont_stmt)};

                                    // also add this to the inclusion checker
                                    self.inclusion_tracker.add_static_inclusion(*r, region, loan_point);
                                }
                                else {
                                    // This happens e.g. when borrowing from a raw pointer etc.
                                    info!("Found unconstrained shared borrow for {:?}", region);
                                    let inferred_constrained = vec![];

                                    // add statement for issuing the loan
                                    cont_stmt = caesium::Stmt::Annot{
                                        a: caesium::Annotation::StartLft(self.format_atomic_region(&lft), inferred_constrained),
                                        s: Box::new(cont_stmt)};

                                    //panic!("Invariant violation: didn't find place region for shared reborrow");
                                }
                            }

                            // before executing the assignment, first enforce dynamic inclusions
                            for (r1, r2, p) in new_dyn_inclusions.iter() {
                                cont_stmt = self.generate_dyn_inclusion(*r1, *r2, *p, cont_stmt);
                            }
                        }
                    }
                }
                StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                    ()
                }
                StatementKind::SetDiscriminant { place: _place, variant_index: _variant_index } =>
                    // TODO
                    return Err(TranslationError::UnsupportedFeature{description: "TODO: implement SetDiscriminant".to_string()}),
                StatementKind::PlaceMention(_place) =>
                    // TODO: this is missed UB
                    return Err(TranslationError::UnsupportedFeature{description: "TODO: implement PlaceMention".to_string()}),
                StatementKind::Intrinsic(_intrinsic) =>
                    return Err(TranslationError::UnsupportedFeature{description: "TODO: implement Intrinsic".to_string()}),
                StatementKind::ConstEvalCounter =>
                    // no-op
                    (),
                StatementKind::StorageLive(_) =>
                    // just ignore
                    (),
                StatementKind::StorageDead(_) =>
                    // just ignore
                    (),
                StatementKind::Deinit(_) =>
                    // TODO: find out where this is emitted
                    return Err(TranslationError::UnsupportedFeature{description: "Unsupported statement: Deinit".to_string()}),
                StatementKind::Retag(_, _) =>
                    // just ignore retags
                    (),
                StatementKind::AscribeUserType(_, _) =>
                    // don't need that info
                    (),
                StatementKind::Coverage(_) =>
                    // don't need that
                    (),
                StatementKind::Nop =>
                    // ignore
                    (),
            }
        }

        Ok(cont_stmt)
    }

    /// Translate a BorrowKind.
    fn translate_borrow_kind(&self, kind: &BorrowKind) -> Result<caesium::BorKind, TranslationError> {
        match kind {
            BorrowKind::Shared => Ok(caesium::BorKind::Shared),
            BorrowKind::Shallow =>
                // TODO: figure out what to do with this
                // arises in match lowering
                Err(TranslationError::UnsupportedFeature { description: "Do not support Shallow borrows currently".to_string() }),
            BorrowKind::Mut{..} => {
                // TODO: handle two-phase borrows?
                Ok(caesium::BorKind::Mutable)
            }
        }
    }

    fn translate_mutability(&self, mt: &Mutability) -> Result<caesium::Mutability, TranslationError> {
        match mt {
            Mutability::Mut => Ok(caesium::Mutability::Mut),
            Mutability::Not => Ok(caesium::Mutability::Shared),
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
    fn translate_binop(&self, op: BinOp, e1: &Operand<'tcx>, _e2: &Operand<'tcx>) -> Result<caesium::Binop, TranslationError> {
        match op {
            BinOp::AddUnchecked => Ok(caesium::Binop::AddOp),
            BinOp::SubUnchecked => Ok(caesium::Binop::SubOp),
            BinOp::MulUnchecked => Ok(caesium::Binop::MulOp),
            BinOp::ShlUnchecked => Ok(caesium::Binop::ShlOp),
            BinOp::ShrUnchecked => Ok(caesium::Binop::ShrOp),
            BinOp::Add => Ok(caesium::Binop::AddOp),
            BinOp::Sub => Ok(caesium::Binop::SubOp),
            BinOp::Mul => Ok(caesium::Binop::MulOp),
            BinOp::Div => Ok(caesium::Binop::DivOp),
            BinOp::Rem => Ok(caesium::Binop::ModOp),
            BinOp::BitXor => Ok(caesium::Binop::BitXorOp),
            BinOp::BitAnd => Ok(caesium::Binop::BitAndOp),
            BinOp::BitOr => Ok(caesium::Binop::BitOrOp),
            BinOp::Shl => Ok(caesium::Binop::ShlOp),
            BinOp::Shr => Ok(caesium::Binop::ShrOp),
            BinOp::Eq => Ok(caesium::Binop::EqOp),
            BinOp::Lt => Ok(caesium::Binop::LtOp),
            BinOp::Le => Ok(caesium::Binop::LeOp),
            BinOp::Ne => Ok(caesium::Binop::NeOp),
            BinOp::Ge => Ok(caesium::Binop::GeOp),
            BinOp::Gt => Ok(caesium::Binop::GtOp),
            BinOp::Offset => {
                // we need to get the layout of the thing we're offsetting
                // try to get the type of e1.
                let e1_ty = self.get_type_of_operand(e1)?;
                let off_ty = self.get_offset_ty(e1_ty)?;
                let st = self.ty_translator.translate_type_to_syn_type(&off_ty)?;
                let ly = self.ty_translator.translate_syn_type_to_layout(&st);
                Ok(caesium::Binop::PtrOffsetOp(ly))
            }
        }
    }

    /// Translate checked binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_checked_binop(&self, op: BinOp) -> Result<caesium::Binop, TranslationError> {
        match op {
            BinOp::Add => Ok(caesium::Binop::CheckedAddOp),
            BinOp::Sub => Ok(caesium::Binop::CheckedSubOp),
            BinOp::Mul => Ok(caesium::Binop::CheckedMulOp),
            BinOp::Shl => {
                Err(TranslationError::UnsupportedFeature { description: "checked Shl is not currently supported".to_string() })
            },
            BinOp::Shr => {
                Err(TranslationError::UnsupportedFeature { description: "checked Shr is not currently supported".to_string() })
            },
            _ => {
                Err(TranslationError::UnknownError("unexpected checked binop that is not Add, Sub, Mul, Shl, or Shr".to_string()))
            },
        }
    }

    /// Translate unary operators.
    fn translate_unop(&self, op: UnOp, ty: &Ty<'tcx>) -> Result<caesium::Unop, TranslationError> {
        match op {
            UnOp::Not => {
                match ty.kind() {
                    ty::TyKind::Bool => {
                        Ok(caesium::Unop::NotBoolOp)
                    },
                    ty::TyKind::Int(_) => {
                        Ok(caesium::Unop::NotIntOp)
                    },
                    ty::TyKind::Uint(_) => {
                        Ok(caesium::Unop::NotIntOp)
                    },
                    _ => {
                        Err(TranslationError::UnknownError("application of UnOp::Not to non-{Int, Bool}".to_string()))
                    },
                }
            }
            UnOp::Neg => Ok(caesium::Unop::NegOp),
        }
    }

    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(&self, bk: BorrowKind, pl: &Place<'tcx>) -> Result<Option<caesium::RustType>, TranslationError> {
        if let BorrowKind::Mut { .. } = bk {
            let ty = self.get_type_of_place(pl)?;
            // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
            let translated_ty = self.ty_translator.translate_type(&ty.ty)?;
            let env = self.ty_translator.generic_scope.borrow();
            let annot_ty = caesium::RustType::of_type(&translated_ty, env.as_ref());
            Ok(Some(annot_ty))
        }
        else {
            Ok(None)
        }
    }

    /// Translates an Rvalue.
    fn translate_rvalue(&mut self, loc: Location, rval: &Rvalue<'tcx>) -> Result<caesium::Expr, TranslationError> {
        match rval {
            Rvalue::Use(op) => {
                // converts an lvalue to an rvalue
                let translated_op = self.translate_operand(op, true)?;
                Ok(translated_op)
            },
            Rvalue::Ref(region, bk, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_bk = self.translate_borrow_kind(bk)?;
                let ty_annot = self.get_type_annotation_for_borrow(*bk, pl)?;
                if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
                    let atomic_region = self.info.atomic_region_of_loan(loan);
                    let lft = self.format_atomic_region(&atomic_region);
                    Ok(caesium::Expr::Borrow {lft, bk: translated_bk, ty: ty_annot, e: Box::new(translated_pl)})
                }
                else {
                    info!("Didn't find loan at {:?}: {:?}; region {:?}",  loc, rval, region);
                    let region = self.region_to_region_vid(*region);
                    let lft = self.format_atomic_region(&info::AtomicRegion::PlaceRegion(region));

                    Ok(caesium::Expr::Borrow {lft, bk: translated_bk, ty: ty_annot, e: Box::new(translated_pl)})
                    //Err(TranslationError::LoanNotFound(loc))
                }
            },
            Rvalue::AddressOf(mt, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_mt = self.translate_mutability(mt)?;
                Ok(caesium::Expr::AddressOf {mt: translated_mt, e: Box::new(translated_pl)})
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

                Ok(caesium::Expr::BinOp {o: translated_op, ot1: e1_ot, ot2: e2_ot, e1: Box::new(translated_e1), e2: Box::new(translated_e2)})
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

                Ok(caesium::Expr::BinOp {o: translated_op, ot1: e1_ot, ot2: e2_ot, e1: Box::new(translated_e1), e2: Box::new(translated_e2)})
            },
            Rvalue::UnaryOp(op, operand) => {
                let translated_e1 = self.translate_operand(operand, true)?;
                let e1_ty = self.get_type_of_operand(operand)?;
                let e1_st = self.ty_translator.translate_type_to_syn_type(&e1_ty)?;
                let e1_ot = self.ty_translator.translate_syn_type_to_op_type(&e1_st);
                let translated_op = self.translate_unop(*op, &e1_ty)?;
                Ok(caesium::Expr::UnOp { o: translated_op, ot: e1_ot, e: Box::new(translated_e1)})
            },
            Rvalue::NullaryOp(op, _ty) => {
                match op {
                    _ =>
                        Err(TranslationError::UnsupportedFeature{description: "nullary ops (AlignOf, Sizeof) are not supported currently".to_string()})
                }
                // TODO: SizeOf
            },
            Rvalue::Discriminant(pl) => {
                let ty = self.get_type_of_place(pl)?;
                let translated_pl = self.translate_place(pl)?;
                info!("getting discriminant of {:?} at type {:?}", pl, ty);

                let translated_ty = self.ty_translator.translate_type(&ty.ty)?;
                if let caesium::Type::Enum(eu) = translated_ty {
                    let els = eu.generate_enum_layout_spec_term();
                    let discriminant_acc = caesium::Expr::EnumDiscriminant { els,
                        e: Box::new(translated_pl) };
                    // need to do a load from this place
                    let it = ty.ty.discriminant_ty(self.env.tcx());
                    let translated_it = self.ty_translator.translate_type(&it)?;
                    if let caesium::Type::Int(translated_it) = translated_it {
                        let ot = caesium::OpType::IntOp(translated_it);
                        Ok(caesium::Expr::Use { ot, e: Box::new(discriminant_acc) })
                    }
                    else {
                        Err(TranslationError::UnknownError(format!("type of discriminant is not an integer type {:?}", it)))
                    }
                }
                else {
                    Err(TranslationError::UnsupportedFeature{description: format!("We do not support discriminant accesses on non-enum types: {:?}", rval).to_string()})
                }
            },
            Rvalue::Aggregate(kind, op) => {
                // translate operands
                let mut translated_ops: Vec<caesium::Expr> = Vec::new();
                let mut operand_types: Vec<Ty<'tcx>> = Vec::new();
                for o in op.iter() {
                    let translated_o = self.translate_operand(o, true)?;
                    let type_of_o = self.get_type_of_operand(o)?;
                    translated_ops.push(translated_o);
                    operand_types.push(type_of_o);
                }

                match *kind {
                    box mir::AggregateKind::Tuple => {
                        let struct_use = self.ty_translator.generate_tuple_use(operand_types.iter().map(|r| *r))?;
                        let sl = struct_use.generate_struct_layout_spec_term();
                        let initializers: Vec<_> = translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();
                        Ok(caesium::Expr::StructInitE {
                            sls: caesium::CoqAppTerm::new_lhs(sl),
                            components: initializers})
                    },
                    box mir::AggregateKind::Adt(did, variant, args, ..) => {
                        // get the adt def
                        let adt_def: ty::AdtDef<'tcx> = self.env.tcx().adt_def(did);

                        if adt_def.is_struct() {
                            let variant = adt_def.variant(variant);
                            let struct_use = self.ty_translator.generate_struct_use(variant.def_id, args)?;
                            if struct_use.is_unit() {
                                Ok(caesium::Expr::Literal(caesium::Literal::LitZST))
                            }
                            else {
                                let sl = struct_use.generate_struct_layout_spec_term();
                                let initializers: Vec<_> = translated_ops.into_iter().zip(variant.fields.iter()).map(|(o, field)| {
                                    (field.name.to_string(), o)
                                }).collect();

                                Ok(caesium::Expr::StructInitE {
                                    sls: caesium::CoqAppTerm::new_lhs(sl),
                                    components: initializers})
                            }
                        }
                        else if adt_def.is_enum() {
                            let variant_def = adt_def.variant(variant);
                            let struct_use = self.ty_translator.generate_enum_variant_use(did, variant, args)?;
                            let sl = struct_use.generate_struct_layout_spec_term();
                            let initializers: Vec<_> = translated_ops.into_iter().zip(variant_def.fields.iter()).map(|(o, field)| {
                                    (field.name.to_string(), o)
                                }).collect();
                            let variant_e = caesium::Expr::StructInitE { sls: caesium::CoqAppTerm::new_lhs(sl), components: initializers};
                            let enum_use = self.ty_translator.generate_enum_use(adt_def, args)?;
                            let els = enum_use.generate_enum_layout_spec_term();

                            let scope = self.ty_translator.generic_scope.borrow();
                            let ty = caesium::RustType::of_type(&caesium::Type::Enum(enum_use), scope.as_ref());
                            let variant_name = variant_def.name.to_string();
                            Ok(caesium::Expr::EnumInitE { els: caesium::CoqAppTerm::new_lhs(els),
                                variant: variant_name,
                                ty,
                                initializer: Box::new(variant_e) })
                        }
                        else {
                            // TODO
                            return Err(TranslationError::UnsupportedFeature{description: format!("TODO: implement Aggregate rvalue for other adts: {:?}", rval).to_string()});
                        }
                    },
                    _ => {
                        // TODO
                        Err(TranslationError::UnsupportedFeature{description: format!("TODO: implement Aggregate rvalue: {:?}", rval).to_string()})
                    }
                }

            },
            Rvalue::Cast(kind, op, ty) => {
                let op_ty = self.get_type_of_operand(op)?;
                let translated_op = self.translate_operand(op, true)?;
                match kind {
                    mir::CastKind::PointerExposeAddress => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                    },
                    mir::CastKind::PointerFromExposedAddress => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                    },
                    mir::CastKind::PointerCoercion(x) => {
                        match x {
                            ty::adjustment::PointerCoercion::MutToConstPointer => {
                                // this is a NOP in our model
                                Ok(translated_op)
                            },
                            ty::adjustment::PointerCoercion::ArrayToPointer => {
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                            },
                            ty::adjustment::PointerCoercion::ClosureFnPointer(_) => {
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                            },
                            ty::adjustment::PointerCoercion::ReifyFnPointer => {
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                            },
                            ty::adjustment::PointerCoercion::UnsafeFnPointer => {
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                            },
                            ty::adjustment::PointerCoercion::Unsize => {
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
                            },
                        }
                    },
                    mir::CastKind::DynStar => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported dyn* cast").to_string()})
                    }
                    mir::CastKind::IntToInt => {
                        // TODO
                        Err(TranslationError::Unimplemented {description: format!("unsupported int-to-int cast").to_string()})
                    },
                    mir::CastKind::IntToFloat => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported int-to-float cast").to_string()})
                    },
                    mir::CastKind::FloatToInt => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported float-to-int cast").to_string()})
                    },
                    mir::CastKind::FloatToFloat => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported float-to-float cast").to_string()})
                    }
                    mir::CastKind::PtrToPtr => {
                        match (op_ty.kind(), ty.kind()) {
                            (TyKind::RawPtr(_), TyKind::RawPtr(_)) => {
                                // Casts between raw pointers are NOPs for us
                                Ok(translated_op)
                            },
                            _ => {
                                // TODO: any other cases we should handle?
                                Err(TranslationError::UnsupportedFeature{description: format!("unsupported ptr-to-ptr cast: {:?}", rval).to_string()})
                            },
                        }
                    },
                    mir::CastKind::FnPtrToPtr => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported fnptr-to-ptr cast: {:?}", rval).to_string()})
                    },
                    mir::CastKind::Transmute => {
                        Err(TranslationError::UnsupportedFeature{description: format!("unsupported transmute cast: {:?}", rval).to_string()})
                    },
                }
            },
            Rvalue::Len(..) => {
                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
            },
            Rvalue::Repeat(..) => {
                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
            },
            Rvalue::ThreadLocalRef(..) => {
                Err(TranslationError::UnsupportedFeature{description: format!("unsupported rvalue: {:?}", rval).to_string()})
            },
            Rvalue::ShallowInitBox(_, _) => {
                Err(TranslationError::UnsupportedFeature { description: format!("unsupported rvalue: {:?}", rval).to_string() })
            },
            Rvalue::CopyForDeref(_) => {
                Err(TranslationError::UnsupportedFeature { description: format!("unsupported rvalue: {:?}", rval).to_string() })
            },
        }
    }

    /// Make a trivial place accessing `local`.
    fn make_local_place(&self, local: &Local) -> Place<'tcx> {
        Place { local: *local, projection: self.env.tcx().mk_place_elems(&[]) }
    }

    /// Translate an operand.
    /// This will either generate an lvalue (in case of Move or Copy) or an rvalue (in most cases
    /// of Constant). How this is used depends on the context. (e.g., Use of an integer constant
    /// does not typecheck, and produces a stuck program).
    fn translate_operand(&mut self, op: &Operand<'tcx>, to_rvalue: bool) -> Result<caesium::Expr, TranslationError> {
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
                            if f.index() == 0{
                                // access to the result of the op
                                let new_place = self.make_local_place(&place.local);
                                translated_place = self.translate_place(&new_place)?;
                                ty = self.get_type_of_place(place)?;
                            }
                            else {
                                // make this a constant false -- our semantics directly checks for overflows and otherwise throws UB.
                                translated_place = caesium::Expr::Literal(caesium::Literal::LitBool(false));
                                //ty = self.get_type_of_place(place)?;
                                return Ok(translated_place);
                            }
                        },
                        _ => {
                            panic!("invariant violation for access to checked op temporary");
                        }
                    }
                }
                else {
                    translated_place = self.translate_place(place)?;
                    ty = self.get_type_of_place(place)?;
                }

                let st = self.ty_translator.translate_type_to_syn_type(&ty.ty)?;
                let ot = self.ty_translator.translate_syn_type_to_op_type(&st);
                if to_rvalue {
                    Ok(caesium::Expr::Use {ot, e: Box::new(translated_place)})
                }
                else {
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

    fn translate_fn_def_use(&mut self, ty: Ty<'tcx>) -> Result<caesium::Expr, TranslationError> {
        match ty.kind() {
            TyKind::FnDef(defid, params) => {
                // track that we are using this function and generate the Coq location name
                let param_name = self.register_use_procedure(defid, params)?;
                Ok(caesium::Expr::MetaParam(param_name))
            },
            _ => Err(TranslationError::UnknownError("not a FnDef type".to_string())),
        }
    }

    /// Translate a scalar at a specific type to a caesium::Expr.
    fn translate_scalar(&mut self, sc: &Scalar, ty: Ty<'tcx>) -> Result<caesium::Expr, TranslationError> {
        match ty.kind() {
            TyKind::Int(it) => {
                match it {
                    ty::IntTy::I8 =>
                        sc.to_i8().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI8(i)))),
                    ty::IntTy::I16 =>
                        sc.to_i16().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI16(i)))),
                    ty::IntTy::I32 =>
                        sc.to_i32().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI32(i)))),
                    ty::IntTy::I64 =>
                        sc.to_i64().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI64(i)))),
                    ty::IntTy::I128 =>
                        sc.to_i128().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI128(i)))),
                    // for caesium, the pointer size is 8 bytes
                    ty::IntTy::Isize =>
                        sc.to_i64().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitI64(i)))),
                }
            },
            TyKind::Uint(it) => {
                match it {
                    ty::UintTy::U8 =>
                        sc.to_u8().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU8(i)))),
                    ty::UintTy::U16 =>
                        sc.to_u16().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU16(i)))),
                    ty::UintTy::U32 =>
                        sc.to_u32().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU32(i)))),
                    ty::UintTy::U64 =>
                        sc.to_u64().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU64(i)))),
                    ty::UintTy::U128 =>
                        sc.to_u128().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU128(i)))),
                    // for caesium, the pointer size is 8 bytes
                    ty::UintTy::Usize =>
                        sc.to_u64().map_or_else(|_| Err(TranslationError::InvalidLayout), |i| Ok(caesium::Expr::Literal(caesium::Literal::LitU64(i)))),
                }
            },
            TyKind::Bool => {
                sc.to_bool().map_or_else(|_| Err(TranslationError::InvalidLayout), |b| Ok(caesium::Expr::Literal(caesium::Literal::LitBool(b))))
            },
            TyKind::FnDef(_, _) => {
                self.translate_fn_def_use(ty)
            },
            TyKind::Tuple(tys) => {
                if tys.is_empty() {
                    Ok(caesium::Expr::Literal(caesium::Literal::LitZST))
                }
                else {
                    Err(TranslationError::UnsupportedFeature{description: format!("Currently do not support compound construction of tuples using literals: {:?}", ty)})
                }
            },
            _ => {
                Err(TranslationError::UnsupportedFeature{description: format!("Unsupported layout for const value: {:?}", ty)})
            },
        }
    }

    /// Translate a Constant to a caesium::Expr.
    fn translate_constant(&mut self, constant: &Constant<'tcx>) -> Result<caesium::Expr, TranslationError> {
        match constant.literal {
            ConstantKind::Ty(v) => {
                let const_ty = v.ty();

                match v.kind() {
                    ConstKind::Value(ref v) => {
                        // this doesn't contain the necessary structure anymore. Need to reconstruct using the type.
                        match v.try_to_scalar() {
                            Some(sc) => {
                                self.translate_scalar(&sc, const_ty)
                            },
                            _ => {
                                Err(TranslationError::UnsupportedFeature { description: format!("const value not supported: {:?}", v) })
                            },
                        }
                    },
                    _ => Err(TranslationError::UnsupportedFeature{description: "Unsupported ConstKind".to_string()})
                }
            },
            ConstantKind::Val(val, ty) => {
                match val {
                    ConstValue::Scalar(sc) => {
                        self.translate_scalar(&sc, ty)
                    },
                    ConstValue::ZeroSized => {
                        // TODO are there more special cases we need to handle somehow?
                        match ty.kind() {
                            TyKind::FnDef(_, _) => {
                                info!("Translating ZST val for function call target: {:?}", ty);
                                self.translate_fn_def_use(ty)
                            },
                            _ => Ok(caesium::Expr::Literal(caesium::Literal::LitZST))
                        }
                    },
                    _ => {
                        // TODO: do we actually care about this case or is this just something that can
                        // appear as part of CTFE/MIRI?
                        Err(TranslationError::UnsupportedFeature{description: format!("Unsupported Constant: ConstValue; {:?}", constant.literal)})
                    }
                }
            },
            ConstantKind::Unevaluated(_, _) => {
                Err(TranslationError::UnsupportedFeature{description: format!("Unsupported Constant: Unevaluated; {:?}", constant.literal)})
            },
        }
    }


    /// Translate a place to a Caesium lvalue.
    fn translate_place(&mut self, pl : &Place<'tcx>) -> Result<caesium::Expr, TranslationError> {
        // Get the type of the underlying local. We will use this to
        // get the necessary layout information for dereferencing
        let cur_ty = self.get_type_of_local(&pl.local)?;
        let mut cur_ty = PlaceTy::from_ty(cur_ty);
        let local_name = self.variable_map.get(&pl.local).ok_or(TranslationError::UnknownVar(format!("{:?}", pl.local)))?;
        let mut acc_expr: caesium::Expr = caesium::Expr::Var(local_name.to_string());

        // iterate in evaluation order
        for ref it in pl.projection.iter() {
            match it {
                ProjectionElem::Deref => {
                    // use the type of the dereferencee
                    let st = self.ty_translator.translate_type_to_syn_type(&cur_ty.ty)?;
                    let ot = self.ty_translator.translate_syn_type_to_op_type(&st);
                    acc_expr = caesium::Expr::Deref{ot, e: Box::new(acc_expr)};
                },
                ProjectionElem::Field(f, _) => {
                    // `t` is the type of the field we are accessing!
                    let struct_use = self.ty_translator.generate_structlike_use(&cur_ty.ty, cur_ty.variant_index)?;
                    let struct_sls = struct_use.generate_struct_layout_spec_term();

                    let name = self.ty_translator.get_field_name_of(f, cur_ty.ty, cur_ty.variant_index.map(|a| a.as_usize()))?;

                    acc_expr = caesium::Expr::FieldOf { e: Box::new(acc_expr), name, sls: struct_sls};
                },
                ProjectionElem::Index(_v) => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature{description: "places: implement index access".to_string()});
                },
                ProjectionElem::ConstantIndex{..} => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature{description: "places: implement const index access".to_string()});
                },
                ProjectionElem::Subslice{..} => {
                    return Err(TranslationError::UnsupportedFeature{description: "places: implement subslicing".to_string()});
                },
                ProjectionElem::Downcast(_, variant_idx) => {
                    info!("Downcast of ty {:?} to {:?}", cur_ty, variant_idx);
                    let translated_ty = self.ty_translator.translate_type(&cur_ty.ty)?;
                    if let caesium::Type::Enum(eu) = translated_ty {
                        let els = eu.generate_enum_layout_spec_term();

                        let variant_name = self.ty_translator.get_variant_name_of(cur_ty.ty, *variant_idx)?;

                        acc_expr = caesium::Expr::EnumData { els, variant: variant_name, e: Box::new(acc_expr) }
                    }
                    else {
                        return Err(TranslationError::UnknownError("places: ADT downcasting on non-enum type".to_string()));
                    }
                },
                ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::UnsupportedFeature{description: "places: implement opaque casts".to_string()});
                },
            };
            // update cur_ty
            cur_ty = cur_ty.projection_ty(self.env.tcx(), *it);
        }
        Ok(acc_expr)
    }

    /// Get the type of a local in a body.
    fn get_type_of_local(&self, local: &Local) -> Result<Ty<'tcx>, TranslationError> {
        self.proc.get_mir().local_decls.get(*local).and_then(|decl| Some(decl.ty)).ok_or(TranslationError::UnknownVar("".to_string()))
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
