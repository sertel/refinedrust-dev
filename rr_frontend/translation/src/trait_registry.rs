use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::string::ToString;

use derive_more::{Constructor, Display};
use log::{info, trace};
use radium::{self, coq, specs};
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::{self, ty};
use typed_arena::Arena;

use crate::base::TranslationError;
use crate::environment::Environment;
use crate::function_body::{get_arg_syntypes_for_procedure_call, mangle_name_with_args, FunctionTranslator};
use crate::spec_parsers::propagate_method_attr_from_impl;
use crate::spec_parsers::trait_attr_parser::{TraitAttrParser, VerboseTraitAttrParser};
use crate::spec_parsers::trait_impl_attr_parser::{TraitImplAttrParser, VerboseTraitImplAttrParser};
use crate::type_translator::{
    generate_args_inst_key, strip_coq_ident, GenericsKey, InFunctionState, LocalTypeTranslator, ParamScope,
    TypeTranslator,
};
use crate::utils;

#[derive(Debug, Clone, Display)]
pub enum Error<'tcx> {
    /// This DefId is not a trait
    #[display("The given DefId {:?} is not a trait", _0)]
    NotATrait(DefId),
    /// This DefId is not an impl of a trait
    #[display("The given DefId {:?} is not a trait implementation", _0)]
    NotATraitImpl(DefId),
    /// This DefId is not a trait method
    #[display("The given DefId {:?} is not a trait method", _0)]
    NotATraitMethod(DefId),
    /// This DefId is not an assoc type
    #[display("The given DefId {:?} is not an associated type", _0)]
    NotAnAssocType(DefId),
    /// This trait already exists
    #[display("This trait {:?} already has been registered", _0)]
    TraitAlreadyExists(DefId),
    /// This trait impl already exists
    #[display("This trait impl {:?} already has been registered", _0)]
    ImplAlreadyExists(DefId),
    /// Trait hasn't been registered yet but is used
    #[display("This trait {:?} has not been registered yet", _0)]
    UnregisteredTrait(DefId),
    /// Trait impl hasn't been registered yet but is used
    #[display("This trait impl {:?} has not been registered yet", _0)]
    UnregisteredImpl(DefId),
    /// Cannot find this trait instance in the local environment
    #[display("An instance for this trait {:?} cannot by found with generic args {:?}", _0, _1)]
    UnknownLocalInstance(DefId, ty::GenericArgsRef<'tcx>),
    #[display("An error occurred when parsing the specification of the trait {:?}: {:?}", _0, _1)]
    TraitSpec(DefId, String),
    #[display("An error occurred when parsing the specification of the trait impl {:?}: {:?}", _0, _1)]
    TraitImplSpec(DefId, String),
    /// Unknown error
    #[display("Unknown Error")]
    Unknown,
}
pub type TraitResult<'tcx, T> = Result<T, Error<'tcx>>;

/// What does a trait registry need?
///
/// for reach Rust trait:
///   - mapping to the Coq representation, i.e. functions with specifications (`FunctionSpec`?) as well as
///     types
///   - list of impls we have translated and which we will emit.
///
/// for each generic in the function scope: (-> `LocalTraitRegistry`)
///   - list of identifiers to the trait instance, and means to add that to the spec later
///     + these are Param instances that we cannot statically resolve
///
///   - a list of trait uses: next to the generic args, what trait implementations do we assume to be
///     available for types? e.g. we might require a trait instance of `Ord` for (T, i32) where T is a generic
///     arg. This instance might not be a parameter, but concretely resolved. i.e. we have a pair of a
///     location, but get the spec for the trait impl as part of the thing.
///   => or do we want to merge these two?
///         e.g., will the second part really be handled differently from the first kind?
///         The difference is:
///         + the second kind depends on the semantic type, the first one should not depend on the semantic
///           type. i.e. the first one will assume a function has a type at the linking level. while the
///           second one assumes the type assignment at the precondition-level.
///         + Note that the first one might still get type parameters for some instances, e.g. if I have an
///           instance for (T, i32). That should be fine and not create any complications.
///       => No, we should not merge these.
///   => Are the trait uses different from just using functions?
///         + They are only different when they directly involve one of the Param traits, otherwise
///         they are statically resolvable.
///
///
///  In the case of closures, we would add the fact that the closure implements the invocation
///  method as an assumption to the `ProcedureScope`.
///  We would generate the spec for that from the annotated spec.
///    In this case, since the instance is auto-generated usually, it can be statically resolved,
///    but will not have a specification or the obligation to generate it yet.
///    So we have to put the obligation on it. Add support to `ProcedureScope` for that.
///    (For now, we'll not resolve that obligation)
///    - generate a new name for that
///    - register a specification for that
///      + the specification is not provided in the form of annotations, but we should generate a
///        `FunctionSpec` nevertheless.
///    -
pub struct TraitRegistry<'tcx, 'def> {
    /// environment
    env: &'def Environment<'tcx>,
    type_translator: &'def TypeTranslator<'def, 'tcx>,

    /// trait declarations
    trait_decls: RefCell<HashMap<LocalDefId, radium::TraitSpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<HashMap<DefId, specs::LiteralTraitSpecRef<'def>>>,

    /// for the trait instances in scope, the names for their Coq definitions
    /// (to enable references to them when translating functions)
    impl_literals: RefCell<HashMap<DefId, specs::LiteralTraitImplRef<'def>>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<specs::LiteralTraitSpec>,
    /// arena for allocating impl literals
    impl_arena: &'def Arena<specs::LiteralTraitImpl>,
    /// arena for function specifications
    fn_spec_arena: &'def Arena<specs::FunctionSpec<specs::InnerFunctionSpec<'def>>>,
}

impl<'tcx, 'def> TraitRegistry<'tcx, 'def> {
    /// Create an empty trait registry.
    pub fn new(
        env: &'def Environment<'tcx>,
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        trait_arena: &'def Arena<specs::LiteralTraitSpec>,
        impl_arena: &'def Arena<specs::LiteralTraitImpl>,
        fn_spec_arena: &'def Arena<specs::FunctionSpec<specs::InnerFunctionSpec<'def>>>,
    ) -> Self {
        Self {
            env,
            type_translator: ty_translator,
            trait_arena,
            impl_arena,
            fn_spec_arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
            impl_literals: RefCell::new(HashMap::new()),
        }
    }

    /// Get registered trait declarations in the local crate.
    pub fn get_trait_decls(&self) -> HashMap<LocalDefId, specs::TraitSpecDecl<'def>> {
        let decls = self.trait_decls.borrow();
        decls.clone()
    }

    /// Get a set of other (different) traits that this trait depends on.
    pub fn get_deps_of_trait(&self, did: DefId) -> HashSet<DefId> {
        let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(did);

        let mut deps = HashSet::new();
        for clause in param_env.caller_bounds() {
            let kind = clause.kind().skip_binder();
            if let ty::ClauseKind::Trait(pred) = kind {
                let other_did = pred.trait_ref.def_id;

                if other_did != did {
                    deps.insert(other_did);
                }
            }
        }

        deps
    }

    /// Order the given traits according to their dependencies.
    pub fn get_trait_deps(&self, traits: &[LocalDefId]) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        for trait_decl in traits {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get a map of dependencies between traits.
    pub fn get_registered_trait_deps(&self) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        let decls = self.trait_decls.borrow();
        for trait_decl in decls.keys() {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Get the names of associated types of this trait.
    pub fn get_associated_type_names(&self, did: DefId) -> Vec<String> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = self.env.get_trait_assoc_types(did);
        for ty_did in &assoc_types {
            let ty_name = self.env.get_assoc_item_name(*ty_did).unwrap();
            assoc_tys.push(ty_name);
        }

        assoc_tys
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(
        &self,
        did: DefId,
        name: String,
        declared_attrs: HashSet<String>,
    ) -> specs::LiteralTraitSpec {
        let phys_record = format!("{name}_phys");
        let spec_record = format!("{name}_spec");
        let spec_params_record = format!("{name}_spec_params");
        let spec_attrs_record = format!("{name}_spec_attrs");
        let base_spec = format!("{name}_base_spec");
        let base_spec_params = format!("{name}_base_spec_params");
        let spec_subsumption = format!("{name}_spec_incl");

        specs::LiteralTraitSpec {
            name,
            assoc_tys: self.get_associated_type_names(did),
            spec_record,
            spec_params_record,
            spec_attrs_record,
            base_spec,
            base_spec_params,
            spec_subsumption,
            declared_attrs,
        }
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub fn register_trait(
        &'def self,
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        did: LocalDefId,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("enter TraitRegistry::register_trait for did={did:?}");

        {
            let scope = self.trait_decls.borrow();
            if scope.get(&did).is_some() {
                return Ok(());
            }
        }

        // TODO: can we handle the case that this depends on a generic having the same trait?
        // In principle, yes, but currently the implementation does not allow it.
        // We also do not generate trait dep parameters.
        // We should depend on the assoc types of the other traits as well as the specs.

        // get generics
        let trait_generics: &'tcx ty::Generics = self.env.tcx().generics_of(did.to_def_id());
        let param_scope = ParamScope::from(trait_generics.params.as_slice());
        // TODO: add associated types

        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));

        // parse trait spec
        let trait_attrs = utils::filter_tool_attrs(self.env.get_attributes(did.into()));
        // As different attributes of the spec may depend on each other, we need to pass a closure
        // determining under which Coq name we are going to introduce them
        // Note: This needs to match up with `radium::LiteralTraitSpec.make_spec_attr_name`!
        let mut attr_parser = VerboseTraitAttrParser::new(&param_scope, |id| format!("{trait_name}_{id}"));
        let trait_spec =
            attr_parser.parse_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

        // get the declared attributes that are allowed on impls
        let valid_attrs: HashSet<String> = trait_spec.attrs.attrs.keys().cloned().collect();

        // make the literal we are going to use
        let lit_trait_spec = self.make_literal_trait_spec(did.to_def_id(), trait_name.clone(), valid_attrs);
        // already register it for use
        // In particular, this is also needed to be able to register the methods of this trait
        // below, as they need to be able to access the associated types of this trait already.
        // (in fact, their environment contains their self instance)
        let lit_trait_spec_ref = self.register_shim(did.to_def_id(), lit_trait_spec)?;

        // get items
        let mut methods = HashMap::new();
        let mut assoc_types = Vec::new();
        let items: &ty::AssocItems = self.env.tcx().associated_items(did);
        for c in items.in_definition_order() {
            if ty::AssocKind::Fn == c.kind {
                // get attributes
                let attrs = self.env.get_attributes_of_function(c.def_id, &propagate_method_attr_from_impl);

                // get function name
                let method_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let method_name = strip_coq_ident(&method_name);

                let name = format!("{trait_name}_{method_name}");
                let spec_name = format!("{name}_base_spec");

                // get spec
                let spec = FunctionTranslator::spec_for_trait_method(
                    self.env,
                    c.def_id,
                    &name,
                    &spec_name,
                    attrs.as_slice(),
                    ty_translator,
                    self,
                )?;
                let spec_ref = self.fn_spec_arena.alloc(spec);

                methods.insert(method_name, &*spec_ref);
            } else if ty::AssocKind::Type == c.kind {
                // get name
                let type_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let type_name = strip_coq_ident(&type_name);
                let lit = radium::LiteralTyParam::new(&type_name, &type_name);
                assoc_types.push(lit);
            }
        }

        let base_instance_spec = radium::TraitInstanceSpec::new(methods);
        let decl = radium::TraitSpecDecl::new(
            lit_trait_spec_ref,
            coq::binder::BinderList::new(trait_spec.context_items),
            param_scope.into(),
            assoc_types,
            base_instance_spec,
            trait_spec.attrs,
        );

        let mut scope = self.trait_decls.borrow_mut();
        scope.insert(did, decl);

        trace!("leave TraitRegistry::register_trait");
        Ok(())
    }

    /// Register a shim with the trait registry.
    ///
    /// Errors:
    /// - NotATrait(did) if did is not a trait
    /// - TraitAlreadyExists(did) if this trait has already been registered
    pub fn register_shim<'a>(
        &'a self,
        did: DefId,
        spec: radium::LiteralTraitSpec,
    ) -> TraitResult<'tcx, radium::LiteralTraitSpecRef<'def>> {
        if !self.env.tcx().is_trait(did) {
            return Err(Error::NotATrait(did));
        }

        let mut trait_literals = self.trait_literals.borrow_mut();
        if trait_literals.get(&did).is_some() {
            return Err(Error::TraitAlreadyExists(did));
        }

        let spec = self.trait_arena.alloc(spec);
        trait_literals.insert(did, &*spec);

        Ok(spec)
    }

    /// Register a shim for a trait impl.
    pub fn register_impl_shim<'a>(
        &'a self,
        did: DefId,
        spec: radium::LiteralTraitImpl,
    ) -> TraitResult<'tcx, radium::LiteralTraitImplRef<'def>> {
        if self.env.tcx().trait_id_of_impl(did).is_none() {
            return Err(Error::NotATraitImpl(did));
        }

        let mut impl_literals = self.impl_literals.borrow_mut();
        if impl_literals.get(&did).is_some() {
            return Err(Error::ImplAlreadyExists(did));
        }

        let spec = self.impl_arena.alloc(spec);
        impl_literals.insert(did, &*spec);

        Ok(spec)
    }

    /// Lookup a trait.
    pub fn lookup_trait(&self, trait_did: DefId) -> Option<radium::LiteralTraitSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        trait_literals.get(&trait_did).copied()
    }

    /// Lookup the spec for an impl.
    /// If None, use the default spec.
    pub fn lookup_impl(&self, impl_did: DefId) -> Option<radium::LiteralTraitImplRef<'def>> {
        let impl_literals = self.impl_literals.borrow();
        impl_literals.get(&impl_did).copied()
    }

    /// Get the term for referring to the attribute record of a particular impl within a function of
    /// that impl.
    pub fn get_impl_attrs_term(&self, impl_did: DefId) -> Result<String, TranslationError<'tcx>> {
        let impl_ref = self.lookup_impl(impl_did).ok_or(Error::UnregisteredImpl(impl_did))?;
        let attr_record = &impl_ref.spec_attrs_record;
        let info = self.get_trait_impl_info(impl_did)?;
        // TODO: maybe it would be better to do the formatting in radium

        let mut attr_term = String::with_capacity(100);
        write!(attr_term, "{attr_record}").unwrap();

        // add the type parameters of the impl
        for ty in info.generics.get_ty_params() {
            write!(attr_term, " {}", ty.refinement_type).unwrap();
        }

        Ok(attr_term)
    }

    /// Get the term for the specification of a trait impl (applied to the given arguments of the trait),
    /// as well as the list of associated types.
    pub fn get_impl_spec_term(
        &self,
        ty_translator: &LocalTypeTranslator<'def, 'tcx>,
        impl_did: DefId,
        impl_args: &[ty::GenericArg<'tcx>],
        trait_args: &[ty::GenericArg<'tcx>],
    ) -> Result<(radium::SpecializedTraitSpec<'def>, Vec<ty::Ty<'tcx>>), TranslationError<'tcx>> {
        trace!(
            "enter TraitRegistry::get_impl_spec_term for impl_did={impl_did:?} impl_args={impl_args:?} trait_args={trait_args:?}"
        );
        let trait_did = self.env.tcx().trait_id_of_impl(impl_did).ok_or(Error::NotATraitImpl(impl_did))?;

        let trait_instance = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        let mut assoc_args = Vec::new();
        // get associated types of this impl
        // Since we know the concrete impl, we can directly resolve all of the associated types
        // TODO is this definition order guaranteed to be the same as on the trait?
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(impl_did);
        for it in assoc_items.in_definition_order() {
            if it.kind == ty::AssocKind::Type {
                let item_did = it.def_id;
                let item_ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.env.tcx().type_of(item_did);
                let subst_ty = item_ty.instantiate(self.env.tcx(), impl_args);

                assoc_args.push(subst_ty);
            }
        }

        // check if there's a more specific impl spec
        let term = if let Some(impl_spec) = self.lookup_impl(impl_did) {
            // pass the args for this specific impl
            let mut all_impl_args = Vec::new();
            for arg in impl_args {
                if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                    let ty = ty_translator.translate_type(ty)?;
                    all_impl_args.push(ty);
                }
            }

            // instantiate the attrs suitably
            let mut args = Vec::new();
            for ty in &all_impl_args {
                args.push(format!("{}", ty.get_rfn_type()));
            }
            let attr_term = format!("{}", coq::term::App::new(impl_spec.spec_attrs_record.clone(), args));

            radium::SpecializedTraitSpec::new_with_params(
                impl_spec.spec_record.clone(),
                Some(all_impl_args),
                attr_term,
                false,
            )
        } else {
            return Err(TranslationError::TraitTranslation(Error::UnregisteredImpl(impl_did)));
        };

        trace!("leave TraitRegistry::get_impl_spec_term");
        Ok((term, assoc_args))
    }

    pub fn get_trait_impl_info(
        &self,
        trait_impl_did: DefId,
    ) -> Result<radium::TraitRefInst<'def>, TranslationError<'tcx>> {
        let trait_did = self
            .env
            .tcx()
            .trait_id_of_impl(trait_impl_did)
            .ok_or(Error::NotATraitImpl(trait_impl_did))?;

        // check if we registered this impl previously
        let trait_spec_ref = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(trait_impl_did);

        // get all associated items
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_impl_did);
        let trait_assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_did);

        // figure out the parameters this impl gets and make a scope
        let impl_generics: &'tcx ty::Generics = self.env.tcx().generics_of(trait_impl_did);
        let param_scope = ParamScope::from(impl_generics.params.as_slice());

        // parse specification
        let trait_impl_attrs = utils::filter_tool_attrs(self.env.get_attributes(trait_impl_did));
        let mut attr_parser = VerboseTraitImplAttrParser::new(&param_scope);
        let impl_spec = attr_parser
            .parse_trait_impl_attrs(&trait_impl_attrs)
            .map_err(|e| Error::TraitImplSpec(trait_impl_did, e))?;

        // figure out the trait ref for this
        let subject = self.env.tcx().impl_subject(trait_impl_did).skip_binder();
        if let ty::ImplSubject::Trait(trait_ref) = subject {
            // get instantiation for parameters
            let mut params_inst = Vec::new();
            let mut lft_inst = Vec::new();
            for arg in trait_ref.args {
                if let Some(ty) = arg.as_type() {
                    let ty = self.type_translator.translate_type_in_scope(param_scope.clone(), ty)?;
                    params_inst.push(ty);
                } else if let Some(lft) = arg.as_region() {
                    let lft = TypeTranslator::translate_region_in_scope(param_scope.clone(), lft)
                        .unwrap_or_else(|| "trait_placeholder_lft".to_owned());
                    lft_inst.push(lft);
                }
            }

            // get instantiation for the associated types
            let mut assoc_types_inst = Vec::new();

            // TODO don't rely on definition order
            // maybe instead iterate over the assoc items of the trait

            for x in trait_assoc_items.in_definition_order() {
                if x.kind == ty::AssocKind::Type {
                    let ty_item = assoc_items.find_by_name_and_kind(
                        self.env.tcx(),
                        x.ident(self.env.tcx()),
                        ty::AssocKind::Type,
                        trait_impl_did,
                    );
                    if let Some(ty_item) = ty_item {
                        let ty_did = ty_item.def_id;
                        let ty = self.env.tcx().type_of(ty_did);
                        let translated_ty = self
                            .type_translator
                            .translate_type_in_scope(param_scope.clone(), ty.skip_binder())?;
                        assoc_types_inst.push(translated_ty);
                    } else {
                        unreachable!("trait impl does not have required item");
                    }
                }
            }

            Ok(radium::TraitRefInst::new(
                trait_spec_ref,
                param_scope.into(),
                lft_inst,
                params_inst,
                assoc_types_inst,
                impl_spec.attrs,
            ))
        } else {
            unreachable!("Expected trait impl");
        }
    }
}

/// Check if this is a built-in trait
pub fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = utils::try_resolve_did(tcx, &["core", "marker", "Sized"])?;

    // TODO: for these, should instead require the primitive encoding of our Coq formalization
    let send_did = utils::try_resolve_did(tcx, &["core", "marker", "Send"])?;
    let sync_did = utils::try_resolve_did(tcx, &["core", "marker", "Sync"])?;
    let copy_did = utils::try_resolve_did(tcx, &["core", "marker", "Copy"])?;

    // used for closures
    let copy_did = utils::try_resolve_did(tcx, &["core", "marker", "Tuple"])?;

    Some(trait_did == sized_did || trait_did == copy_did)
}

/// Get non-trivial trait requirements of a function's `ParamEnv`.
pub fn get_nontrivial_trait_requirements<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> Vec<ty::TraitRef<'tcx>> {
    let mut trait_refs = Vec::new();

    let clauses = param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Trait(trait_pred) = cl_kind {
            // We ignore negative polarities for now
            if trait_pred.polarity == ty::ImplPolarity::Positive {
                let trait_ref = trait_pred.trait_ref;

                // filter Sized, Copy, Send, Sync?
                if Some(true) == is_builtin_trait(tcx, trait_ref.def_id) {
                    continue;
                }

                // this is a nontrivial requirement
                trait_refs.push(trait_ref);
            }
        }
    }
    trait_refs
}

/// Given a particular reference to a trait, get the associated type constraints for this trait reference.
pub fn get_trait_assoc_constraints<'tcx>(
    env: &Environment<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> HashMap<String, ty::Ty<'tcx>> {
    let mut assoc_ty_map = HashMap::new();

    // TODO: check if caller_bounds does the right thing for implied bounds
    let clauses = param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Projection(proj) = cl_kind {
            if trait_ref.def_id == proj.trait_def_id(env.tcx()) && trait_ref.args == proj.projection_ty.args {
                // same trait and same args
                let name = env.get_assoc_item_name(proj.def_id()).unwrap();
                let ty = proj.term.ty().unwrap();
                assoc_ty_map.insert(name, ty);
            }
        }
    }
    assoc_ty_map
}

/// A using occurrence of a trait in the signature of the function.
#[derive(Debug, Clone)]
pub struct GenericTraitUse<'def> {
    /// the DefId of the trait
    pub did: DefId,
    /// the self type this is implemented for
    pub self_ty: ty::ParamTy,
    /// the Coq-level trait use
    pub trait_use: radium::LiteralTraitSpecUse<'def>,
}

impl<'def> GenericTraitUse<'def> {
    /// Create a new trait use.
    #[must_use]
    pub fn new<'tcx>(
        type_translator: &TypeTranslator<'def, 'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: radium::LiteralTraitSpecRef<'def>,
        is_used_in_self_trait: bool,
        assoc_ty_constraints: HashMap<String, radium::Type<'def>>,
    ) -> Self {
        let did = trait_ref.def_id;

        // translate the arguments in the scope of the function
        let mut translated_args = Vec::new();
        for arg in trait_ref.args {
            if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                let translated_ty = type_translator.translate_type(ty, scope).unwrap();
                translated_args.push(translated_ty);
            }
        }

        // the self param should be a Param that is bound in the function's scope
        let param = if let ty::TyKind::Param(param) = trait_ref.args[0].expect_ty().kind() {
            *param
        } else {
            unreachable!("self should be a Param");
        };

        // TODO: allow to override the assumed specification using attributes
        let spec_override = None;

        // create a name for this instance by including the args
        let mangled_base = mangle_name_with_args(&spec_ref.name, trait_ref.args.as_slice());
        let spec_use = radium::LiteralTraitSpecUse::new(
            spec_ref,
            translated_args,
            mangled_base,
            spec_override,
            is_used_in_self_trait,
            assoc_ty_constraints,
        );

        Self {
            did,
            self_ty: param,
            trait_use: spec_use,
        }
    }

    /// Get the names of associated types of this trait.
    pub fn get_associated_type_names(&self, env: &Environment<'_>) -> Vec<String> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in &assoc_types {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            assoc_tys.push(ty_name);
        }
        assoc_tys
    }

    /// Get the associated type instantiations for this trait use.
    pub fn get_associated_type_uses(&self, env: &Environment<'_>) -> Vec<radium::Type<'def>> {
        let mut assoc_tys: Vec<radium::Type> = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in &assoc_types {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            let lit = self.trait_use.make_assoc_type_use(&strip_coq_ident(&ty_name));
            assoc_tys.push(lit);
        }
        assoc_tys
    }
}
