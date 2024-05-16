use std::cell::RefCell;
use std::collections::{HashSet, HashMap};

use log::{info, trace};
use radium::{code, specs};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use typed_arena::Arena;

use crate::base::TranslationError;
use crate::environment::Environment;
use crate::function_body::{get_arg_syntypes_for_procedure_call, mangle_name_with_args, FunctionTranslator};
use crate::spec_parsers::propagate_method_attr_from_impl;
use crate::type_translator::{
    generate_args_inst_key, strip_coq_ident, GenericsKey, InFunctionState, LocalTypeTranslator,
    TypeTranslator,
};
use crate::utils;

use derive_more::Constructor;

#[derive(Debug, Clone)]
pub enum TraitRegistryError<'tcx> {
    /// This DefId is not a trait
    NotATrait(DefId),
    /// This DefId is not an impl of a trait
    NotATraitImpl(DefId),
    /// This DefId is not a trait method
    NotATraitMethod(DefId),
    /// This DefId is not an assoc type
    NotAnAssocType(DefId),
    /// This trait already exists
    TraitAlreadyExists(DefId),
    /// Trait hasn't been registered yet but is used
    UnregisteredTrait(DefId),
    /// Cannot find this trait instance in the local environment
    UnknownLocalInstance(DefId, ty::GenericArgsRef<'tcx>),
    /// Unknown error
    Unknown,
}
pub type TraitRegistryResult<'tcx, T> = Result<T, TraitRegistryError<'tcx>>;


/// What does a trait registry need?
///
/// for reach Rust trait:
///   - mapping to the Coq representation, i.e. functions with specifications (FunctionSpec?) as well as types
///   - list of impls we have translated and which we will emit.
///
/// for each generic in the function scope: (-> LocalTraitRegistry)
///   - list of identifiers to the trait instance, and means to add that to the spec later
///     + these are Param instances that we cannot statically resolve
///
///   - a list of trait uses: next to the generic args, what trait implementations do we assume to be
///     available for types? e.g. we might require a trait instance of Ord for (T, i32) where T is a generic
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
///  method as an assumption to the ProcedureScope.
///  We would generate the spec for that from the annotated spec.
///    In this case, since the instance is auto-generated usually, it can be statically resolved,
///    but will not have a specification or the obligation to generate it yet.
///    So we have to put the obligation on it. Add support to ProcedureScope for that.
///    (For now, we'll not resolve that obligation)
///    - generate a new name for that
///    - register a specification for that
///      + the specification is not provided in the form of annotations, but we should generate a FunctionSpec
///        nevertheless.
///    -
pub struct TraitRegistry<'tcx, 'def> {
    /// environment
    env: &'def Environment<'tcx>,
    type_translator: &'def TypeTranslator<'def, 'tcx>,

    /// trait declarations
    trait_decls: RefCell<HashMap<LocalDefId, specs::TraitSpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<HashMap<DefId, specs::LiteralTraitSpecRef<'def>>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<specs::LiteralTraitSpec>,
}

impl<'tcx, 'def> TraitRegistry<'tcx, 'def> {
    /// Create an empty trait registry.
    pub fn new(
        env: &'def Environment<'tcx>,
        ty_translator: &'def TypeTranslator<'def, 'tcx>,
        arena: &'def Arena<specs::LiteralTraitSpec>,
    ) -> Self {
        Self {
            env,
            type_translator: ty_translator,
            trait_arena: arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
        }
    }

    /// Get registered trait declarations in the local crate.
    pub fn get_trait_decls(&self) -> HashMap<LocalDefId, specs::TraitSpecDecl<'def>> {
        let decls = self.trait_decls.borrow();
        decls.clone()
    }

    /// Get a map of dependencies between traits.
    pub fn get_trait_deps(&self) -> HashMap<DefId, HashSet<DefId>> {
        let mut dep_map = HashMap::new();

        let decls = self.trait_decls.borrow();
        for trait_decl in decls.keys() {
            // check for other traits we need
            let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(trait_decl.to_def_id());

            let mut deps = HashSet::new();
            for clause in param_env.caller_bounds() {
                let kind = clause.kind().skip_binder();
                if let ty::ClauseKind::Trait(pred) = kind {
                    let other_did = pred.trait_ref.def_id;

                    if other_did != trait_decl.to_def_id() {
                        deps.insert(other_did);
                    }
                }
            }
            dep_map.insert(trait_decl.to_def_id(), deps);
        }

        dep_map
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(name: String) -> specs::LiteralTraitSpec {
        let phys_record = format!("{name}_phys");
        let spec_record = format!("{name}_spec");
        let base_spec = format!("{name}_base_spec");
        let spec_subsumption = format!("{name}_spec_incl");

        specs::LiteralTraitSpec {
            name,
            spec_record,
            base_spec,
            spec_subsumption,
        }
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub fn register_trait(&'def self, ty_translator: &'def TypeTranslator<'def, 'tcx>, did: LocalDefId) -> Result<(), TranslationError<'tcx>> {
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

        // make the literal we are going to use
        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));
        let lit_trait_spec = Self::make_literal_trait_spec(trait_name.clone());
        // already register it for use.
        // In particular, this is also needed to be able to register the methods of this trait
        // below, as they need to be able to access the associated types of this trait already.
        // (in fact, their environment contains their self instance)
        let lit_trait_spec_ref = self.register_shim(did.to_def_id(), lit_trait_spec)?;

        // get generics
        let trait_generics: &'tcx ty::Generics = self.env.tcx().generics_of(did.to_def_id());
        let mut generic_env = Vec::new();
        for param in trait_generics.params.iter() {
            if let rustc_middle::ty::GenericParamDefKind::Type { .. } = param.kind {
                let name = param.name.as_str();
                let lit = specs::LiteralTyParam::new(&name, &name);
                generic_env.push(Some(lit)); 
            }
            else {
                generic_env.push(None);
            }
        }

        // get extra context items from trait annotation
        // TODO
        let extra_context_items = Vec::new();
        let extra_context_items = specs::CoqParamList(extra_context_items);

        // get items
        let mut methods = HashMap::new();
        let mut assoc_types = Vec::new();
        let items: &ty::AssocItems = self.env.tcx().associated_items(did);
        for c in items.in_definition_order() {
            if ty::AssocKind::Fn == c.kind {
                // get attributes
                let attrs =
                    self.env.get_attributes_of_function(c.def_id, |x| propagate_method_attr_from_impl(x));

                // get function name
                let method_name = self
                    .env
                    .get_assoc_item_name(c.def_id)
                    .ok_or(TraitRegistryError::NotATraitMethod(c.def_id))?;
                let method_name = strip_coq_ident(&method_name);

                let name = format!("{trait_name}_{method_name}");
                let spec_name = format!("{name}_base_spec");

                // get spec
                let spec = FunctionTranslator::spec_for_trait_method(self.env, c.def_id, name.clone(), spec_name, attrs.as_slice(), ty_translator, &self)?;

                methods.insert(method_name, spec); 
            }
            else if ty::AssocKind::Type == c.kind {
                // get name
                let type_name = self
                    .env
                    .get_assoc_item_name(c.def_id)
                    .ok_or(TraitRegistryError::NotATraitMethod(c.def_id))?;
                let type_name = strip_coq_ident(&type_name);
                let lit = radium::LiteralTyParam::new(&type_name, &type_name);
                assoc_types.push(lit);
            }
        }

        let base_instance_spec = specs::TraitInstanceSpec::new(methods);
        let decl = specs::TraitSpecDecl::new(lit_trait_spec_ref, extra_context_items, generic_env, assoc_types, base_instance_spec);

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
        spec: specs::LiteralTraitSpec,
    ) -> TraitRegistryResult<'tcx, specs::LiteralTraitSpecRef<'def>> {
        if !self.env.tcx().is_trait(did) {
            return Err(TraitRegistryError::NotATrait(did));
        }

        let mut trait_literals = self.trait_literals.borrow_mut();
        if trait_literals.get(&did).is_some() {
            return Err(TraitRegistryError::TraitAlreadyExists(did));
        }

        let spec = self.trait_arena.alloc(spec);
        trait_literals.insert(did, &*spec);

        Ok(spec)
    }

    /// Lookup a trait.
    pub fn lookup_trait(&self, trait_did: DefId) -> Option<specs::LiteralTraitSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        trait_literals.get(&trait_did).copied()
    }

    /// Get the term for the specification of a trait impl (applied to the given arguments of the trait), 
    /// as well as the list of associated types.
    pub fn get_impl_spec_term(&self, ty_translator: &LocalTypeTranslator<'def, 'tcx>, impl_did: DefId, impl_args: &[ty::GenericArg<'tcx>], trait_args: &[ty::GenericArg<'tcx>]) -> Result<(String, Vec<radium::Type<'def>>), TranslationError<'tcx>> {
        trace!("enter TraitRegistry::get_impl_spec_term for impl_did={impl_did:?} impl_args={impl_args:?} trait_args={trait_args:?}");
        let trait_did = self.env.tcx().trait_id_of_impl(impl_did).ok_or(TraitRegistryError::NotATraitImpl(impl_did))?;

        let trait_instance = self.lookup_trait(trait_did).ok_or(TraitRegistryError::NotATrait(trait_did))?;

        // the base_spec gets all the trait's args as well as the associated types
        let mut all_trait_args = Vec::new();
        for arg in trait_args.iter() {
            if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                let ty = ty_translator.translate_type(&ty)?;
                all_trait_args.push(ty);
            }
        }

        let mut assoc_args = Vec::new();
        // get associated types of this impl
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(impl_did);
        for it in assoc_items.in_definition_order() {
            if it.kind == ty::AssocKind::Type {
                let item_did = it.def_id;
                let item_ty: ty::EarlyBinder<ty::Ty<'tcx>> = self.env.tcx().type_of(item_did);
                let subst_ty = item_ty.instantiate(self.env.tcx(), impl_args);

                let translated_ty = ty_translator.translate_type(&subst_ty)?;
                all_trait_args.push(translated_ty.clone());
                assoc_args.push(translated_ty);
            }
        }

        let term = specs::CoqAppTerm::new(trait_instance.base_spec.clone(), all_trait_args.iter().map(|x| x.to_string()).collect());

        trace!("leave TraitRegistry::get_impl_spec_term");
        Ok((term.to_string(), assoc_args))
    }
}


/// Check if this is a built-in trait
pub fn is_builtin_trait(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let sized_did = utils::try_resolve_did(tcx, &["core", "marker", "Sized"])?;

    // TODO: for these, should instead require the primitive encoding of our Coq formalization
    let send_did = utils::try_resolve_did(tcx, &["core", "marker", "Send"])?;
    let sync_did = utils::try_resolve_did(tcx, &["core", "marker", "Sync"])?;
    let copy_did = utils::try_resolve_did(tcx, &["core", "marker", "Copy"])?;

    Some(trait_did == sized_did)
}

/// Get non-trivial trait requirements of a function's ParamEnv.
pub fn get_nontrivial_trait_requirements<'tcx>(tcx: ty::TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>) -> Vec<ty::TraitRef<'tcx>> {
    let mut trait_refs = Vec::new();

    // TODO: check if caller_bounds does the right thing for implied bounds
    let clauses = param_env.caller_bounds(); 
    for cl in clauses.iter() {
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

/// A using occurrence of a trait in the signature of the function.
#[derive(Debug, Clone)]
pub struct GenericTraitUse<'def> {
    /// the DefId of the trait
    did: DefId,
    /// the self type this is implemented for
    self_ty: ty::ParamTy,
    /// the Coq-level trait use
    pub trait_use: specs::LiteralTraitSpecUse<'def>,
}

impl<'def> GenericTraitUse<'def> {
    /// Create a new trait use.
    pub fn new<'tcx>(
        type_translator: &TypeTranslator<'def, 'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: radium::LiteralTraitSpecRef<'def>,
        is_used_in_self_trait: bool,
    ) -> Self {
        let did = trait_ref.def_id;

        let self_ty = trait_ref.args[0];
        let args = &trait_ref.args.as_slice()[1..];

        // translate the arguments in the scope of the function
        let mut translated_args = Vec::new();
        for arg in args.iter() {
            if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                let translated_ty = type_translator.translate_type(&ty, scope).unwrap();
                translated_args.push(translated_ty);
            }
        }

        // the self param should be a Param that is bound in the function's scope
        let translated_self = type_translator.translate_type(&self_ty.expect_ty(), scope).unwrap();
        let param = if let ty::TyKind::Param(param) = self_ty.expect_ty().kind() {
            *param
        } else {
            unreachable!("self should be a Param");
        };

        // TODO: allow to override the assumed specification using attributes
        let spec_override = None;

        // create a name for this instance by including the args
        let mangled_base = mangle_name_with_args(&format!("{}", spec_ref.name), trait_ref.args.as_slice());
        let spec_use =
            specs::LiteralTraitSpecUse::new(spec_ref, translated_self, translated_args, mangled_base, spec_override, is_used_in_self_trait);

        Self {
            did,
            self_ty: param,
            trait_use: spec_use,
        }
    }

    /// Get the associated types we require for this trait use.
    pub fn get_associated_type_literals(&self, env: &Environment<'_>) -> Vec<specs::LiteralTyParam> {
        let mut assoc_tys: Vec<specs::LiteralTyParam> = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for ty_did in assoc_types.iter() {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            let lit = self.trait_use.make_assoc_type_lit(&strip_coq_ident(&ty_name));
            assoc_tys.push(lit);
        }
        assoc_tys
    }
}

// Next steps:
// - add trait registration from code

// Note: if I use a function which has traits, I need to provide it with the specification I provide.
// This is something I have to provide as the caller
// I need to look in the trait registry and check for registered instances
// TODO: add notion of registered instances/ instance registry.
//
// I guess when I register that I call a function, I should check whether it requires any trait
// implementations (i.e., go over its clauses)
// I should then find out which instance will get picked for it, i.e. which instance gets picked.
//  either this is a Param instance
//  or it's an instance I can concretely resolve.
// in the former case, I guess I give it the spec param recursively
// in the latter case, I check if I have a registered spec for this instance, and use that.
//
// How about structs which use associated types?
// if it's not statically resolvable, I guess it just acts as another type parameter, and it should
// TODO: shelve ADTs with trait constraints
