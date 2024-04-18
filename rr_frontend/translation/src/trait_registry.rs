use std::cell::RefCell;
use std::collections::HashMap;

use log::{info, trace};
use radium::{code, specs};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use typed_arena::Arena;

use crate::base::TranslationError;
use crate::environment::Environment;
use crate::type_translator::{generate_args_inst_key, GenericsKey, LocalTypeTranslator};

#[derive(Debug, Clone)]
pub enum TraitRegistryError<'tcx> {
    /// This DefId is not a trait
    NotATrait(DefId),
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

/// A specification for a particular instance of a trait
pub struct TraitInstanceSpec<'def> {
    /// a map from identifiers to the associated types
    assoc_types: HashMap<String, specs::LiteralTyParam>,
    /// a map from the identifiers to the method specs
    methods: HashMap<String, specs::FunctionSpec<'def>>,
}

/// A using occurrence of a trait spec.
#[derive(Debug, Clone)]
pub struct LiteralTraitSpec {
    /// Name of the trait
    name: String,

    /// The name of the Coq definition for the physical information
    /// (Coq def has no parameter)
    phys_record: String,
    /// The name of the Coq definition for the spec information
    /// (Coq def has no parameter)
    spec_record: String,

    /// The basic specification annotated on the trait definition
    /// (Coq def has self, type parameters, as well as associated types)
    base_spec: String,
    /// The relation saying that an implementation satisfies a spec
    /// (Coq def has no parameters)
    spec_rel: String,
}
pub type LiteralTraitSpecRef<'def> = &'def LiteralTraitSpec;

impl LiteralTraitSpec {
    /// Make the name for the method spec field of the spec record.
    pub fn make_spec_method_name(&self, method: &str) -> String {
        format!("{}_{method}_spec", self.name)
    }

    /// Make the name for the method loc field of the phys record.
    pub fn make_phys_loc_name(&self, method: &str) -> String {
        format!("{}_{method}_loc", self.name)
    }

    /// Make the name for the method arg_sts field of the phys record.
    pub fn make_phys_arg_sts_name(&self, method: &str) -> String {
        format!("{}_{method}_arg_sts", self.name)
    }

    /// Make the name for the type field of the spec record.
    pub fn make_spec_ty_name(&self, ty: &str) -> String {
        format!("{}_{ty}_ty", self.name)
    }

    /// Make the name for the type st field of the phys record.
    pub fn make_phys_st_name(&self, ty: &str) -> String {
        format!("{}_{ty}_st", self.name)
    }
}

/// A reference to a trait instantiated with its parameters in the verification of a function.
#[derive(Debug, Clone)]
pub struct LiteralTraitSpecUse<'def> {
    pub trait_ref: LiteralTraitSpecRef<'def>,
    /// the instantiation for the self parameter
    pub self_inst: specs::Type<'def>,
    /// the instantiation for the type parameters
    pub params_inst: Vec<specs::Type<'def>>,

    /// Name for the phys parameter for this use
    pub phys_param_name: String,
}

impl<'def> LiteralTraitSpecUse<'def> {
    pub fn new(
        trait_ref: LiteralTraitSpecRef<'def>,
        self_inst: specs::Type<'def>,
        params_inst: Vec<specs::Type<'def>>,
        phys_param_name: String,
    ) -> Self {
        Self {
            trait_ref,
            self_inst,
            params_inst,
            phys_param_name,
        }
    }

    /// Get the term for the location of a method of this instance.
    pub fn get_loc_term_of_method(&self, method: &str) -> String {
        format!("{}.({})", self.phys_param_name, self.trait_ref.make_phys_loc_name(method))
    }

    /// Get the term for the syntype list of a method of this instance.
    pub fn get_arg_sts_term_of_method(&self, method: &str) -> String {
        format!("{}.({})", self.phys_param_name, self.trait_ref.make_phys_arg_sts_name(method))
    }

    /// Get the term for the syntype of an associated type of this instance.
    pub fn get_assoc_st_term_of_method(&self, ty: &str) -> String {
        format!("{}.({})", self.phys_param_name, self.trait_ref.make_phys_st_name(ty))
    }
}

/// When translating a trait declaration, we should generate this, bundling all the components of
/// the trait together.
pub struct TraitSpecDecl<'def> {
    /// A reference to all the Coq definition names we should generate.
    lit: LiteralTraitSpecRef<'def>,

    /// a list of extra things we assume in the Coq context
    extra_coq_context: specs::CoqParamList,

    /// The generics this trait uses
    generics: Vec<Option<specs::LiteralTyParam>>,

    /// The default specification from the trait declaration
    default_spec: TraitInstanceSpec<'def>,
}

/// When translating an impl block, we should generate this, which bundles all components of the
/// implementation together.
pub struct ImplSpec<'def> {
    /// name of the implementation
    name: String,
    /// The name of the record instance for physical information
    phys_record: String,
    /// The name of the record instance for spec information
    spec_record: String,
    /// The name of the proof that the base spec is implied by the more specific spec
    spec_subsumption: String,

    /// reference to the trait this is implementing
    of_trait: LiteralTraitSpecRef<'def>,

    /// the implementation of the associated types
    assoc_types: HashMap<String, specs::Type<'def>>,
    /// the implementation and specification for the method implementations
    methods: HashMap<String, code::Function<'def>>,
}

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
    /// trait declarations
    trait_decls: RefCell<HashMap<DefId, TraitSpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<HashMap<DefId, LiteralTraitSpecRef<'def>>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<LiteralTraitSpec>,
}

impl<'tcx, 'def> TraitRegistry<'tcx, 'def> {
    /// Create an empty trait registry.
    pub fn new(env: &'def Environment<'tcx>, arena: &'def Arena<LiteralTraitSpec>) -> Self {
        Self {
            env,
            trait_arena: arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
        }
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(name: String) -> LiteralTraitSpec {
        let phys_record = format!("{name}_phys");
        let spec_record = format!("{name}_spec");
        let base_spec = format!("{name}_base_spec");
        let spec_rel = format!("{name}_has_spec");

        LiteralTraitSpec {
            name,
            phys_record,
            spec_record,
            base_spec,
            spec_rel,
        }
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub const fn register_trait(&self, did: DefId) -> TraitRegistryResult<'tcx, ()> {
        // TODO
        // - make a TraitSpecDecl and insert it
        // - use make_literal_trait_spec

        Err(TraitRegistryError::Unknown)
    }

    /// Register a shim with the trait registry.
    ///
    /// Errors:
    /// - NotATrait(did) if did is not a trait
    /// - TraitAlreadyExists(did) if this trait has already been registered
    pub fn register_shim(
        &self,
        did: DefId,
        spec: LiteralTraitSpec,
    ) -> TraitRegistryResult<'tcx, LiteralTraitSpecRef<'def>> {
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
    pub fn lookup_trait(&self, trait_did: DefId) -> Option<LiteralTraitSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        trait_literals.get(&trait_did).copied()
    }
}

/// A using occurrence of a trait in the signature of the function.
#[derive(Debug, Clone)]
pub struct GenericTraitUse<'def> {
    /// the DefId of the trait
    did: DefId,
    /// the self type this is implemented for
    self_ty: ty::ParamTy,
    /// the Coq-level trait use
    trait_use: LiteralTraitSpecUse<'def>,
}
// further items we need:
// - TODO: think about spec overrides. We want to put requirements on the specification of traits when
//   assuming a trait implementation.

impl<'def> GenericTraitUse<'def> {
    /// Create a new trait use.
    pub fn new<'tcx>(
        type_translator: &LocalTypeTranslator<'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: LiteralTraitSpecRef<'def>,
    ) -> Self {
        let did = trait_ref.def_id;

        let self_ty = trait_ref.args[0];
        let args = &trait_ref.args.as_slice()[1..];

        // translate the arguments in the scope of the function
        let mut translated_args = Vec::new();
        for arg in args.iter() {
            if let ty::GenericArgKind::Type(ty) = arg.unpack() {
                let translated_ty = type_translator.translate_type(&ty).unwrap();
                translated_args.push(translated_ty);
            }
        }

        // the self param should be a Param that is bound in the function's scope
        let translated_self = type_translator.translate_type(&self_ty.expect_ty()).unwrap();
        let param = if let ty::TyKind::Param(param) = self_ty.expect_ty().kind() {
            *param
        } else {
            unreachable!("self should be a Param");
        };

        // TODO: should include generic args in the name
        let phys_param_name = format!("{}_phys", spec_ref.name);

        let spec_use = LiteralTraitSpecUse::new(spec_ref, translated_self, translated_args, phys_param_name);

        Self {
            did,
            self_ty: param,
            trait_use: spec_use,
        }
    }
}

/// A scope for keeping track of traits for generic args in a function.
pub struct GenericTraitScope<'tcx, 'def> {
    /// map from (trait_id, generics) to the corresponding trait use
    used_traits: HashMap<(DefId, GenericsKey<'tcx>), GenericTraitUse<'def>>,
    // TODO: maybe index by the set of parameters for the trait?
    // we need to be able to look up the specific instance for the set of generic args
}

impl<'tcx, 'def> GenericTraitScope<'tcx, 'def> {
    /// Initializes this trait scope for a function with ParamEnv `env` and generic parameters
    /// `function_params`.
    pub fn new<'a, 'b>(
        tcx: ty::TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        type_translator: &'b LocalTypeTranslator<'def, 'tcx>,
        trait_registry: &'a TraitRegistry<'tcx, 'def>,
    ) -> TraitRegistryResult<'tcx, Self> {
        trace!("enter GenericTraitScope::new with param_env={param_env:?}");

        let mut used_traits = HashMap::new();

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
                    // TODO: maybe filter Sized, Copy, Send, Sync?

                    // lookup the trait in the trait registry
                    if let Some(trait_spec) = trait_registry.lookup_trait(trait_ref.def_id) {
                        let trait_use = GenericTraitUse::new(type_translator, trait_ref, trait_spec);

                        let key = (trait_ref.def_id, generate_args_inst_key(tcx, trait_ref.args).unwrap());
                        used_traits.insert(key, trait_use);
                    } else {
                        return Err(TraitRegistryError::UnregisteredTrait(trait_ref.def_id));
                    }
                }
            }
        }

        trace!("leave GenericTraitScope::new with used_traits={used_traits:?}");

        Ok(Self { used_traits })
    }

    /// Lookup the trait use for a specific trait with given parameters.
    /// (here, args includes the self parameter as the first element)
    pub fn lookup_trait_use(
        &self,
        tcx: ty::TyCtxt<'tcx>,
        trait_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> TraitRegistryResult<'tcx, &LiteralTraitSpecUse<'def>> {
        if !tcx.is_trait(trait_did) {
            return Err(TraitRegistryError::NotATrait(trait_did));
        }

        let key = (trait_did, generate_args_inst_key(tcx, args).unwrap());
        if let Some(trait_ref) = self.used_traits.get(&key) {
            Ok(&trait_ref.trait_use)
        } else {
            Err(TraitRegistryError::UnknownLocalInstance(trait_did, args))
        }
    }
}

/// A trait registry for the local environment in a function.
pub struct LocalTraitRegistry<'tcx, 'def> {
    registry: &'def TraitRegistry<'tcx, 'def>,
    scope: GenericTraitScope<'tcx, 'def>,
}

impl<'tcx, 'def> LocalTraitRegistry<'tcx, 'def> {
    pub const fn new(registry: &'def TraitRegistry<'tcx, 'def>, scope: GenericTraitScope<'tcx, 'def>) -> Self {
        Self { registry, scope }
    }
}

// Next steps:
// - implement lookup when calling a Param function
// - add the trait requirements to the emitted code
