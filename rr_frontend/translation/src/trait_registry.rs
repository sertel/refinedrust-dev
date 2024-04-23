use std::cell::RefCell;
use std::collections::HashMap;

use log::{info, trace};
use radium::{code, specs};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use typed_arena::Arena;

use crate::base::TranslationError;
use crate::environment::Environment;
use crate::type_translator::{InFunctionState, generate_args_inst_key, GenericsKey, TypeTranslator, LocalTypeTranslator, strip_coq_ident};

use crate::utils;
use crate::function_body::{get_arg_syntypes_for_procedure_call, FunctionTranslator, mangle_name_with_args};

use crate::spec_parsers::propagate_method_attr_from_impl;


#[derive(Debug, Clone)]
pub enum TraitRegistryError<'tcx> {
    /// This DefId is not a trait
    NotATrait(DefId),
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


/// Get the name of a trait method without the path prefix.
pub fn get_assoc_item_name<'tcx>(tcx: ty::TyCtxt<'tcx>, trait_method_did: DefId) -> Option<String> {
    let def_path = tcx.def_path(trait_method_did);
    if let Some(last_elem) = def_path.data.last() {
        if let Some(name) = last_elem.data.get_opt_name() {
            return Some(strip_coq_ident(name.as_str()));
        }
    }
    None
}

/// A specification for a particular instance of a trait
#[derive(Clone, Debug)]
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
    pub name: String,

    /// The name of the Coq definition for the spec information
    /// (Coq def has no parameter)
    pub spec_record: String,

    /// The basic specification annotated on the trait definition
    /// (Coq def has self, type parameters, as well as associated types)
    pub base_spec: String,
    /// The subsumption relation between specs
    /// (Coq def has no parameters)
    pub spec_subsumption: String,
}
pub type LiteralTraitSpecRef<'def> = &'def LiteralTraitSpec;

impl LiteralTraitSpec {
    /// Make the name for the method spec field of the spec record.
    pub fn make_spec_method_name(&self, method: &str) -> String {
        format!("{}_{method}_spec", self.name)
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

    /// the name including the generic args
    mangled_base: String,
}

impl<'def> LiteralTraitSpecUse<'def> {
    pub fn new(
        trait_ref: LiteralTraitSpecRef<'def>,
        self_inst: specs::Type<'def>,
        params_inst: Vec<specs::Type<'def>>,
        mangled_base: String,
    ) -> Self {
        Self {
            trait_ref,
            self_inst,
            params_inst,
            mangled_base,
        }
    }

    /// Get the name for a spec parameter for this trait instance.
    pub fn make_spec_param_name(&self) -> String {
        format!("{}_spec", self.mangled_base)
    }

    /// Make the name for the location parameter of a use of a method of this trait parameter.
    pub fn make_loc_name(&self, mangled_method_name: &str) -> String {
        format!("{}_{}_loc", self.mangled_base, mangled_method_name)
    }

    /// Make the term for the specification of the given method.
    pub fn make_method_spec_term(&self, method_name: &str) -> String {
        format!("{}.({})", self.make_spec_param_name(), self.trait_ref.make_spec_method_name(method_name))
    }

    /// Make the names for the Coq-level parameters for an associated type of this instance.
    pub fn make_assoc_type_lit(&self, assoc_type: &str) -> specs::LiteralTyParam {
        let rust_name = format!("{}_{}", self.mangled_base, assoc_type);
        let ty_name = format!("{rust_name}_ty");
        let rt_name = format!("{rust_name}_rt");
        let st_name = format!("{rust_name}_st");

        specs::LiteralTyParam {
            rust_name,
            type_term: ty_name,
            refinement_type: rt_name, 
            syn_type: st_name,
        }
    }
}

/// When translating a trait declaration, we should generate this, bundling all the components of
/// the trait together.
#[derive(Clone, Debug)]
pub struct TraitSpecDecl<'def> {
    /// A reference to all the Coq definition names we should generate.
    pub lit: LiteralTraitSpecRef<'def>,

    /// a list of extra things we assume in the Coq context
    extra_coq_context: specs::CoqParamList,

    /// The generics this trait uses
    generics: Vec<Option<specs::LiteralTyParam>>,

    /// The default specification from the trait declaration
    default_spec: TraitInstanceSpec<'def>,
}

impl<'def> TraitSpecDecl<'def> {
    //pub fn new(lit: LiteralTraitSpecRef<'def>, extra_params
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
    type_translator: &'def TypeTranslator<'def, 'tcx>,

    /// trait declarations
    trait_decls: RefCell<HashMap<LocalDefId, TraitSpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<HashMap<DefId, LiteralTraitSpecRef<'def>>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<LiteralTraitSpec>,
}

impl<'tcx, 'def> TraitRegistry<'tcx, 'def> {
    /// Create an empty trait registry.
    pub fn new(env: &'def Environment<'tcx>, ty_translator: &'def TypeTranslator<'def, 'tcx>, arena: &'def Arena<LiteralTraitSpec>) -> Self {
        Self {
            env,
            type_translator: ty_translator,
            trait_arena: arena,
            trait_decls: RefCell::new(HashMap::new()),
            trait_literals: RefCell::new(HashMap::new()),
        }
    }

    /// Get registered trait declarations in the local crate.
    pub fn get_trait_decls(&self) -> HashMap<LocalDefId, TraitSpecDecl<'def>> {
        let decls = self.trait_decls.borrow();     
        decls.clone()
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(name: String) -> LiteralTraitSpec {
        let phys_record = format!("{name}_phys");
        let spec_record = format!("{name}_spec");
        let base_spec = format!("{name}_base_spec");
        let spec_subsumption = format!("{name}_spec_incl");

        LiteralTraitSpec {
            name,
            spec_record,
            base_spec,
            spec_subsumption,
        }
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub fn register_trait(&self, did: LocalDefId) -> TraitRegistryResult<'tcx, ()> {
        trace!("enter TraitRegistry::register_trait for did={did:?}");

        // make the literal we are going to use
        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));
        let lit_trait_spec = Self::make_literal_trait_spec(trait_name);
        // already register it for use
        let lit_trait_spec_ref = self.register_shim(did.to_def_id(), lit_trait_spec)?;

        // get generics
        // TODO

        // get items
        let children = self.env.tcx().module_children_local(did);
        for c in children.iter() {
            if let rustc_hir::def::Res::Def(def_kind, def_id) = c.res {
                if def_kind == rustc_hir::def::DefKind::AssocFn {

                    // get attributes
                    let attrs = self.env.get_attributes_of_function(did.into(), |x| propagate_method_attr_from_impl(x));

                    // get function name
                    let name = get_assoc_item_name(self.env.tcx(), did.into()).ok_or_else(|| TraitRegistryError::NotATraitMethod(did.into()))?;

                    // TODO
                    //FunctionTranslator::spec_for_trait_method(&self.env, def_id, ) 
                     
                }

            }
        }
        
        //let decl = TraitSpecDecl

        trace!("leave TraitRegistry::register_trait");
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
    pub trait_use: LiteralTraitSpecUse<'def>,
}

impl<'def> GenericTraitUse<'def> {
    /// Create a new trait use.
    pub fn new<'tcx>(
        type_translator: &TypeTranslator<'def, 'tcx>,
        scope: InFunctionState<'_, 'def, 'tcx>,
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

        // create a name for this instance by including the args
        let mangled_base = mangle_name_with_args(&format!("{}", spec_ref.name), trait_ref.args.as_slice());
        let spec_use = LiteralTraitSpecUse::new(spec_ref, translated_self, translated_args, mangled_base);

        Self {
            did,
            self_ty: param,
            trait_use: spec_use,
        }
    }
}

// Next steps:
// - implement lookup when calling a Param function
// - add trait registration from code
// - add trait shim generation
// - add the trait requirements to the emitted code
