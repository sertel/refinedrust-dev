// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use log::{info, trace, warn};
use radium::{self, push_str_list};
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use rustc_middle::ty::{IntTy, Ty, TyKind, UintTy};
use typed_arena::Arena;

pub use crate::base::*;
use crate::environment::{polonius_info as info, Environment};
use crate::rustc_middle::ty::TypeFoldable;
use crate::spec_parsers::enum_spec_parser::{EnumSpecParser, VerboseEnumSpecParser};
use crate::spec_parsers::struct_spec_parser::{self, InvariantSpecParser, StructFieldSpecParser};
use crate::traits::normalize_type;
use crate::tyvars::*;

/// Strip symbols from an identifier to be compatible with Coq.
/// In particular things like ' or ::.
pub fn strip_coq_ident(s: &str) -> String {
    String::from(s)
        .replace('\'', "")
        .replace("::", "_")
        .replace(|c: char| !(c.is_alphanumeric() || c == '_'), "")
}

/// Key used for resolving early-bound parameters for function calls.
/// Invariant: All regions contained in these types should be erased, as type parameter instantiation is
/// independent of lifetimes.
/// TODO: handle early-bound lifetimes.
pub type FnGenericKey<'tcx> = Vec<ty::Ty<'tcx>>;

/// Keys used to deduplicate adt uses for `syn_type` assumptions.
/// TODO maybe we should use `SimplifiedType` + `simplify_type` instead of the syntys?
#[derive(Eq, PartialEq, Hash, Debug)]
pub struct AdtUseKey {
    pub base_did: DefId,
    pub generics: Vec<radium::SynType>,
}

impl AdtUseKey {
    pub fn new(defid: DefId, params: &[radium::Type<'_>]) -> Self {
        let generic_syntys: Vec<_> = params.iter().map(|ty| ty.get_syn_type()).collect();
        Self {
            base_did: defid,
            generics: generic_syntys,
        }
    }
}

/// A scope tracking the type translation state when translating the body of a function.
#[derive(Debug)]
pub struct TypeTranslationScope<'def> {
    /// defid of the current function
    pub(crate) did: DefId,

    /// maps generic indices (De Bruijn) to the corresponding Coq names in the current environment
    /// the invariant is that they are Literals
    pub generic_scope: Vec<Option<radium::LiteralTyParam>>,

    /// maps universal lifetime indices (Polonius) to their names. offset by 1 because 0 = static.
    universal_lifetimes: HashMap<ty::RegionVid, String>,

    // TODO currently, these may contain duplicates
    /// collection of tuple types that we use
    pub(crate) tuple_uses: Vec<radium::LiteralTypeUse<'def>>,
    /// Shim uses for the current function
    pub(crate) shim_uses: HashMap<AdtUseKey, radium::LiteralTypeUse<'def>>,
}

impl<'def> TypeTranslationScope<'def> {
    /// Lookup a universal region.
    pub fn lookup_universal_region(&self, lft: ty::RegionVid) -> Option<radium::Lft> {
        info!("Looking up universal lifetime {:?}", lft);
        self.universal_lifetimes.get(&lft).map(|s| s.to_string())
    }

    /// Create a new empty scope for a function.
    pub fn empty(did: DefId) -> Self {
        Self {
            did,
            tuple_uses: Vec::new(),
            shim_uses: HashMap::new(),
            generic_scope: Vec::new(),
            universal_lifetimes: HashMap::new(),
        }
    }

    /// Create a new scope for a function translation with the given generic parameters.
    pub fn new(
        did: DefId,
        ty_params: ty::GenericArgsRef<'_>,
        univ_lfts: HashMap<ty::RegionVid, String>,
    ) -> Result<Self, TranslationError> {
        info!("Entering procedure with ty_params {:?} and univ_lfts {:?}", ty_params, univ_lfts);

        let mut v: Vec<Option<radium::LiteralTyParam>> = Vec::new();
        let mut num_lifetimes = 0;
        for gen_arg in ty_params {
            match gen_arg.unpack() {
                ty::GenericArgKind::Type(ty) => match ty.kind() {
                    TyKind::Param(p) => {
                        info!("ty param {} @ {}", p.name, p.index);
                        let type_name = format!("{}_ty", p.name);
                        let st_name = format!("{}_st", p.name);
                        let rt_name = format!("{}_rt", p.name);

                        let ty_term = type_name;
                        let st_term = st_name;

                        let lit_ty = radium::LiteralTyParam {
                            rust_name: p.name.as_str().to_string(),
                            type_term: ty_term,
                            refinement_type: rt_name,
                            syn_type: st_term,
                        };

                        v.push(Some(lit_ty));
                    },
                    _ => {
                        panic!("enter_generic_scope: not a type parameter");
                    },
                },
                ty::GenericArgKind::Lifetime(r) => {
                    num_lifetimes += 1;
                    match *r {
                        ty::RegionKind::ReLateBound(..) | ty::RegionKind::ReEarlyBound(..) => {
                            // ignore
                            v.push(None);
                        },
                        ty::RegionKind::ReVar(..) => {
                            // ignore
                            v.push(None);
                        },
                        _ => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: format!("Unsupported lifetime generic {:?}", r),
                            });
                        },
                    }
                },
                ty::GenericArgKind::Const(_c) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does not currently support const generics".to_string(),
                    });
                },
            }
        }

        // for closures, not all lifetime parameters materialize in `ty_params`, so we fill them up
        // afterwards
        for _ in 0..(univ_lfts.len() - num_lifetimes) {
            v.push(None);
        }

        Ok(Self {
            did,
            tuple_uses: Vec::new(),
            generic_scope: v,
            universal_lifetimes: univ_lfts,
            shim_uses: HashMap::new(),
        })
    }
}

/// The `TypeTranslator` has two modes:
/// - translation of a type within the generic scope of a function
/// - translation of a type as part of an ADT definition, where we always translate parameters as
/// variables, but need to track dependencies on other ADTs.
#[derive(Debug)]
pub enum TranslationStateInner<'b, 'def: 'b> {
    /// This type is used in a function
    InFunction(&'b mut TypeTranslationScope<'def>),
    /// We are generating the definition of an ADT and this type is used in there
    TranslateAdt(&'b mut HashSet<DefId>),
}
pub type TranslationState<'a, 'b, 'def> = &'a mut TranslationStateInner<'b, 'def>;
pub type InFunctionState<'a, 'def> = &'a mut TypeTranslationScope<'def>;
pub type TranslateAdtState<'a> = &'a mut HashSet<DefId>;

impl<'a, 'def> TranslationStateInner<'a, 'def> {
    const fn in_function(&self) -> bool {
        matches!(*self, Self::InFunction(_))
    }

    const fn translate_adt(&self) -> bool {
        matches!(*self, Self::TranslateAdt(_))
    }
}

pub struct TypeTranslator<'def, 'tcx> {
    env: &'def Environment<'tcx>,

    /// arena for keeping ownership of structs
    /// during building, it will be None, afterwards it will always be Some
    struct_arena: &'def Arena<RefCell<Option<radium::AbstractStruct<'def>>>>,
    /// arena for keeping ownership of enums
    enum_arena: &'def Arena<RefCell<Option<radium::AbstractEnum<'def>>>>,
    /// arena for keeping ownership of shims
    shim_arena: &'def Arena<radium::LiteralType>,

    /// maps ADT variants to struct specifications.
    /// the boolean is true iff this is a variant of an enum.
    /// the literal is present after the variant has been fully translated
    variant_registry: RefCell<
        HashMap<
            DefId,
            (
                String,
                radium::AbstractStructRef<'def>,
                &'tcx ty::VariantDef,
                bool,
                Option<radium::LiteralTypeRef<'def>>,
            ),
        >,
    >,
    /// maps ADTs that are enums to the enum specifications
    /// the literal is present after the enum has been fully translated
    enum_registry: RefCell<
        HashMap<
            DefId,
            (String, radium::AbstractEnumRef<'def>, ty::AdtDef<'tcx>, Option<radium::LiteralTypeRef<'def>>),
        >,
    >,
    /// a registry for abstract struct defs for tuples, indexed by the number of tuple fields
    tuple_registry: RefCell<HashMap<usize, (radium::AbstractStructRef<'def>, radium::LiteralTypeRef<'def>)>>,

    /// dependencies of one ADT definition on another ADT definition
    adt_deps: RefCell<HashMap<DefId, HashSet<DefId>>>,

    /// shims for ADTs
    adt_shims: RefCell<HashMap<DefId, radium::LiteralTypeRef<'def>>>,
}

impl<'def, 'tcx: 'def> TypeTranslator<'def, 'tcx> {
    pub fn new(
        env: &'def Environment<'tcx>,
        struct_arena: &'def Arena<RefCell<Option<radium::AbstractStruct<'def>>>>,
        enum_arena: &'def Arena<RefCell<Option<radium::AbstractEnum<'def>>>>,
        shim_arena: &'def Arena<radium::LiteralType>,
    ) -> Self {
        TypeTranslator {
            env,
            adt_deps: RefCell::new(HashMap::new()),
            adt_shims: RefCell::new(HashMap::new()),
            struct_arena,
            enum_arena,
            shim_arena,
            variant_registry: RefCell::new(HashMap::new()),
            enum_registry: RefCell::new(HashMap::new()),
            tuple_registry: RefCell::new(HashMap::new()),
        }
    }

    /// Intern a literal.
    pub fn intern_literal(&self, lit: radium::LiteralType) -> radium::LiteralTypeRef<'def> {
        self.shim_arena.alloc(lit)
    }

    /// Register a shim for an ADT.
    pub fn register_adt_shim(&self, did: DefId, lit: radium::LiteralType) -> Result<(), String> {
        let lit_ref = self.intern_literal(lit.clone());
        let mut shims = self.adt_shims.borrow_mut();
        if let Some(old) = shims.insert(did, lit_ref) {
            Err(format!("Shim for defid {:?} was {:?} before and has been overridden by {:?}", did, old, lit))
        } else {
            Ok(())
        }
    }

    /// Lookup a shim for an ADT.
    fn lookup_adt_shim(&self, did: DefId) -> Option<radium::LiteralTypeRef<'def>> {
        self.adt_shims.borrow().get(&did).copied()
    }

    /// Get all the struct definitions that clients have used (excluding the variants of enums).
    pub fn get_struct_defs(&self) -> HashMap<DefId, radium::AbstractStructRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, is_of_enum, _)) in self.variant_registry.borrow().iter() {
            // skip structs belonging to enums
            if !is_of_enum {
                defs.insert(*did, *su);
            }
        }
        defs
    }

    /// Get all the variant definitions that clients have used (including the variants of enums).
    pub fn get_variant_defs(&self) -> HashMap<DefId, radium::AbstractStructRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, _, _)) in self.variant_registry.borrow().iter() {
            defs.insert(*did, *su);
        }
        defs
    }

    /// Get all the enum definitions that clients have used.
    pub fn get_enum_defs(&self) -> HashMap<DefId, radium::AbstractEnumRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, _)) in self.enum_registry.borrow().iter() {
            defs.insert(*did, *su);
        }
        defs
    }

    /// Get the dependency map between ADTs.
    pub fn get_adt_deps(&self) -> HashMap<DefId, HashSet<DefId>> {
        let deps = self.adt_deps.borrow();
        deps.clone()
    }

    /// Try to translate a region to a Caesium lifetime.
    /// Note: This relies on all the regions being `ReVar` inference variables.
    fn translate_region<'a, 'b>(
        &self,
        translation_state: TranslationState<'a, 'b, 'def>,
        region: &ty::Region<'tcx>,
    ) -> Option<radium::Lft> {
        match **region {
            ty::RegionKind::ReEarlyBound(early) => {
                info!("Translating region: EarlyBound {:?}", early);
                None
            },
            ty::RegionKind::ReLateBound(idx, r) => {
                info!("Translating region: LateBound {:?} {:?}", idx, r);
                None
            },
            ty::RegionKind::RePlaceholder(placeholder) => {
                // TODO: not sure if any placeholders should remain at this stage.
                info!("Translating region: Placeholder {:?}", placeholder);
                None
            },
            ty::RegionKind::ReStatic => Some("static".to_string()),
            ty::RegionKind::ReErased => Some("erased".to_string()),
            ty::RegionKind::ReVar(v) => match translation_state {
                TranslationStateInner::InFunction(ref scope) => {
                    let r = scope.lookup_universal_region(v);
                    info!("Translating region: ReVar {:?} as {:?}", v, r);
                    r
                },
                _ => {
                    info!("Translating region: ReVar {:?} as None (outside of function)", v);
                    None
                },
            },
            _ => {
                info!("Translating region: {:?}", region);
                None
            },
        }
    }

    /// Lookup an ADT variant and return a reference to its struct def.
    fn lookup_adt_variant(
        &self,
        did: DefId,
    ) -> Result<(radium::AbstractStructRef<'def>, Option<radium::LiteralTypeRef<'def>>), TranslationError>
    {
        if let Some((_n, st, _, _, lit)) = self.variant_registry.borrow().get(&did) {
            Ok((*st, *lit))
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Lookup the literal for an ADT variant.
    fn lookup_adt_variant_literal(
        &self,
        did: DefId,
    ) -> Result<radium::LiteralTypeRef<'def>, TranslationError> {
        if let Some(lit) = self.lookup_adt_shim(did) {
            Ok(lit)
        } else if let Some((_n, _, _, _, lit)) = self.variant_registry.borrow().get(&did) {
            Ok(lit.unwrap())
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Lookup an enum ADT and return a reference to its enum def.
    fn lookup_enum(
        &self,
        did: DefId,
    ) -> Result<(radium::AbstractEnumRef<'def>, Option<radium::LiteralTypeRef<'def>>), TranslationError> {
        if let Some((_n, st, _, lit)) = self.enum_registry.borrow().get(&did) {
            Ok((*st, *lit))
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Lookup the literal for an enum.
    fn lookup_enum_literal(&self, did: DefId) -> Result<radium::LiteralTypeRef<'def>, TranslationError> {
        if let Some(lit) = self.lookup_adt_shim(did) {
            Ok(lit)
        } else if let Some((_n, _, _, lit)) = self.enum_registry.borrow().get(&did) {
            Ok(lit.unwrap())
        } else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Generate a use of a struct, instantiated with type parameters.
    /// This should only be called on tuples and struct ADTs.
    /// Only for internal references as part of type translation.
    fn generate_structlike_use_internal<'a, 'b>(
        &self,
        ty: &Ty<'tcx>,
        variant: Option<rustc_target::abi::VariantIdx>,
        adt_deps: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::Type<'def>, TranslationError> {
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                // Check if we have a shim
                if self.lookup_adt_shim(adt.did()).is_some() {
                    self.generate_adt_shim_use(adt, args, adt_deps)
                } else if adt.is_box() {
                    // TODO: for now, Box gets a special treatment and is not accurately
                    // translated. Reconsider this later on
                    Err(TranslationError::UnknownError("Box is not a proper structlike".to_string()))
                } else if adt.is_struct() {
                    info!("generating struct use for {:?}", adt.did());
                    // register the ADT, if necessary
                    self.register_adt(*adt)?;
                    self.generate_struct_use_noshim(adt.did(), *args, adt_deps).map(radium::Type::Struct)
                } else if adt.is_enum() {
                    if let Some(variant) = variant {
                        self.register_adt(*adt)?;
                        self.generate_enum_variant_use_noshim(adt.did(), variant, args.iter(), adt_deps)
                            .map(radium::Type::Struct)
                    } else {
                        Err(TranslationError::UnknownError(
                            "a non-downcast enum is not a structlike".to_string(),
                        ))
                    }
                } else {
                    Err(TranslationError::UnsupportedType {
                        description: "non-{enum, struct, tuple} ADTs are not supported".to_string(),
                    })
                }
            },
            TyKind::Tuple(args) => self.generate_tuple_use(*args, adt_deps).map(radium::Type::Literal),
            _ => Err(TranslationError::UnknownError("not a structlike".to_string())),
        }
    }

    /// Generate the use of an enum.
    /// Only for internal references as part of type translation.
    fn generate_enum_use_noshim<'a, 'b, F>(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: F,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::AbstractEnumUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating enum use for {:?}", adt_def.did());
        self.register_adt(adt_def)?;

        let (enum_ref, lit_ref) = self.lookup_enum(adt_def.did())?;
        let params = self.translate_generic_args(args, &mut *state)?;
        let key = AdtUseKey::new(adt_def.did(), &params);

        // track this enum use for the current function
        if let TranslationStateInner::InFunction(state) = state {
            let lit_uses = &mut state.shim_uses;

            lit_uses
                .entry(key)
                .or_insert_with(|| radium::LiteralTypeUse::new(lit_ref.unwrap(), params.clone()));
        }

        let enum_use = radium::AbstractEnumUse::new(enum_ref, params);
        Ok(enum_use)
    }

    /// Check if a variant given by a [`DefId`] is [`std::marker::PhantomData`].
    fn is_phantom_data(&self, did: DefId) -> Option<bool> {
        let ty: ty::Ty<'tcx> = self.env.tcx().type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::Adt(def, _) => Some(def.is_phantom_data()),
            _ => None,
        }
    }

    /// Check if a struct is definitely zero-sized.
    fn is_struct_definitely_zero_sized(&self, did: DefId) -> Option<bool> {
        self.is_phantom_data(did)
    }

    /// Translate `generic_args` of an ADT instantiation, tracking dependencies on other ADTs in `adt_deps`.
    fn translate_generic_args<'a, 'b, F>(
        &self,
        args: F,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<Vec<radium::Type<'def>>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        let mut params = Vec::new();

        for arg in args {
            let Some(arg_ty) = arg.as_type() else {
                return Err(TranslationError::UnsupportedFeature {
                    description: "ADTs with lifetime parameters are not supported".to_string(),
                });
            };

            let translated_ty = match state {
                TranslationStateInner::TranslateAdt(ref mut deps) => {
                    self.translate_type_with_deps(&arg_ty, &mut TranslationStateInner::TranslateAdt(deps))?
                },
                TranslationStateInner::InFunction(ref mut scope) => {
                    let mut translated_ty = self
                        .translate_type_with_deps(&arg_ty, &mut TranslationStateInner::InFunction(scope))?;

                    // we need to substitute in the variables according to the function scope
                    translated_ty.subst_params(scope.generic_scope.as_slice());

                    translated_ty
                },
            };

            params.push(translated_ty);
        }

        Ok(params)
    }

    /// Generate the use of a struct.
    /// Only for internal references as part of type translation.
    fn generate_struct_use_noshim<'a, 'b, F>(
        &self,
        variant_id: DefId,
        args: F,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::AbstractStructUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating struct use for {:?}", variant_id);

        if self.is_struct_definitely_zero_sized(variant_id) == Some(true) {
            info!("replacing zero-sized struct with unit");
            return Ok(radium::AbstractStructUse::new_unit());
        }

        let (struct_ref, lit_ref) = self.lookup_adt_variant(variant_id)?;
        let params = self.translate_generic_args(args, &mut *state)?;
        let key = AdtUseKey::new(variant_id, &params);

        if let TranslationStateInner::InFunction(ref mut scope) = state {
            let lit_uses = &mut scope.shim_uses;

            lit_uses
                .entry(key)
                .or_insert_with(|| radium::LiteralTypeUse::new(lit_ref.unwrap(), params.clone()));
        }

        let struct_use = radium::AbstractStructUse::new(struct_ref, params, radium::TypeIsRaw::No);
        Ok(struct_use)
    }

    /// Generate the use of an enum variant.
    /// Only for internal references as part of type translation.
    fn generate_enum_variant_use_noshim<'a, 'b, F>(
        &self,
        adt_id: DefId,
        variant_idx: rustc_target::abi::VariantIdx,
        args: F,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::AbstractStructUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating variant use for variant {:?} of {:?}", variant_idx, adt_id);

        let variant_idx = variant_idx.as_usize();
        let (enum_ref, _lit_ref) = self.lookup_enum(adt_id)?;
        let enum_ref = enum_ref.borrow();
        let enum_ref = enum_ref.as_ref().unwrap();

        let (_, struct_ref, _) = enum_ref.get_variant(variant_idx).unwrap();
        let struct_ref: radium::AbstractStructRef<'def> = *struct_ref;

        // apply the generic parameters according to the mask
        let params = self.translate_generic_args(args, state)?;

        let struct_use = radium::AbstractStructUse::new(struct_ref, params, radium::TypeIsRaw::No);

        // TODO maybe track the whole enum?
        // track this enum use for the current function
        //let mut struct_uses = self.struct_uses.borrow_mut();
        //struct_uses.push(struct_use.clone());

        Ok(struct_use)
    }

    /// Generate a tuple use for a tuple with the given types.
    pub fn generate_tuple_use<'a, 'b, F>(
        &self,
        tys: F,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = Ty<'tcx>>,
    {
        let tys = tys.into_iter();

        let generic_args: Vec<_> = tys.into_iter().map(|ty| ty.into()).collect();
        let params = self.translate_generic_args(generic_args, &mut *state)?;

        let num_components = params.len();
        let (_, lit) = self.get_tuple_struct_ref(num_components);

        // TODO: don't generate duplicates
        let struct_use = radium::LiteralTypeUse::new(lit, params);
        if let TranslationStateInner::InFunction(ref mut scope) = *state {
            scope.tuple_uses.push(struct_use.clone());
        }

        Ok(struct_use)
    }

    /// Get the struct ref for a tuple with `num_components` components.
    fn get_tuple_struct_ref(
        &self,
        num_components: usize,
    ) -> (radium::AbstractStructRef<'def>, radium::LiteralTypeRef<'def>) {
        self.register_tuple(num_components);
        let registry = self.tuple_registry.borrow();
        let (struct_ref, lit) = registry.get(&num_components).unwrap();
        (struct_ref, lit)
    }

    /// Register a tuple type with `num_components` components.
    fn register_tuple(&self, num_components: usize) {
        if self.tuple_registry.borrow().get(&num_components).is_some() {
            return;
        }
        info!("Generating a tuple type with {} components", num_components);
        let struct_def = radium::make_tuple_struct_repr(num_components);
        let literal = self.intern_literal(struct_def.make_literal_type());
        let struct_def = self.struct_arena.alloc(RefCell::new(Some(struct_def)));
        self.tuple_registry.borrow_mut().insert(num_components, (struct_def, literal));
    }

    /// Register an ADT that is being used by the program.
    fn register_adt(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError> {
        trace!("Registering ADT {:?}", def.did());

        if def.is_union() {
            Err(TranslationError::Unimplemented {
                description: "union ADTs are not yet supported".to_string(),
            })
        } else if self.is_struct_definitely_zero_sized(def.did()) == Some(true) {
            Ok(())
        } else if def.is_enum() {
            self.register_enum(def)
        } else if def.is_struct() {
            // register all variants
            for variant in def.variants() {
                self.register_struct(variant, def)?;
            }
            Ok(())
        } else {
            Err(TranslationError::Unimplemented {
                description: format!("unhandled ADT kind: {:?}", def),
            })
        }
    }

    /// Register a struct ADT type that is used by the program.
    fn register_struct(&self, ty: &'tcx ty::VariantDef, adt: ty::AdtDef) -> Result<(), TranslationError> {
        if self.lookup_adt_variant_literal(ty.def_id).is_ok() {
            // already there, that's fine.
            return Ok(());
        }
        info!("registering struct {:?}", ty);

        // first thing: figure out the generics we are using here.
        let mut folder = TyVarFolder::new(self.env.tcx());
        for f in &ty.fields {
            let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
            f_ty.fold_with(&mut folder);
        }
        let mut used_generics: Vec<ty::ParamTy> = folder.get_result().into_iter().collect();

        let mut adt_deps: HashSet<DefId> = HashSet::new();

        // sort according to the index, i.e., the declaration order of the params.
        used_generics.sort();
        info!("used generics: {:?}", used_generics);
        let ty_params: Vec<String> = used_generics.iter().map(|param| param.name.to_string()).collect();

        // build names for ty_params
        let ty_param_defs: Vec<_> = ty_params
            .iter()
            .map(|name| radium::LiteralTyParam {
                rust_name: name.clone(),
                type_term: format!("{}_ty", name),
                refinement_type: format!("{}_rt", name),
                syn_type: format!("{}_st", name),
            })
            .collect();

        // to account for recursive structs and enable establishing circular references,
        // we first generate a dummy struct (None)
        let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

        let tcx = self.env.tcx();
        let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());
        self.variant_registry
            .borrow_mut()
            .insert(ty.def_id, (struct_name, &*struct_def_init, ty, false, None));

        let translate_adt = || {
            let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());
            let (variant_def, invariant_def) =
                self.make_adt_variant(&struct_name, ty, adt, &ty_param_defs, &mut adt_deps)?;

            let mut struct_def = radium::AbstractStruct::new(variant_def, ty_param_defs);
            if let Some(invariant_def) = invariant_def {
                struct_def.add_invariant(invariant_def);
            }
            Ok(struct_def)
        };

        match translate_adt() {
            Ok(struct_def) => {
                let lit = self.intern_literal(struct_def.make_literal_type());

                // finalize the definition
                // TODO for generating the semtype definition, we will also need to track dependencies
                // between structs so that we know when we need recursive types etc.
                let mut struct_def_ref = struct_def_init.borrow_mut();
                *struct_def_ref = Some(struct_def);

                let mut deps_ref = self.adt_deps.borrow_mut();
                deps_ref.insert(adt.did(), adt_deps);

                let mut reg = self.variant_registry.borrow_mut();
                let aref = reg.get_mut(&ty.def_id).unwrap();
                aref.4 = Some(lit);

                Ok(())
            },
            Err(err) => {
                // remove the partial definition
                self.variant_registry.borrow_mut().remove(&ty.def_id);
                Err(err)
            },
        }
    }

    /// Make an ADT variant.
    /// This assumes that this variant has already been pre-registered to account for recursive
    /// occurrences.
    fn make_adt_variant<'a>(
        &self,
        struct_name: &str,
        ty: &'tcx ty::VariantDef,
        adt: ty::AdtDef,
        ty_param_defs: &[radium::LiteralTyParam],
        adt_deps: TranslateAdtState<'a>,
    ) -> Result<(radium::AbstractVariant<'def>, Option<radium::InvariantSpec>), TranslationError> {
        info!("adt variant: {:?}", ty);

        let tcx = self.env.tcx();

        // check for representation flags
        let repr = adt.repr();
        let mut repr_opt = radium::StructRepr::ReprRust;
        if repr.c() {
            repr_opt = radium::StructRepr::ReprC;
        } else if repr.simd() {
            return Err(TranslationError::UnsupportedFeature {
                description: "The SIMD flag is currently unsupported".to_string(),
            });
        } else if repr.packed() {
            return Err(TranslationError::UnsupportedFeature {
                description: "The repr(packed) flag is currently unsupported".to_string(),
            });
        } else if repr.linear() {
            return Err(TranslationError::UnsupportedFeature {
                description: "The linear flag is currently unsupported".to_string(),
            });
        } else if repr.transparent() {
            repr_opt = radium::StructRepr::ReprTransparent;
        }

        let mut builder = radium::VariantBuilder::new(struct_name.to_string(), repr_opt);

        // parse attributes
        let outer_attrs = self.env.get_attributes(ty.def_id);
        // TODO: change once we handle structs with lft parameters
        let lft_params: Vec<(Option<String>, radium::Lft)> = Vec::new();
        let expect_refinement;
        let mut invariant_spec;
        if crate::utils::has_tool_attr(outer_attrs, "refined_by") {
            let outer_attrs = crate::utils::filter_tool_attrs(outer_attrs);
            let mut spec_parser = struct_spec_parser::VerboseInvariantSpecParser::new();
            let ty_name = strip_coq_ident(format!("{}_inv_t", struct_name).as_str());
            let res = spec_parser
                .parse_invariant_spec(&ty_name, &outer_attrs, ty_param_defs, &lft_params)
                .map_err(TranslationError::FatalError)?;
            invariant_spec = Some(res.0);
            expect_refinement = !res.1;
        } else {
            invariant_spec = None;
            expect_refinement = false;
        }
        info!("adt variant spec: {:?}", invariant_spec);

        // build a substitution environment that substitutes all the type parameters by literals
        let ty_env: Vec<Option<radium::LiteralTyParam>> =
            ty_param_defs.iter().map(|names| Some(names.clone())).collect();

        // assemble the field definition
        let mut field_refinements = Vec::new();
        for f in &ty.fields {
            let f_name = f.ident(tcx).to_string();

            let attrs = self.env.get_attributes(f.did);
            let attrs = crate::utils::filter_tool_attrs(attrs);

            let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
            let mut ty =
                self.translate_type_with_deps(&f_ty, &mut TranslationStateInner::TranslateAdt(adt_deps))?;

            // substitute all the type parameters by literals
            ty.subst_params(&ty_env);

            let mut parser = struct_spec_parser::VerboseStructFieldSpecParser::new(
                &ty,
                ty_param_defs,
                &lft_params,
                expect_refinement,
                |lit| self.intern_literal(lit),
            );
            let field_spec =
                parser.parse_field_spec(&f_name, &attrs).map_err(TranslationError::UnknownError)?;

            info!("adt variant field: {:?} -> {} (with rfn {:?})", f_name, field_spec.ty, field_spec.rfn);
            builder.add_field(&f_name, field_spec.ty);

            if expect_refinement {
                if let Some(rfn) = field_spec.rfn {
                    field_refinements.push(rfn);
                } else {
                    return Err(TranslationError::UnknownError(format!(
                        "No refinement annotated for field {:?}",
                        f_name
                    )));
                }
            }
        }

        let struct_def = builder.finish(ty_param_defs);
        info!("finished variant def: {:?}", struct_def);

        // now add the invariant, if one was annotated
        if let Some(ref mut invariant_spec) = invariant_spec {
            if expect_refinement {
                // make a plist out of this
                let mut rfn = String::with_capacity(100);

                rfn.push_str("-[");
                push_str_list!(rfn, &field_refinements, "; ", "#({})");
                rfn.push(']');

                invariant_spec.provide_abstracted_refinement(rfn);
            }
        }

        // TODO for generating the semtype definition, we will also need to track dependencies
        // between structs so that we know when we need recursive types etc.

        Ok((struct_def, invariant_spec))
    }

    /// Make a `GlobalId` for constants (use for discriminants).
    fn make_global_id_for_discr<'a>(
        &self,
        did: DefId,
        env: &'a [ty::GenericArg<'tcx>],
    ) -> rustc_middle::mir::interpret::GlobalId<'tcx> {
        rustc_middle::mir::interpret::GlobalId {
            instance: ty::Instance::new(did, self.env.tcx().mk_args(env)),
            promoted: None,
        }
    }

    fn try_scalar_int_to_i128(s: rustc_middle::ty::ScalarInt) -> Option<i128> {
        s.try_to_int(s.size()).ok()
    }

    /// Build a map from discriminant names to their value, if it fits in a i128.
    fn build_discriminant_map(
        &self,
        def: ty::AdtDef<'tcx>,
    ) -> Result<HashMap<String, i128>, TranslationError> {
        let mut map: HashMap<String, i128> = HashMap::new();
        let variants = def.variants();

        let mut last_explicit_discr: i128 = 0;
        for v in variants {
            let v: &ty::VariantDef = v;
            let name = v.name.to_string();
            info!("Discriminant for {:?}: {:?}", v, v.discr);
            match v.discr {
                ty::VariantDiscr::Explicit(did) => {
                    // we try to const-evaluate the discriminant
                    let evaluated_discr = self
                        .env
                        .tcx()
                        .const_eval_global_id_for_typeck(
                            ty::ParamEnv::empty(),
                            self.make_global_id_for_discr(did, &[]),
                            None,
                        )
                        .map_err(|err| {
                            TranslationError::FatalError(format!(
                                "Failed to const-evaluate discriminant: {:?}",
                                err
                            ))
                        })?;

                    let evaluated_discr = evaluated_discr.ok_or_else(|| {
                        TranslationError::FatalError(format!("Failed to const-evaluate discriminant"))
                    })?;

                    let evaluated_int = evaluated_discr.try_to_scalar_int().unwrap();
                    let evaluated_int = Self::try_scalar_int_to_i128(evaluated_int).ok_or_else(|| {
                        TranslationError::FatalError(format!("Enum discriminant is too large"))
                    })?;

                    info!("const-evaluated enum discriminant: {:?}", evaluated_int);

                    last_explicit_discr = evaluated_int;
                    map.insert(name, evaluated_int);
                },
                ty::VariantDiscr::Relative(offset) => {
                    let idx: i128 = last_explicit_discr + i128::from(offset);
                    map.insert(name, idx);
                },
            }
        }
        info!("Discriminant map for {:?}: {:?}", def, map);
        Ok(map)
    }

    fn does_did_match(&self, did: DefId, path: &[&str]) -> bool {
        let lookup_did = crate::utils::try_resolve_did(self.env.tcx(), path);
        if let Some(lookup_did) = lookup_did {
            if lookup_did == did {
                return true;
            }
        }
        false
    }

    /// Get the spec for a built-in enum like `std::option::Option`.
    fn get_builtin_enum_spec(&self, did: DefId) -> Result<Option<radium::EnumSpec>, TranslationError> {
        let option_spec = radium::EnumSpec {
            rfn_type: radium::CoqType::Literal("_".to_string()),
            variant_patterns: vec![
                ("None".to_string(), vec![], "-[]".to_string()),
                ("Some".to_string(), vec!["x".to_string()], "-[x]".to_string()),
            ],
        };
        let enum_spec = radium::EnumSpec {
            rfn_type: radium::CoqType::Literal("_".to_string()),
            variant_patterns: vec![
                ("inl".to_string(), vec!["x".to_string()], "-[x]".to_string()),
                ("inr".to_string(), vec!["x".to_string()], "-[x]".to_string()),
            ],
        };

        // TODO: find a more modular way to do this.
        if self.does_did_match(did, &["std", "option", "Option"])
            || self.does_did_match(did, &["core", "option", "Option"])
        {
            return Ok(Some(option_spec));
        }

        if self.does_did_match(did, &["std", "result", "Result"])
            || self.does_did_match(did, &["core", "result", "Result"])
        {
            return Ok(Some(enum_spec));
        }

        Ok(None)
    }

    /// Given a Rust enum which has already been registered and whose fields have been translated, generate a
    /// corresponding Coq Inductive as well as an `EnumSpec`.
    fn generate_enum_spec(
        &self,
        def: ty::AdtDef<'tcx>,
        enum_name: &str,
    ) -> (radium::CoqInductive, radium::EnumSpec) {
        trace!("Generating Inductive for enum {:?}", def);

        let mut variants: Vec<radium::CoqVariant> = Vec::new();
        let mut variant_patterns = Vec::new();

        for v in def.variants() {
            let registry = self.variant_registry.borrow();
            let (variant_name, coq_def, variant_def, _, _) = registry.get(&v.def_id).unwrap();
            let coq_def = coq_def.borrow();
            let coq_def = coq_def.as_ref().unwrap();
            let refinement_type = coq_def.plain_rt_def_name().to_string();

            // simple optimization: if the variant has no fields, also this constructor gets no arguments
            let (variant_args, variant_arg_binders, variant_rfn) = if variant_def.fields.is_empty() {
                (vec![], vec![], "-[]".to_string())
            } else {
                let args = vec![(radium::CoqName::Unnamed, radium::CoqType::Literal(refinement_type))];
                (args, vec!["x".to_string()], "x".to_string())
            };

            let variant_def = radium::CoqVariant {
                name: variant_name.to_string(),
                params: radium::CoqParamList(variant_args),
            };

            variants.push(variant_def);
            variant_patterns.push((variant_name.to_string(), variant_arg_binders, variant_rfn));
        }

        // We assume the generated Inductive def is placed in a context where the generic types are in scope.
        let inductive = radium::CoqInductive {
            name: enum_name.to_string(),
            parameters: radium::CoqParamList(vec![]),
            variants,
        };

        let enum_spec = radium::EnumSpec {
            rfn_type: radium::CoqType::Literal(enum_name.to_string()),
            variant_patterns,
        };

        info!("Generated inductive for {:?}: {:?}", def, inductive);

        (inductive, enum_spec)
    }

    /// Register an enum ADT
    fn register_enum(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError> {
        if self.lookup_enum_literal(def.did()).is_ok() {
            // already there, that's fine.
            return Ok(());
        }
        info!("Registering enum {:?}", def.did());

        // pre-register the enum for recursion
        let enum_def_init = self.enum_arena.alloc(RefCell::new(None));
        // gather the other ADTs this one depends on
        let mut adt_deps: HashSet<DefId> = HashSet::new();

        let tcx = self.env.tcx();

        // TODO: currently a hack, I don't know how to query the name properly
        let enum_name = strip_coq_ident(format!("{:?}", def).as_str());

        // first thing: figure out the generics we are using here.
        // we need to search all of the variant types for that.
        let mut folder = TyVarFolder::new(self.env.tcx());
        for v in def.variants() {
            for f in &v.fields {
                let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
                f_ty.fold_with(&mut folder);
            }
        }
        let mut used_generics: Vec<ty::ParamTy> = folder.get_result().into_iter().collect();

        // sort according to the index, i.e., the declaration order of the params.
        used_generics.sort();
        let ty_params: Vec<String> = used_generics.iter().map(|param| param.name.to_string()).collect();
        // build names for ty_params
        let ty_param_defs: Vec<_> = ty_params
            .iter()
            .map(|name| radium::LiteralTyParam {
                rust_name: name.clone(),
                type_term: format!("{}_ty", name),
                refinement_type: format!("{}_rt", name),
                syn_type: format!("{}_st", name),
            })
            .collect();

        info!("enum using generics: {:?}", used_generics);

        // insert partial definition for recursive occurrences
        self.enum_registry
            .borrow_mut()
            .insert(def.did(), (enum_name.clone(), &*enum_def_init, def, None));

        let translate_variants = || {
            let mut variant_attrs = Vec::new();
            for v in def.variants() {
                // now generate the variant
                let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

                let struct_name = strip_coq_ident(format!("{}_{}", enum_name, v.ident(tcx)).as_str());
                self.variant_registry
                    .borrow_mut()
                    .insert(v.def_id, (struct_name.clone(), &*struct_def_init, v, true, None));

                let (variant_def, invariant_def) =
                    self.make_adt_variant(struct_name.as_str(), v, def, &ty_param_defs, &mut adt_deps)?;

                let mut struct_def = radium::AbstractStruct::new(variant_def, ty_param_defs.clone());
                if let Some(invariant_def) = invariant_def {
                    struct_def.add_invariant(invariant_def);
                }

                // also remember the attributes for additional processing
                let outer_attrs = self.env.get_attributes(v.def_id);
                let outer_attrs = crate::utils::filter_tool_attrs(outer_attrs);
                variant_attrs.push(outer_attrs);

                // finalize the definition
                {
                    let lit = self.intern_literal(struct_def.make_literal_type());
                    let mut struct_def_ref = struct_def_init.borrow_mut();
                    *struct_def_ref = Some(struct_def);

                    let mut reg = self.variant_registry.borrow_mut();
                    let aref = reg.get_mut(&v.def_id).unwrap();
                    aref.4 = Some(lit);
                }
            }

            // get the type of the discriminant
            let it = def.repr().discr_type();
            let translated_it = self.translate_integer_type(it)?;

            // build the discriminant map
            let discrs = self.build_discriminant_map(def)?;

            // get representation options
            let repr = def.repr();
            let mut repr_opt = radium::EnumRepr::ReprRust;
            if repr.c() {
                repr_opt = radium::EnumRepr::ReprC;
            } else if repr.simd() {
                return Err(TranslationError::UnsupportedFeature {
                    description: "The SIMD flag is currently unsupported".to_string(),
                });
            } else if repr.packed() {
                return Err(TranslationError::UnsupportedFeature {
                    description: "The repr(packed) flag is currently unsupported".to_string(),
                });
            } else if repr.linear() {
                return Err(TranslationError::UnsupportedFeature {
                    description: "The linear flag is currently unsupported".to_string(),
                });
            } else if repr.transparent() {
                repr_opt = radium::EnumRepr::ReprTransparent;
            }

            // parse annotations for enum type
            let enum_spec;
            let mut inductive_decl = None;
            let builtin_spec = self.get_builtin_enum_spec(def.did())?;
            if let Some(spec) = builtin_spec {
                enum_spec = spec;
            } else if self.env.has_tool_attribute(def.did(), "refined_by") {
                let attributes = self.env.get_attributes(def.did());
                let attributes = crate::utils::filter_tool_attrs(attributes);

                // TODO: change once we handle lft parameters properly
                let lft_params: Vec<(Option<String>, radium::Lft)> = Vec::new();

                let mut parser = VerboseEnumSpecParser::new();
                enum_spec = parser
                    .parse_enum_spec("", &attributes, &variant_attrs, &ty_param_defs, &lft_params)
                    .map_err(TranslationError::FatalError)?;
            } else {
                // generate a specification
                let decl;
                (decl, enum_spec) = self.generate_enum_spec(def, &enum_name);
                inductive_decl = Some(decl);
            }

            let mut enum_builder =
                radium::EnumBuilder::new(enum_name, ty_param_defs, translated_it, repr_opt);
            // now build the enum itself
            for v in def.variants() {
                let (variant_ref, _) = self.lookup_adt_variant(v.def_id)?;
                let variant_name = strip_coq_ident(&v.ident(tcx).to_string());
                let discriminant = discrs.get(&variant_name).unwrap();
                enum_builder.add_variant(&variant_name, variant_ref, *discriminant);
            }
            Ok(enum_builder.finish(inductive_decl, enum_spec))
        };

        match translate_variants() {
            Ok(enum_def) => {
                let lit = self.intern_literal(enum_def.make_literal_type());

                // finalize the definition
                let mut enum_def_ref = enum_def_init.borrow_mut();
                *enum_def_ref = Some(enum_def);

                let mut reg = self.enum_registry.borrow_mut();
                let aref = reg.get_mut(&def.did()).unwrap();
                aref.3 = Some(lit);

                let mut deps_ref = self.adt_deps.borrow_mut();
                deps_ref.insert(def.did(), adt_deps);
                Ok(())
            },
            Err(err) => {
                // deregister the ADT again
                self.enum_registry.borrow_mut().remove(&def.did());
                Err(err)
            },
        }
    }

    fn generate_adt_shim_use<'a, 'b>(
        &self,
        adt: &ty::AdtDef<'tcx>,
        substs: ty::GenericArgsRef<'tcx>,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::Type<'def>, TranslationError> {
        if let Some(shim) = self.lookup_adt_shim(adt.did()) {
            let params = self.translate_generic_args(substs.iter(), &mut *state)?;

            let key = AdtUseKey::new(adt.did(), &params);
            let shim_use = radium::LiteralTypeUse::new(shim, params);

            if let TranslationStateInner::InFunction(ref mut scope) = state {
                // track this shim use for the current function
                scope.shim_uses.entry(key).or_insert_with(|| shim_use.clone());
            }

            Ok(radium::Type::Literal(shim_use))
        } else {
            Err(TranslationError::UnknownError(format!(
                "generate_adt_shim_use called for unknown adt shim {:?}",
                adt.did()
            )))
        }
    }

    // Okay, I don't know what the problem is.
    // 'def outlives 'a
    // 'b outlives 'a
    // I dont' know why it infers that 'a outlives 'def or so.
    //
    // What do I want?
    // I want to pass mutable access to the translation context.
    // In some cases, I need to be able to wrap the translation context.
    // I guess I can just do interior mutability with RefCell.
    //

    /// Translate types, while placing the `DefIds` of ADTs that this type uses in the `adt_deps`
    /// argument, if provided.
    pub fn translate_type_with_deps<'a, 'b>(
        &self,
        ty: &Ty<'tcx>,
        state: TranslationState<'a, 'b, 'def>,
    ) -> Result<radium::Type<'def>, TranslationError> {
        match ty.kind() {
            TyKind::Char => Ok(radium::Type::Char),
            TyKind::Int(it) => Ok(radium::Type::Int(match it {
                IntTy::I8 => radium::IntType::I8,
                IntTy::I16 => radium::IntType::I16,
                IntTy::I32 => radium::IntType::I32,
                IntTy::I64 => radium::IntType::I64,
                IntTy::I128 => radium::IntType::I128,
                IntTy::Isize => radium::IntType::ISize, // should have same size as pointer types
            })),
            TyKind::Uint(it) => Ok(radium::Type::Int(match it {
                UintTy::U8 => radium::IntType::U8,
                UintTy::U16 => radium::IntType::U16,
                UintTy::U32 => radium::IntType::U32,
                UintTy::U64 => radium::IntType::U64,
                UintTy::U128 => radium::IntType::U128,
                UintTy::Usize => radium::IntType::USize, // should have same size as pointer types
            })),
            TyKind::Bool => Ok(radium::Type::Bool),
            TyKind::Float(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support float".to_string(),
            }),
            TyKind::Array(_, _) => Err(TranslationError::UnsupportedFeature {
                description: "Arrays are currently unsupported".to_string(),
            }),
            TyKind::Slice(_) =>
            // TODO this should really be a fat ptr?
            {
                Err(TranslationError::UnsupportedFeature {
                    description: "Slices are currently unsupported".to_string(),
                })
            },
            TyKind::RawPtr(_) => Ok(radium::Type::RawPtr),
            // TODO: this will have to change for handling fat ptrs. see the corresponding rustc
            // def for inspiration.
            TyKind::Ref(region, ty, mutability) => {
                if ty.is_str() || ty.is_array_slice() {
                    // special handling for slice types commonly used in error handling branches we
                    // don't care about
                    // TODO: emit a warning
                    return Ok(radium::Type::Unit);
                }

                let translated_ty = self.translate_type_with_deps(ty, &mut *state)?;
                // in case this isn't a universal region, we usually won't care about it.
                let lft = if let Some(lft) = self.translate_region(&mut *state, region) {
                    lft
                } else {
                    warn!("Failed to translate region {:?}", region);
                    format!("placeholder_lft")
                };

                match mutability {
                    rustc_ast::ast::Mutability::Mut => Ok(radium::Type::MutRef(Box::new(translated_ty), lft)),
                    _ => Ok(radium::Type::ShrRef(Box::new(translated_ty), lft)),
                }
            },
            TyKind::Never => Ok(radium::Type::Never),
            TyKind::Adt(adt, substs) => {
                if adt.is_box() {
                    // extract the type parameter
                    // the second parameter is the allocator, which we ignore for now
                    assert!(substs.len() == 2);
                    let ty = substs[0].expect_ty();
                    let translated_ty = self.translate_type_with_deps(&ty, &mut *state)?;
                    Ok(radium::Type::BoxType(Box::new(translated_ty)))
                } else if self.is_struct_definitely_zero_sized(adt.did()) == Some(true) {
                    // make this unit
                    Ok(radium::Type::Unit)
                } else {
                    if let TranslationStateInner::TranslateAdt(ref mut adt_deps) = *state {
                        adt_deps.insert(adt.did());
                    }

                    if self.lookup_adt_shim(adt.did()).is_some() {
                        self.generate_adt_shim_use(adt, substs, &mut *state)
                    } else if adt.is_struct() {
                        self.generate_structlike_use_internal(ty, None, &mut *state)
                    } else if adt.is_enum() {
                        let eu = self.generate_enum_use_noshim(*adt, *substs, &mut *state)?;
                        Ok(radium::Type::Enum(eu))
                    } else {
                        Err(TranslationError::UnsupportedFeature {
                            description: format!("unsupported ADT {:?}", ty),
                        })
                    }
                }
            },
            TyKind::Tuple(params) => {
                if params.len() == 0 {
                    Ok(radium::Type::Unit)
                } else {
                    let su = self.generate_tuple_use(params.iter(), &mut *state)?;
                    Ok(radium::Type::Literal(su))
                }
            },
            TyKind::Param(param_ty) => {
                if let TranslationStateInner::InFunction(ref mut scope) = state {
                    // lookup in the function's scope
                    info!("using generic type param: {}", param_ty);
                    if let Some(param) = scope.generic_scope.get(param_ty.index as usize) {
                        if let Some(ty) = param {
                            Ok(radium::Type::LiteralParam(ty.clone()))
                        } else {
                            Err(TranslationError::UnknownVar(format!(
                                "unknown generic parameter {:?} is a region {:?}, not a type",
                                param_ty, param
                            )))
                        }
                    } else {
                        Err(TranslationError::UnknownVar(format!("unknown generic parameter {:?}", param_ty)))
                    }
                } else {
                    info!("using generic type param: {}", param_ty);
                    Ok(radium::Type::Var(param_ty.index as usize))
                }
            },
            TyKind::Foreign(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support extern types".to_string(),
            }),
            TyKind::Str => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not support str".to_string(),
            }),
            TyKind::FnDef(_, _) => Err(TranslationError::Unimplemented {
                description: "translate_type_with_deps: implement FnDef".to_string(),
            }),
            TyKind::FnPtr(_) => Err(TranslationError::Unimplemented {
                description: format!("translate_type_with_deps: implement FnPtr ({:?})", ty),
            }),
            TyKind::Dynamic(..) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not trait objects".to_string(),
            }),
            TyKind::Closure(_def, closure_args) => {
                // We replace this with the tuple of the closure's state
                let clos = closure_args.as_closure();

                let upvar_tys = clos.tupled_upvars_ty();
                self.translate_type_with_deps(&upvar_tys, &mut *state)
            },
            TyKind::Generator(..) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not support generators".to_string(),
            }),
            TyKind::GeneratorWitness(..) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not support generators".to_string(),
            }),
            TyKind::GeneratorWitnessMIR(_, _) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does currently not support generators".to_string(),
            }),
            TyKind::Alias(_, _) =>
            // TODO: probably need this when translating trait definitions
            {
                Err(TranslationError::UnsupportedType {
                    description: "RefinedRust does not support Alias types".to_string(),
                })
            },
            TyKind::Bound(_, _) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support higher-ranked types".to_string(),
            }),
            TyKind::Placeholder(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support higher-ranked types".to_string(),
            }),
            TyKind::Infer(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support infer types".to_string(),
            }),
            TyKind::Error(_) => Err(TranslationError::UnsupportedType {
                description: "RefinedRust does not support higher-ranked types".to_string(),
            }),
        }
    }

    /// Translate a `rustc_attr::IntType` (this is different from the `rustc_ty` `IntType`).
    const fn translate_int_type(&self, it: rustc_attr::IntType) -> Result<radium::IntType, TranslationError> {
        match it {
            rustc_attr::IntType::SignedInt(it) => Ok(match it {
                rustc_ast::IntTy::I8 => radium::IntType::I8,
                rustc_ast::IntTy::I16 => radium::IntType::I16,
                rustc_ast::IntTy::I32 => radium::IntType::I32,
                rustc_ast::IntTy::I64 => radium::IntType::I64,
                rustc_ast::IntTy::I128 => radium::IntType::I128,
                rustc_ast::IntTy::Isize => radium::IntType::ISize,
            }),
            rustc_attr::IntType::UnsignedInt(it) => Ok(match it {
                rustc_ast::UintTy::U8 => radium::IntType::U8,
                rustc_ast::UintTy::U16 => radium::IntType::U16,
                rustc_ast::UintTy::U32 => radium::IntType::U32,
                rustc_ast::UintTy::U64 => radium::IntType::U64,
                rustc_ast::UintTy::U128 => radium::IntType::U128,
                rustc_ast::UintTy::Usize => radium::IntType::USize,
            }),
        }
    }

    /// Translate a `rustc_attr::IntType` (this is different from the `rustc_ty` `IntType`).
    const fn translate_integer_type(
        &self,
        it: rustc_abi::IntegerType,
    ) -> Result<radium::IntType, TranslationError> {
        match it {
            rustc_abi::IntegerType::Fixed(size, sign) => {
                if sign {
                    Ok(match size {
                        rustc_abi::Integer::I8 => radium::IntType::I8,
                        rustc_abi::Integer::I16 => radium::IntType::I16,
                        rustc_abi::Integer::I32 => radium::IntType::I32,
                        rustc_abi::Integer::I64 => radium::IntType::I64,
                        rustc_abi::Integer::I128 => radium::IntType::I128,
                    })
                } else {
                    Ok(match size {
                        rustc_abi::Integer::I8 => radium::IntType::U8,
                        rustc_abi::Integer::I16 => radium::IntType::U16,
                        rustc_abi::Integer::I32 => radium::IntType::U32,
                        rustc_abi::Integer::I64 => radium::IntType::U64,
                        rustc_abi::Integer::I128 => radium::IntType::U128,
                    })
                }
            },
            rustc_abi::IntegerType::Pointer(sign) => {
                if sign {
                    Ok(radium::IntType::ISize)
                } else {
                    Ok(radium::IntType::USize)
                }
            },
        }
    }

    /// Get the name for a field of an ADT or tuple type
    pub fn get_field_name_of(
        &self,
        f: &rustc_target::abi::FieldIdx,
        ty: Ty<'tcx>,
        variant: Option<usize>,
    ) -> Result<String, TranslationError> {
        let tcx = self.env.tcx();
        match ty.kind() {
            TyKind::Adt(def, _) => {
                info!("getting field name of {:?} at {} (variant {:?})", f, ty, variant);
                if def.is_struct() {
                    let i = def.variants().get(rustc_target::abi::VariantIdx::from_usize(0)).unwrap();
                    i.fields.get(*f).map(|f| f.ident(tcx).to_string()).ok_or_else(|| {
                        TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty))
                    })
                } else if def.is_enum() {
                    let variant = variant.unwrap();
                    let i = def.variants().get(rustc_target::abi::VariantIdx::from_usize(variant)).unwrap();
                    i.fields.get(*f).map(|f| f.ident(tcx).to_string()).ok_or_else(|| {
                        TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty))
                    })
                } else {
                    Err(TranslationError::UnsupportedFeature {
                        description: format!("unsupported field access {:?}to ADT {:?}", f, ty),
                    })
                }
            },
            TyKind::Tuple(_) => Ok(f.index().to_string()),
            TyKind::Closure(_, _) => {
                // treat as tuple of upvars
                Ok(f.index().to_string())
            },
            _ => Err(TranslationError::InvalidLayout),
        }
    }

    /// Get the name of a variant of an enum.
    pub fn get_variant_name_of(
        &self,
        ty: Ty<'tcx>,
        variant: rustc_target::abi::VariantIdx,
    ) -> Result<String, TranslationError> {
        match ty.kind() {
            TyKind::Adt(def, _) => {
                info!("getting variant name of {:?} at {}", variant, ty);
                let i = def.variants().get(variant).unwrap();
                Ok(i.name.to_string())
            },
            _ => Err(TranslationError::InvalidLayout),
        }
    }
}

/// Public functions used by the `BodyTranslator`.
impl<'def, 'tcx> TypeTranslator<'def, 'tcx> {
    /// Translate a MIR type to the Caesium syntactic type we need when storing an element of the type,
    /// substituting all generics.
    pub fn translate_type_to_syn_type(
        &self,
        ty: &Ty<'tcx>,
        scope: InFunctionState<'_, 'def>,
    ) -> Result<radium::SynType, TranslationError> {
        // give an environment substituting in the generics
        self.translate_type(ty, &mut *scope).map(|mut ty| {
            ty.subst_params(&scope.generic_scope);
            ty.get_syn_type()
        })
    }

    /// Translate type in the scope of a function.
    pub fn translate_type(
        &self,
        ty: &Ty<'tcx>,
        scope: InFunctionState<'_, 'def>,
    ) -> Result<radium::Type<'def>, TranslationError> {
        self.translate_type_with_deps(ty, &mut TranslationStateInner::InFunction(&mut *scope))
    }

    /// Translate type in an empty scope.
    pub fn translate_type_in_empty_scope(
        &self,
        ty: &Ty<'tcx>,
    ) -> Result<radium::Type<'def>, TranslationError> {
        let mut s = HashSet::new();
        self.translate_type_with_deps(ty, &mut TranslationStateInner::TranslateAdt(&mut s))
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_structlike_use<'a>(
        &self,
        ty: &Ty<'tcx>,
        variant: Option<rustc_target::abi::VariantIdx>,
        scope: InFunctionState<'a, 'def>,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError> {
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                if adt.is_struct() {
                    info!("generating struct use for {:?}", adt.did());
                    // register the ADT, if necessary
                    self.register_adt(*adt)?;
                    self.generate_struct_use(adt.did(), *args, &mut *scope)
                } else if adt.is_enum() {
                    if let Some(variant) = variant {
                        self.register_adt(*adt)?;
                        let v = &adt.variants()[variant];
                        self.generate_enum_variant_use(v.def_id, args.iter(), scope).map(Some)
                    } else {
                        Err(TranslationError::UnknownError(
                            "a non-downcast enum is not a structlike".to_string(),
                        ))
                    }
                } else {
                    Err(TranslationError::UnsupportedType {
                        description: "non-{enum, struct, tuple} ADTs are not supported".to_string(),
                    })
                }
            },
            TyKind::Tuple(args) => {
                self.generate_tuple_use(*args, &mut TranslationStateInner::InFunction(scope)).map(Some)
            },
            TyKind::Closure(_, args) => {
                // use the upvar tuple
                let closure_args = args.as_closure();
                let upvars = closure_args.upvar_tys();
                self.generate_tuple_use(upvars, &mut TranslationStateInner::InFunction(scope)).map(Some)
            },
            _ => Err(TranslationError::UnknownError("not a structlike".to_string())),
        }
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_enum_use<F>(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: F,
        state: InFunctionState<'_, 'def>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating enum use for {:?}", adt_def.did());
        self.register_adt(adt_def)?;

        let enum_ref: radium::LiteralTypeRef<'def> = self.lookup_enum_literal(adt_def.did())?;
        let params =
            self.translate_generic_args(args, &mut TranslationStateInner::InFunction(&mut *state))?;
        let key = AdtUseKey::new(adt_def.did(), &params);
        let enum_use = radium::LiteralTypeUse::new(enum_ref, params);

        // track this enum use for the current function
        let enum_uses = &mut state.shim_uses;
        enum_uses.entry(key).or_insert_with(|| enum_use.clone());

        Ok(enum_use)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_struct_use<F>(
        &self,
        variant_id: DefId,
        args: F,
        scope: InFunctionState<'_, 'def>,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating struct use for {:?}", variant_id);

        if self.is_struct_definitely_zero_sized(variant_id) == Some(true) {
            info!("replacing zero-sized struct with unit");
            return Ok(None);
        }

        let params =
            self.translate_generic_args(args, &mut TranslationStateInner::InFunction(&mut *scope))?;
        let key = AdtUseKey::new(variant_id, &params);

        let struct_ref: radium::LiteralTypeRef<'def> = self.lookup_adt_variant_literal(variant_id)?;
        let struct_use = radium::LiteralTypeUse::new(struct_ref, params);

        scope.shim_uses.entry(key).or_insert_with(|| struct_use.clone());

        Ok(Some(struct_use))
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    pub fn generate_enum_variant_use<'a, F>(
        &self,
        variant_id: DefId,
        args: F,
        scope: InFunctionState<'a, 'def>,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        info!("generating enum variant use for {:?}", variant_id);

        let x: TranslationState<'_, '_, 'def> = &mut TranslationStateInner::InFunction(&mut *scope);
        let params = self.translate_generic_args(args, x)?;
        let _key = AdtUseKey::new(variant_id, &params);

        let struct_ref: radium::LiteralTypeRef<'def> = self.lookup_adt_variant_literal(variant_id)?;
        let struct_use = radium::LiteralTypeUse::new(struct_ref, params);

        // TODO: track?
        // generate the struct use key
        //let mut shim_uses = self.shim_uses.borrow_mut();
        //if !shim_uses.contains_key(&key) {
        //shim_uses.insert(key, struct_use.clone());
        //}

        Ok(struct_use)
    }

    pub fn make_tuple_use<'a, 'b>(
        &self,
        translated_tys: Vec<radium::Type<'def>>,
        state: TranslationState<'a, 'b, 'def>,
    ) -> radium::Type<'def> {
        let num_components = translated_tys.len();
        if num_components == 0 {
            return radium::Type::Unit;
        }

        let (_, lit) = self.get_tuple_struct_ref(num_components);
        // TODO: don't generate duplicates
        //let struct_use = radium::AbstractStructUse::new(struct_ref, translated_tys,
        // radium::TypeIsRaw::Yes);
        let struct_use = radium::LiteralTypeUse::new(lit, translated_tys);
        if let TranslationStateInner::InFunction(ref mut scope) = *state {
            scope.tuple_uses.push(struct_use.clone());
        }

        radium::Type::Literal(struct_use)
    }
}

/// Type translator bundling the function scope
pub struct LocalTypeTranslator<'a, 'def, 'tcx> {
    pub translator: &'a TypeTranslator<'def, 'tcx>,
    pub scope: RefCell<TypeTranslationScope<'def>>,
}
impl<'a, 'def, 'tcx> LocalTypeTranslator<'a, 'def, 'tcx> {
    pub const fn new(translator: &'a TypeTranslator<'def, 'tcx>, scope: TypeTranslationScope<'def>) -> Self {
        Self {
            translator,
            scope: RefCell::new(scope),
        }
    }

    /// Translate a MIR type to the Caesium syntactic type we need when storing an element of the type,
    /// substituting all generics.
    pub fn translate_type_to_syn_type(&self, ty: &Ty<'tcx>) -> Result<radium::SynType, TranslationError> {
        let ty = self.normalize(*ty)?;
        let mut scope = self.scope.borrow_mut();
        self.translator.translate_type_to_syn_type(&ty, &mut scope)
    }

    /// Translate type.
    pub fn translate_type(&self, ty: &Ty<'tcx>) -> Result<radium::Type<'def>, TranslationError> {
        let ty = self.normalize(*ty)?;
        let mut scope = self.scope.borrow_mut();
        self.translator.translate_type(&ty, &mut scope)
    }

    /// Translate type without normalizing first.
    pub fn translate_type_no_normalize(&self, ty: &Ty<'tcx>) -> Result<radium::Type<'def>, TranslationError> {
        let mut scope = self.scope.borrow_mut();
        self.translator.translate_type(ty, &mut scope)
    }

    /// Translate a MIR type to the Caesium syntactic type we need when storing an element of the type,
    /// substituting all generics, without normalizing first.
    pub fn translate_type_to_syn_type_no_normalize(
        &self,
        ty: &Ty<'tcx>,
    ) -> Result<radium::SynType, TranslationError> {
        let mut scope = self.scope.borrow_mut();
        self.translator.translate_type_to_syn_type(ty, &mut scope)
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_structlike_use(
        &self,
        ty: &Ty<'tcx>,
        variant: Option<rustc_target::abi::VariantIdx>,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError> {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_structlike_use(ty, variant, &mut scope)
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_enum_use<F>(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: F,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_enum_use(adt_def, args, &mut scope)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub fn generate_struct_use<F>(
        &self,
        variant_id: DefId,
        args: F,
    ) -> Result<Option<radium::LiteralTypeUse<'def>>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_struct_use(variant_id, args, &mut scope)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    pub fn generate_enum_variant_use<F>(
        &self,
        variant_id: DefId,
        args: F,
    ) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_enum_variant_use(variant_id, args, &mut scope)
    }

    pub fn make_tuple_use(&self, translated_tys: Vec<radium::Type<'def>>) -> radium::Type<'def> {
        let mut scope = self.scope.borrow_mut();
        self.translator
            .make_tuple_use(translated_tys, &mut TranslationStateInner::InFunction(&mut scope))
    }

    /// Translates a syntactic type to an op type.
    pub fn translate_syn_type_to_op_type(&self, st: &radium::SynType) -> radium::OpType {
        let scope = self.scope.borrow();
        st.optype_typaram(&scope.generic_scope)
    }

    /// Translates a syntactic type to a layout term.
    pub fn translate_syn_type_to_layout(&self, st: &radium::SynType) -> radium::Layout {
        let scope = self.scope.borrow();
        st.layout_term_typaram(&scope.generic_scope)
    }

    pub fn generate_tuple_use<F>(&self, tys: F) -> Result<radium::LiteralTypeUse<'def>, TranslationError>
    where
        F: IntoIterator<Item = Ty<'tcx>>,
    {
        let mut scope = self.scope.borrow_mut();
        self.translator
            .generate_tuple_use(tys, &mut TranslationStateInner::InFunction(&mut scope))
    }

    /// Format the Coq representation of an atomic region.
    pub fn format_atomic_region(&self, r: &info::AtomicRegion) -> String {
        let scope = self.scope.borrow();
        format_atomic_region_direct(r, Some(&*scope))
    }

    /// Normalize a type in the given function environment.
    pub fn normalize<T>(&self, ty: T) -> Result<T, TranslationError>
    where
        T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
    {
        let scope = self.scope.borrow();
        normalize_in_function(scope.did, self.translator.env.tcx(), ty)
    }
}

/// Normalize a type in the given function environment.
pub fn normalize_in_function<'tcx, T>(
    function_did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    ty: T,
) -> Result<T, TranslationError>
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let param_env = tcx.param_env(function_did);
    normalize_type(tcx, param_env, ty)
        .map_err(|e| TranslationError::TraitResolution(format!("normalization error: {:?}", e)))
}

/// Format the Coq representation of an atomic region.
pub fn format_atomic_region_direct(
    r: &info::AtomicRegion,
    scope: Option<&TypeTranslationScope<'_>>,
) -> String {
    match r {
        info::AtomicRegion::Loan(_, r) => {
            format!("llft{}", r.index())
        },
        info::AtomicRegion::Universal(_, r) => {
            if let Some(scope) = scope {
                match scope.lookup_universal_region(*r) {
                    Some(s) => s,
                    None => format!("ulft{}", r.index()),
                }
            } else {
                format!("ulft{}", r.index())
            }
        },
        info::AtomicRegion::PlaceRegion(r) => {
            format!("plft{}", r.index())
        },
        info::AtomicRegion::Unknown(r) => {
            format!("vlft{}", r.index())
        },
    }
}
