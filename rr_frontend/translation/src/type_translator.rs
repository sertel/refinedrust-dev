// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;

use rustc_hir::def_id::DefId;
use rustc_middle::ty as ty;
use rustc_middle::ty::{Ty, IntTy, UintTy, TyKind};
//use rustc_middle::mir::Field;
use crate::rustc_middle::ty::TypeFoldable;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;
use std::fmt::Write;

use typed_arena::Arena;

use crate::environment::Environment;

use radium;

use crate::spec_parsers::struct_spec_parser::{self, InvariantSpecParser, StructFieldSpecParser};
use crate::spec_parsers::enum_spec_parser::{VerboseEnumSpecParser, EnumSpecParser};

use crate::tyvars::*;
pub use crate::base::*;

/// Strip symbols from an identifier to be compatible with Coq.
/// In particular things like ' or ::.
pub(crate) fn strip_coq_ident(s: &str) -> String {
    let s = str::replace(s, "'", "");
    let s = str::replace(&s, "::", "_");
    let s = s.replace(|c: char| !(c.is_alphanumeric() || c == '_'), "");
    s
}

/// Key used for resolving early-bound parameters for function calls.
/// Invariant: All regions contained in these types should be erased, as type parameter instantiation is
/// independent of lifetimes.
/// TODO: handle early-bound lifetimes.
pub type FnGenericKey<'tcx> = Vec<ty::Ty<'tcx>>;

/// Keys used to deduplicate struct uses for syn_type assumptions.
/// TODO maybe we should use SimplifiedType + simplify_type instead of the syntys?
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct AdtUseKey {
    pub base_struct: DefId,
    pub generics: Vec<radium::SynType>,
}


// TODO(refactor): move the function-specific stuff out of here and into the BodyTranslator.
pub struct TypeTranslator<'def, 'tcx> {
    env: &'def Environment<'tcx>,


    /// maps universal lifetime indices (Polonius) to their names. offset by 1 because 0 = static.
    universal_lifetimes: RefCell<Vec<String>>,

    /// arena for keeping ownership of structs
    /// during building, it will be None, afterwards it will always be Some
    struct_arena: &'def Arena<RefCell<Option<radium::AbstractStruct<'def>>>>,
    /// arena for keeping ownership of enums
    enum_arena: &'def Arena<RefCell<Option<radium::AbstractEnum<'def>>>>,

    /// maps ADT variants to struct specifications.
    /// the boolean is true iff this is a variant of an enum.
    variant_registry: RefCell<HashMap<DefId, (String, radium::AbstractStructRef<'def>, &'tcx ty::VariantDef, bool)>>,
    /// maps ADTs to their (Coq-)name and def
    /// TODO what do we need this for.
    adt_registry: RefCell<HashMap<DefId, (String, ty::AdtDef<'tcx>)>>,
    /// maps ADTs that are enums to the enum specifications
    enum_registry: RefCell<HashMap<DefId, (String, radium::AbstractEnumRef<'def>, ty::AdtDef<'tcx>)>>,

    /// a registry for abstract struct defs for tuples, indexed by the number of tuple fields
    tuple_registry: RefCell<HashMap<usize, radium::AbstractStructRef<'def>>>,

    // TODO currently, these may contain duplicates
    /// collection of tuple types that we use
    pub(crate) tuple_uses: RefCell<Vec<radium::AbstractStructUse<'def>>>,
    /// AbstractStructUses for this function
    pub(crate) struct_uses: RefCell<HashMap<AdtUseKey, radium::AbstractStructUse<'def>>>,
    /// AbstractEnumUses for the current function
    pub(crate) enum_uses: RefCell<HashMap<AdtUseKey, radium::AbstractEnumUse<'def>>>,
    /// maps generic indices (De Bruijn) to the corresponding Coq names in the current environment
    /// the invariant is that they are Literals, consisting of three names:
    /// for the syntactic type, the type, and the refinement type.
    /// This contains options because we skip over region parameters.
    pub generic_scope: RefCell<Vec<Option<radium::Type<'def>>>>,
    /// for convenience: a copy of generic_scope that just contains the syntype names
    pub synty_scope: RefCell<Vec<Option<radium::SynType>>>,
    /// for convenience: a copy of generic_scope that just contains the refinement type names
    pub rfnty_scope: RefCell<Vec<Option<radium::CoqType>>>,
}

impl <'def, 'tcx : 'def> TypeTranslator<'def, 'tcx> {
    pub fn new(env: &'def Environment<'tcx>,
               struct_arena: &'def Arena<RefCell<Option<radium::AbstractStruct<'def>>>>,
               enum_arena: &'def Arena<RefCell<Option<radium::AbstractEnum<'def>>>>,
               ) -> Self {
        TypeTranslator { env,
            generic_scope: RefCell::new(Vec::new()),
            synty_scope: RefCell::new(Vec::new()),
            rfnty_scope: RefCell::new(Vec::new()),
            universal_lifetimes: RefCell::new(Vec::new()),
            struct_arena,
            enum_arena,
            variant_registry: RefCell::new(HashMap::new()),
            adt_registry: RefCell::new(HashMap::new()),
            enum_registry: RefCell::new(HashMap::new()),
            tuple_uses: RefCell::new(Vec::new()),
            struct_uses: RefCell::new(HashMap::new()),
            enum_uses: RefCell::new(HashMap::new()),
            tuple_registry: RefCell::new(HashMap::new()),
        }
    }

    /// Get all the struct definitions that clients have used (excluding the variants of enums).
    pub fn get_struct_defs(&self) -> HashMap<DefId, radium::AbstractStructRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _, is_of_enum)) in self.variant_registry.borrow().iter() {
            // skip structs belonging to enums
            if !is_of_enum {
                defs.insert(*did, *su);
            }
        }
        defs
    }

    /// Get all the enum definitions that clients have used.
    pub fn get_enum_defs(&self) -> HashMap<DefId, radium::AbstractEnumRef<'def>> {
        let mut defs = HashMap::new();
        for (did, (_, su, _)) in self.enum_registry.borrow().iter() {
            defs.insert(*did, *su);
        }
        defs
    }

    /// Enter a procedure and add corresponding type parameters to the scope, as well as universal
    /// lifetimes with given names.
    pub fn enter_procedure(&self, ty_params: &ty::GenericArgsRef<'tcx>, univ_lfts: Vec<String>) -> Result<(), TranslationError> {
        info!("Entering procedure with ty_params {:?} and univ_lfts {:?}", ty_params, univ_lfts);

        let mut v: Vec<Option<radium::Type<'def>>> = Vec::new();
        let mut syntypes = Vec::new();
        let mut rfntypes = Vec::new();
        for gen_arg in ty_params.iter() {
            match gen_arg.unpack() {
                ty::GenericArgKind::Type(ty) => {
                    match ty.kind() {
                        TyKind::Param(p) => {
                            info!("ty param {} @ {}", p.name, p.index);
                            let type_name = format!("{}_ty", p.name);
                            let st_name = format!("{}_st", p.name);
                            let rt_name = format!("{}_rt", p.name);

                            let ty_term = radium::CoqAppTerm::new_lhs(type_name);
                            let st_term = radium::CoqAppTerm::new_lhs(st_name);
                            v.push(Some(radium::Type::Literal(
                                    Some(p.name.as_str().to_string()),
                                    ty_term,
                                    radium::CoqType::Literal(rt_name.clone()),
                                    radium::SynType::Literal(st_term.clone()),
                                    // TODO: maybe add something here?
                                    radium::TypeAnnotMeta::empty())));
                            syntypes.push(Some(radium::SynType::Literal(st_term)));
                            rfntypes.push(Some(radium::CoqType::Literal(rt_name)));
                        },
                        _ => {
                            panic!("enter_generic_scope: not a type parameter");
                        },
                    }
                },
                ty::GenericArgKind::Lifetime(r) => {
                    match *r {
                        ty::RegionKind::ReLateBound(..)
                        | ty::RegionKind::ReEarlyBound(..) => {
                            // ignore
                            v.push(None);
                            syntypes.push(None);
                            rfntypes.push(None);
                        },
                        _ => {
                            return Err(TranslationError::UnsupportedFeature{description:
                                format!("Unsupported lifetime generic {:?}", r)});
                        },
                    }
                },
                ty::GenericArgKind::Const(_c) => {
                    return Err(TranslationError::UnsupportedFeature{description:
                        "RefinedRust does not currently support const generics".to_string()});
                },
            }
        }

        self.universal_lifetimes.replace(univ_lfts);
        self.generic_scope.replace(v);
        self.synty_scope.replace(syntypes);
        self.rfnty_scope.replace(rfntypes);
        Ok(())
    }

    /// Leave a procedure and remove the corresponding type parameters from the scope.
    pub fn leave_procedure(&self) {
        self.generic_scope.replace(Vec::new());
        self.universal_lifetimes.replace(Vec::new());
        self.synty_scope.replace(Vec::new());
        self.rfnty_scope.replace(Vec::new());
        self.struct_uses.replace(HashMap::new());
        self.tuple_uses.replace(Vec::new());
        self.enum_uses.replace(HashMap::new());
    }

    /// Lookup a universal lifetime.
    pub fn lookup_universal_lifetime(&self, lft: ty::RegionVid) -> Option<radium::Lft> {
        // offset by 1 due to static which is at zero
        self.universal_lifetimes.borrow().get(lft.as_usize() - 1).map(|s| s.to_string())
    }

    /// Try to translate a region to a Caesium lifetime.
    /// Note: This relies on all the regions being ReVar inference variables.
    fn translate_region(&self, region: &ty::Region<'tcx>) -> Option<radium::Lft> {
        match **region {
            ty::RegionKind::ReEarlyBound(early) => {
                info!("Translating region: EarlyBound {:?}", early);
                // TODO is the index here really the right one?
                //self.lookup_universal_lifetime(early.index)
                None
            },
            ty::RegionKind::RePlaceholder(placeholder) => {
                // TODO: not sure if any placeholders should remain at this stage.
                info!("Translating region: Placeholder {:?}", placeholder);
                None
            },
            ty::RegionKind::ReStatic => {
                Some("static".to_string())
            },
            ty::RegionKind::ReErased => {
                Some("erased".to_string())
            },
            ty::RegionKind::ReVar(v) => {
                self.lookup_universal_lifetime(v)
            },
            _ => {
                info!("Translating region: {:?}", region);
                None
            }
        }
    }

    /// Lookup an ADT variant and return a reference to its struct def.
    fn lookup_adt_variant(&self, did: DefId) -> Result<radium::AbstractStructRef<'def>, TranslationError> {
        if let Some((_n, st, _, _)) = self.variant_registry.borrow().get(&did) {
            Ok(*st)
        }
        else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Lookup an enum ADT and return a reference to its enum def.
    fn lookup_enum(&self, did: DefId) -> Result<radium::AbstractEnumRef<'def>, TranslationError> {
        if let Some((_n, st, _)) = self.enum_registry.borrow().get(&did) {
            Ok(*st)
        }
        else {
            Err(TranslationError::UnknownError(format!("could not find type: {:?}", did)))
        }
    }

    /// Generate a use of a struct, instantiated with type parameters.
    /// This should only be called on tuples and struct ADTs.
    pub fn generate_structlike_use(&self, ty: &Ty<'tcx>, variant: Option<rustc_target::abi::VariantIdx>) -> Result<radium::AbstractStructUse<'def>, TranslationError> {
        match ty.kind() {
            TyKind::Adt(adt, args) => {
                if adt.is_box() {
                    // TODO: for now, Box gets a special treatment and is not accurately
                    // translated. Reconsider this later on
                    Err(TranslationError::UnknownError("Box is not a proper structlike".to_string()))
                }
                else if adt.is_struct() {
                    info!("generating struct use for {:?}", adt.did());
                    // register the ADT, if necessary
                    self.register_adt(*adt)?;
                    self.generate_struct_use(adt.did(), *args)
                }
                else if adt.is_enum() {
                    if let Some(variant) = variant {
                        self.register_adt(*adt)?;
                        self.generate_enum_variant_use(adt.did(), variant, args.iter())
                    }
                    else {
                        Err(TranslationError::UnknownError("a non-downcast enum is not a structlike".to_string()))
                    }
                }
                else {
                    Err(TranslationError::UnsupportedType{ description: "non-{enum, struct, tuple} ADTs are not supported".to_string()})
                }
            },
            TyKind::Tuple(args) => {
                self.generate_tuple_use(args.into_iter())
            },
            _ => {
                Err(TranslationError::UnknownError("not a structlike".to_string()))
            }
        }
    }

    /// Generate the use of an enum.
    pub fn generate_enum_use<F>(&self, adt_def: ty::AdtDef<'tcx>, args: F) -> Result<radium::AbstractEnumUse<'def>, TranslationError>
        where F: IntoIterator<Item=ty::GenericArg<'tcx>>
    {
        info!("generating enum use for {:?}", adt_def.did());
        self.register_adt(adt_def)?;

        let enum_ref: radium::AbstractEnumRef<'def> = self.lookup_enum(adt_def.did())?;
        // apply the generic parameters
        let mut params = Vec::new();
        let generic_env = &*self.generic_scope.borrow();

        let mut generic_syntys = Vec::new();
        for arg in args.into_iter() {
            let arg_ty = arg.expect_ty();
            let mut translated_ty = self.translate_type(&arg_ty)?;
            // we need to substitute in the variables according to the function scope
            translated_ty.subst(generic_env.as_slice());
            //translated_ty.subst
            generic_syntys.push(translated_ty.get_syn_type());
            params.push(translated_ty);
        }

        let enum_use = radium::AbstractEnumUse::new(enum_ref, params);

        // track this enum use for the current function
        let key = AdtUseKey { base_struct: adt_def.did(), generics: generic_syntys};
        let mut enum_uses = self.enum_uses.borrow_mut();
        if !enum_uses.contains_key(&key) {
            enum_uses.insert(key, enum_use.clone());
        }

        Ok(enum_use)
    }

    /// Check if a variant given by a [DefId] is [std::marker::PhantomData].
    fn is_phantom_data(&self, did: DefId) -> Option<bool> {
        let ty: ty::Ty<'tcx> = self.env.tcx().type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::Adt(def, _) => {
                Some(def.is_phantom_data())
            },
            _ => {
                None
            }
        }
    }

    /// Check if a struct is definitely zero-sized.
    fn is_struct_definitely_zero_sized(&self, did: DefId) -> Option<bool> {
        self.is_phantom_data(did)
    }

    /// Generate the use of a struct.
    pub fn generate_struct_use<F>(&self, variant_id: DefId, args: F) -> Result<radium::AbstractStructUse<'def>, TranslationError>
        where F: IntoIterator<Item=ty::GenericArg<'tcx>>
    {
        info!("generating struct use for {:?}", variant_id);

        if let Some(true) = self.is_struct_definitely_zero_sized(variant_id) {
            info!("replacing zero-sized struct with unit");
            return Ok(radium::AbstractStructUse::new_unit());
        }

        let struct_ref: radium::AbstractStructRef<'def> = self.lookup_adt_variant(variant_id)?;
        // apply the generic parameters
        let mut params = Vec::new();
        let generic_env = &*self.generic_scope.borrow();

        let mut generic_syntys = Vec::new();

        for arg in args.into_iter() {
            let arg_ty = arg.expect_ty();
            let mut translated_ty = self.translate_type(&arg_ty)?;
            // we need to substitute in the variables according to the function scope
            translated_ty.subst(generic_env.as_slice());
            //translated_ty.subst
            generic_syntys.push(translated_ty.get_syn_type());
            params.push(translated_ty);
        }

        let struct_use = radium::AbstractStructUse::new(struct_ref, params);

        // generate the struct use key
        let key = AdtUseKey { base_struct: variant_id, generics: generic_syntys};
        let mut struct_uses = self.struct_uses.borrow_mut();
        if !struct_uses.contains_key(&key) {
            struct_uses.insert(key, struct_use.clone());
        }

        Ok(struct_use)
    }

    /// Generate the use of an enum variant.
    pub fn generate_enum_variant_use<F>(&self, adt_id: DefId, variant_idx: rustc_target::abi::VariantIdx, args: F) -> Result<radium::AbstractStructUse<'def>, TranslationError>
        where F: IntoIterator<Item=ty::GenericArg<'tcx>>
    {
        info!("generating variant use for variant {:?} of {:?}", variant_idx, adt_id);

        let variant_idx = variant_idx.as_usize();
        let enum_ref: radium::AbstractEnumRef<'def> = self.lookup_enum(adt_id)?;
        let enum_ref = enum_ref.borrow();
        let enum_ref = enum_ref.as_ref().unwrap();

        let (_, struct_ref, mask, _) = enum_ref.get_variant(variant_idx).unwrap();
        let struct_ref: radium::AbstractStructRef<'def> = *struct_ref;

        // apply the generic parameters according to the mask
        let mut params = Vec::new();
        let generic_env = &*self.generic_scope.borrow();

        for (arg, bit) in args.into_iter().zip(mask.iter()) {
            if *bit {
                let arg_ty = arg.expect_ty();
                let mut translated_ty = self.translate_type(&arg_ty)?;
                // we need to substitute in the variables according to the function scope
                translated_ty.subst(generic_env.as_slice());
                params.push(translated_ty);
            }
        }

        let struct_use = radium::AbstractStructUse::new(struct_ref, params);

        // TODO maybe track the whole enum?
        // track this enum use for the current function
        //let mut struct_uses = self.struct_uses.borrow_mut();
        //struct_uses.push(struct_use.clone());

        Ok(struct_use)
    }

    /// Generate a tuple use for a tuple with the given types.
    pub fn generate_tuple_use<F>(&self, tys: F) -> Result<radium::AbstractStructUse<'def>, TranslationError>
        where F: IntoIterator<Item=Ty<'tcx>>
    {
        let tys = tys.into_iter();

        let generic_env = &*self.generic_scope.borrow();
        let mut params = Vec::new();
        for arg_ty in tys {
            let mut translated_ty = self.translate_type(&arg_ty)?;
            // we need to substitute in the variables according to the function scope
            translated_ty.subst(generic_env.as_slice());
            params.push(translated_ty);
        }

        let num_components = params.len();
        let struct_ref = self.get_tuple_struct_ref(num_components);

        // TODO: don't generate duplicates
        let struct_use = radium::AbstractStructUse::new(struct_ref, params);
        self.tuple_uses.borrow_mut().push(struct_use.clone());

        Ok(struct_use)
    }

    /// Get the struct ref for a tuple with [num_components] components.
    fn get_tuple_struct_ref(&self, num_components: usize) -> radium::AbstractStructRef<'def> {
        if self.tuple_registry.borrow().get(&num_components).is_none() {
            self.register_tuple(num_components);
        }
        let registry = self.tuple_registry.borrow();
        let struct_ref = registry.get(&num_components).unwrap();
        struct_ref
    }

    /// Register a tuple type with [num_components] components.
    fn register_tuple(&self, num_components: usize) {
        info!("Generating a tuple type with {} components", num_components);
        let struct_def = radium::make_tuple_struct_repr(num_components);
        let struct_def = self.struct_arena.alloc(RefCell::new(Some(struct_def)));
        self.tuple_registry.borrow_mut().insert(num_components, struct_def);
    }


    /// Register an ADT that is being used by the program.
    fn register_adt(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError> {
        if self.adt_registry.borrow().get(&def.did()).is_some() {
            return Ok(());
        }
        info!("Registering ADT {:?}", def);

        {
            let mut adb = self.adt_registry.borrow_mut();
            adb.deref_mut().insert(def.did(), ("".to_string(), def));
        }

        if def.is_union() {
            Err(TranslationError::Unimplemented {description: "union ADTs are not yet supported".to_string()})
        }
        else if let Some(true) = self.is_struct_definitely_zero_sized(def.did()) {
            Ok(())
        }
        else if def.is_enum() {
            self.register_enum(def)
        }
        else if def.is_struct() {
            // register all variants
            for variant in def.variants().iter() {
                self.register_struct(variant, def)?;
            }
            Ok(())
        }
        else {
            Err(TranslationError::Unimplemented {description: format!("unhandled ADT kind: {:?}", def)})
        }
    }

    /// Register a struct ADT type that is used by the program.
    fn register_struct(&self, ty: &'tcx ty::VariantDef, adt: ty::AdtDef) -> Result<(), TranslationError> {
        if let Some(_) = self.variant_registry.borrow().get(&ty.def_id) {
            // already there, that's fine.
            return Ok(())
        }
        info!("registering struct {:?}", ty);

        // first thing: figure out the generics we are using here.
        let mut folder = TyVarFolder::new(self.env.tcx());
        for f in ty.fields.iter() {
            let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
            f_ty.fold_with(&mut folder);
        }
        let mut used_generics: Vec<ty::ParamTy> = folder.get_result().into_iter().collect();

        // sort according to the index, i.e., the declaration order of the params.
        used_generics.sort();
        info!("used generics: {:?}", used_generics);
        let ty_params: Vec<String> = used_generics.iter().map(|param| param.name.to_string()).collect();

        // build names for ty_params
        let ty_param_defs: Vec<_> = ty_params.iter().map(|name|
                radium::TyParamNames {param_name: name.clone(), ty_name: format!("{}_ty", name),
                rt_name: format!("{}_rt", name)}).collect();
        let st_params: Vec<String> = ty_params.iter().map(|name|
                format!("{}_st", name)).collect();


        // to account for recursive structs and enable establishing circular references,
        // we first generate a dummy struct (None)
        let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

        let tcx = self.env.tcx();
        let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());
        self.variant_registry.borrow_mut().insert(ty.def_id, (struct_name.clone(), &*struct_def_init, ty, false));

        let struct_name = strip_coq_ident(&ty.ident(tcx).to_string());
        let (variant_def, invariant_def) = self.make_adt_variant(&struct_name, ty, adt, &ty_param_defs, &st_params)?;

        let mut struct_def = radium::AbstractStruct::new(variant_def, ty_param_defs, st_params);
        if let Some(invariant_def) = invariant_def {
            struct_def.add_invariant(invariant_def);
        }

        // TODO for generating the semtype definition, we will also need to track dependencies
        // between structs so that we know when we need recursive types etc.

        // finalize the definition
        {
            let mut struct_def_ref = struct_def_init.borrow_mut();
            *struct_def_ref = Some(struct_def);
        }

        Ok(())
    }

    /// Make an ADT variant.
    /// This assumes that this variant has already been pre-registered to account for recursive
    /// occurrences.
    fn make_adt_variant(&self, struct_name: &str, ty: &'tcx ty::VariantDef, adt: ty::AdtDef, ty_param_defs: &[radium::TyParamNames], st_params: &[String])
            -> Result<(radium::AbstractVariant<'def>, Option<radium::InvariantSpec>), TranslationError>
    {
        info!("adt variant: {:?}", ty);

        let tcx = self.env.tcx();

        // check for representation flags
        let repr = adt.repr();
        let mut repr_opt = radium::StructRepr::ReprRust;
        if repr.c() {
            repr_opt = radium::StructRepr::ReprC;
        }
        else if repr.simd() {
            return Err(TranslationError::UnsupportedFeature { description: "The SIMD flag is currently unsupported".to_string() })
        }
        else if repr.packed() {
            return Err(TranslationError::UnsupportedFeature { description: "The repr(packed) flag is currently unsupported".to_string() })
        }
        else if repr.linear() {
            return Err(TranslationError::UnsupportedFeature { description: "The linear flag is currently unsupported".to_string() })
        }
        else if repr.transparent() {
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
            let res = spec_parser.parse_invariant_spec(&ty_name, &outer_attrs, &ty_param_defs, &lft_params).map_err(|err| {
                TranslationError::FatalError(err)
            })?;
            invariant_spec = Some (res.0);
            expect_refinement = !res.1;
        }
        else {
            invariant_spec = None;
            expect_refinement = false;
        }
        info!("adt variant spec: {:?}", invariant_spec);

        // build a substitution environment that substitutes all the type parameters by literals
        let ty_env: Vec<Option<radium::Type<'def>>> = ty_param_defs.iter().zip(st_params.iter()).map(|(names, st_name)| {
            Some(radium::Type::Literal(Some(names.param_name.clone()),
                radium::CoqAppTerm::new_lhs(names.ty_name.clone()),
                radium::CoqType::Literal(names.rt_name.clone()),
                radium::SynType::Literal(radium::CoqAppTerm::new_lhs(st_name.clone())),
                // TODO: maybe add something here?
                radium::TypeAnnotMeta::empty()))
        }).collect();

        // assemble the field definition
        let mut field_refinements = Vec::new();
        for f in ty.fields.iter() {
            let f_name = f.ident(tcx).to_string();

            let attrs = self.env.get_attributes(f.did);
            let attrs = crate::utils::filter_tool_attrs(attrs);

            let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
            let mut ty = self.translate_type(&f_ty)?;

            // substitute all the type parameters by literals
            ty.subst(&ty_env);

            let mut parser = struct_spec_parser::VerboseStructFieldSpecParser::new(&ty, &ty_param_defs, &lft_params, expect_refinement);
            let field_spec = parser.parse_field_spec(&f_name, &attrs).map_err(|err| {
                TranslationError::UnknownError(err)
            })?;

            info!("adt variant field: {:?} -> {} (with rfn {:?})", f_name, field_spec.ty, field_spec.rfn);
            builder.add_field(&f_name, field_spec.ty);

            if expect_refinement {
                field_refinements.push(field_spec.rfn.unwrap());
            }
        }

        let struct_def = builder.finish(&ty_param_defs, &st_params);
        info!("finished variant def: {:?}", struct_def);

        // now add the invariant, if one was annotated
        if let Some(ref mut invariant_spec) = invariant_spec {
            if expect_refinement {
                // make a plist out of this
                let mut rfn = String::with_capacity(100);
                write!(rfn, "-[").unwrap();
                let mut need_sep = false;
                for refinement in field_refinements.iter() {
                    if need_sep {
                        write!(rfn, "; ").unwrap();
                    }
                    need_sep = true;
                    write!(rfn, "#({})", refinement).unwrap();
                }
                write!(rfn, "]").unwrap();
                invariant_spec.provide_abstracted_refinement(rfn);
            }
        }

        // TODO for generating the semtype definition, we will also need to track dependencies
        // between structs so that we know when we need recursive types etc.

        Ok((struct_def, invariant_spec))
    }

    /// Make a GlobalId for constants (use for discriminants).
    fn make_global_id_for_discr<'a>(&self, did: DefId, env: &'a [ty::GenericArg<'tcx>]) -> rustc_middle::mir::interpret::GlobalId<'tcx> {
        rustc_middle::mir::interpret::GlobalId {
            instance: ty::Instance::new(did, self.env.tcx().mk_args(env)),
            promoted: None
        }
    }

    fn try_scalar_int_to_i128(s: rustc_middle::ty::ScalarInt) -> Option<i128> {
        s.try_to_int(s.size()).ok()
    }

    /// Build a map from discriminant names to their value, if it fits in a i128.
    fn build_discriminant_map(&self, def: ty::AdtDef<'tcx>) -> Result<HashMap<String, i128>, TranslationError> {
        let mut map: HashMap<String, i128> = HashMap::new();
        let variants = def.variants();

        let mut last_explicit_discr: i128 = 0;
        for v in variants.iter() {
            let v: &ty::VariantDef = v;
            let name = v.name.to_string();
            info!("Discriminant for {:?}: {:?}", v, v.discr);
            match v.discr {
                ty::VariantDiscr::Explicit(did) => {
                    // we try to const-evaluate the discriminant
                    let evaluated_discr = self.env.tcx().const_eval_global_id_for_typeck(ty::ParamEnv::empty(),
                                                                   self.make_global_id_for_discr(did, &[]), None)
                        .map_err(|err| TranslationError::FatalError(format!("Failed to const-evaluate discriminant: {:?}", err)))?;
                    let evaluated_discr = evaluated_discr.ok_or(TranslationError::FatalError(format!("Failed to const-evaluate discriminant")))?;

                    let evaluated_int = evaluated_discr.try_to_scalar_int().unwrap();
                    let evaluated_int = Self::try_scalar_int_to_i128(evaluated_int).ok_or(TranslationError::FatalError(format!("Enum discriminant is too large")))?;
                    info!("const-evaluated enum discriminant: {:?}", evaluated_int);

                    last_explicit_discr = evaluated_int;
                    map.insert(name, evaluated_int);
                },
                ty::VariantDiscr::Relative(offset) => {
                    let idx: i128 = last_explicit_discr + (offset as i128);
                    map.insert(name, idx);
                },
            }
        }
        info!("Discriminant map for {:?}: {:?}", def, map);
        Ok(map)
    }

    /// Get the spec for a built-in enum like std::option::Option.
    fn get_builtin_enum_spec(&self, did: DefId) -> Result<Option<radium::EnumSpec>, TranslationError> {
        // TODO: find a more modular way to do this.
        let option_did = crate::utils::try_resolve_did(self.env.tcx(), &["std", "option", "Option"]);
        let option_spec = radium::EnumSpec {
            rfn_type: radium::CoqType::Literal("_".to_string()),
            variant_patterns: vec![("None".to_string(), vec![], "-[]".to_string()),
                                   ("Some".to_string(), vec!["x".to_string()], "-[x]".to_string())],

        };

        if let Some(option_did) = option_did {
            if option_did == did {
                return Ok(Some(option_spec));
            }
        }

        let core_option_did = crate::utils::try_resolve_did(self.env.tcx(), &["core", "option", "Option"]);
        if let Some(option_did) = core_option_did {
            if option_did == did {
                return Ok(Some(option_spec));
            }
        }

        Ok(None)
    }

    /// Register an enum ADT
    fn register_enum(&self, def: ty::AdtDef<'tcx>) -> Result<(), TranslationError> {
        if let Some(_) = self.enum_registry.borrow().get(&def.did()) {
            // already there, that's fine.
            return Ok(())
        }
        info!("Registering enum {:?}", def);

        // pre-register the enum for recursion
        let enum_def_init = self.enum_arena.alloc(RefCell::new(None));

        let tcx = self.env.tcx();

        // TODO: currently a hack, I don't know how to query the name properly
        let enum_name = strip_coq_ident(format!("{:?}", def).as_str());
        self.enum_registry.borrow_mut().insert(def.did(), (enum_name.clone(), &*enum_def_init, def));

        // first thing: figure out the generics we are using here.
        // we need to search all of the variant types for that.
        let mut folder = TyVarFolder::new(self.env.tcx());
        for v in def.variants().iter() {
            for f in v.fields.iter() {
                let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
                f_ty.fold_with(&mut folder);
            }
        }
        let mut used_generics: Vec<ty::ParamTy> = folder.get_result().into_iter().collect();

        // sort according to the index, i.e., the declaration order of the params.
        used_generics.sort();
        let ty_params: Vec<String> = used_generics.iter().map(|param| param.name.to_string()).collect();
        // build names for ty_params
        let ty_param_defs: Vec<_> = ty_params.iter().map(|name|
                radium::TyParamNames {param_name: name.clone(), ty_name: format!("{}_ty", name),
                rt_name: format!("{}_rt", name)}).collect();
        let st_params: Vec<String> = ty_params.iter().map(|name|
                format!("{}_st", name)).collect();

        info!("enum using generics: {:?}", used_generics);

        // now build masks describing which generics each of the variants uses
        // and register the variants
        let mut variant_masks: HashMap<DefId, Vec<bool>> = HashMap::new();
        let mut variant_attrs = Vec::new();
        for v in def.variants().iter() {
            let mut folder = TyVarFolder::new(self.env.tcx());
            for f in v.fields.iter() {
                let f_ty = self.env.tcx().type_of(f.did).instantiate_identity();
                f_ty.fold_with(&mut folder);
            }
            let variant_generics: HashSet<ty::ParamTy> = folder.get_result();

            let mut mask = Vec::new();
            let mut these_param_defs = Vec::new();
            let mut these_st_params = Vec::new();
            for ((param, param_defs), st_param) in used_generics.iter().zip(ty_param_defs.iter()).zip(st_params.iter()) {
                if variant_generics.contains(param) {
                    mask.push(true);
                    these_param_defs.push(param_defs.clone());
                    these_st_params.push(st_param.clone());
                }
                else {
                    mask.push(false);
                }
            }
            variant_masks.insert(v.def_id, mask);

            // now generate the variant
            let struct_def_init = self.struct_arena.alloc(RefCell::new(None));

            let struct_name = strip_coq_ident(format!("{}_{}", enum_name, v.ident(tcx)).as_str());
            self.variant_registry.borrow_mut().insert(v.def_id, (struct_name.clone(), &*struct_def_init, v, true));

            // IMPORTANT: use the full enum's ty_param_defs to account for indexing
            let (variant_def, invariant_def) = self.make_adt_variant(struct_name.as_str(), v, def, &ty_param_defs, &st_params)?;

            // IMPORTANT: use the subset of actually used params for the definition
            let mut struct_def = radium::AbstractStruct::new(variant_def, these_param_defs, these_st_params);
            if let Some(invariant_def) = invariant_def {
                struct_def.add_invariant(invariant_def);
            }

            // also remember the attributes for additional processing
            let outer_attrs = self.env.get_attributes(v.def_id);
            let outer_attrs = crate::utils::filter_tool_attrs(outer_attrs);
            variant_attrs.push(outer_attrs);

            // finalize the definition
            {
                let mut struct_def_ref = struct_def_init.borrow_mut();
                *struct_def_ref = Some(struct_def);
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
        }
        else if repr.simd() {
            return Err(TranslationError::UnsupportedFeature { description: "The SIMD flag is currently unsupported".to_string() })
        }
        else if repr.packed() {
            return Err(TranslationError::UnsupportedFeature { description: "The repr(packed) flag is currently unsupported".to_string() })
        }
        else if repr.linear() {
            return Err(TranslationError::UnsupportedFeature { description: "The linear flag is currently unsupported".to_string() })
        }
        else if repr.transparent() {
            repr_opt = radium::EnumRepr::ReprTransparent;
        }

        // parse annotations for enum type
        let enum_spec;
        let builtin_spec = self.get_builtin_enum_spec(def.did())?;
        if let Some(spec) = builtin_spec {
            enum_spec = spec;
        }
        else {
            let attributes = self.env.get_attributes(def.did());
            let attributes = crate::utils::filter_tool_attrs(attributes);

            // TODO: change once we handle lft parameters properly
            let lft_params: Vec<(Option<String>, radium::Lft)> = Vec::new();

            let mut parser = VerboseEnumSpecParser::new();
            enum_spec = parser.parse_enum_spec("", &attributes, &variant_attrs, &ty_param_defs, &lft_params)
                .map_err(|err| TranslationError::FatalError(err))?;
        }

        let mut enum_builder = radium::EnumBuilder::new(enum_name, ty_param_defs, st_params, translated_it, repr_opt);
        // now build the enum itself
        for v in def.variants().iter() {
            let variant_ref = self.lookup_adt_variant(v.def_id)?;
            let variant_name = strip_coq_ident(&v.ident(tcx).to_string());
            let discriminant = discrs.get(&variant_name).unwrap();
            enum_builder.add_variant(&variant_name, variant_ref, variant_masks.remove(&v.def_id).unwrap(), *discriminant);
        }

        let enum_def = enum_builder.finish(enum_spec);
        // finalize the definition
        {
            let mut enum_def_ref = enum_def_init.borrow_mut();
            *enum_def_ref = Some(enum_def);
        }

        Ok(())
    }

    /// Translate type.
    pub fn translate_type(&self, ty : &Ty<'tcx>) -> Result<radium::Type<'def>, TranslationError> {
        match ty.kind() {
            TyKind::Char => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does not support char".to_string()}),
                //Ok(radium::Layout::CharLayout),
            TyKind::Int(it) => Ok(radium::Type::Int(
                match it {
                    IntTy::I8 => radium::IntType::I8,
                    IntTy::I16 => radium::IntType::I16,
                    IntTy::I32 => radium::IntType::I32,
                    IntTy::I64 => radium::IntType::I64,
                    IntTy::I128 => radium::IntType::I128,
                    IntTy::Isize => radium::IntType::ISize,    // should have same size as pointer types

                })),
            TyKind::Uint(it) => Ok(radium::Type::Int(
                match it {
                    UintTy::U8 => radium::IntType::U8,
                    UintTy::U16 => radium::IntType::U16,
                    UintTy::U32 => radium::IntType::U32,
                    UintTy::U64 => radium::IntType::U64,
                    UintTy::U128 => radium::IntType::U128,
                    UintTy::Usize => radium::IntType::USize,    // should have same size as pointer types

                })),
            TyKind::Bool => Ok(radium::Type::Bool),
            TyKind::Float(_) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does not support float".to_string()}),
            TyKind::Array(_, _) =>
                Err(TranslationError::UnsupportedFeature {description:
                    "Arrays are currently unsupported".to_string()}),
            TyKind::Slice(_) =>
                // TODO this should really be a fat ptr?
                Err(TranslationError::UnsupportedFeature {description:
                    "Slices are currently unsupported".to_string()}),
            TyKind::RawPtr(_) =>
                // just use a dummmy raw ptr type here that has no semantic interpretation, but of which we can get the syntype
                Ok(radium::Type::RawPtr),
                //Ok(radium::Layout::PtrLayout),
            // TODO: this will have to change for handling fat ptrs. see the corresponding rustc
            // def for inspiration.
            TyKind::Ref(region, ty, mutability) => {
                let translated_ty = self.translate_type(ty)?;
                // in case this isn't a universal region, we usually won't care about it.
                let lft = self.translate_region(region).unwrap_or("placeholder_lft".to_string());

                match mutability {
                    rustc_ast::ast::Mutability::Mut =>
                        Ok(radium::Type::MutRef(Box::new(translated_ty), lft)),
                    _ =>
                        Ok(radium::Type::ShrRef(Box::new(translated_ty), lft)),
                }
            },
            TyKind::Never => Ok(radium::Type::Never),
            TyKind::Adt(adt, substs) => {
                if adt.is_box() {
                    // extract the type parameter
                    // the second parameter is the allocator, which we ignore for now
                    assert!(substs.len() == 2);
                    let ty = substs[0].expect_ty();
                    let translated_ty = self.translate_type(&ty)?;
                    Ok(radium::Type::BoxType(Box::new(translated_ty)))
                }
                else if let Some(true) = self.is_struct_definitely_zero_sized(adt.did()) {
                    // make this unit
                    Ok(radium::Type::Unit)
                }
                else {
                    if adt.is_struct() {
                        let su = self.generate_structlike_use(ty, None)?;
                        Ok(radium::Type::Struct(su, radium::TypeIsRaw::No))
                    }
                    else if adt.is_enum() {
                        let eu = self.generate_enum_use(*adt, *substs)?;
                        Ok(radium::Type::Enum(eu))
                    }
                    else {
                        Err(TranslationError::UnsupportedFeature { description: format!("unsupported ADT {:?}", ty) })
                    }
                }
            },
            TyKind::Tuple(params) => {
                if params.len() == 0 {
                    Ok(radium::Type::Unit)
                }
                else {
                    let su = self.generate_tuple_use(params.iter())?;
                    Ok(radium::Type::Struct(su, radium::TypeIsRaw::Yes))
                }
            },
            TyKind::Param(param_ty) => {
                info!("using generic type param: {}", param_ty);
                Ok(radium::Type::Var(param_ty.index as usize))
            },
            TyKind::Foreign(_) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does not support extern types".to_string()}),
            TyKind::Str => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does currently not support str".to_string()}),
            TyKind::FnDef(_, _) => Err(TranslationError::Unimplemented {description:
                "translate_type_to_layout: implement FnDef".to_string()}),
            TyKind::FnPtr(_) => Err(TranslationError::Unimplemented {description:
                "translate_type_to_layout: implement FnPtr".to_string()}),
            TyKind::Dynamic(..) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does currently not trait objects".to_string()}),
            TyKind::Closure(..) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does currently not support closures".to_string()}),
            TyKind::Generator(..) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does currently not support generators".to_string()}),
            TyKind::GeneratorWitness(..) => Err(TranslationError::UnsupportedType {description:
                "RefinedRust does currently not support generators".to_string()}),
            //TyKind::Projection(..) => Err(TranslationError::UnsupportedType {description:
                //"RefinedRust does currently not support associated types".to_string()}),
            //TyKind::Opaque(..) => Err(TranslationError::UnsupportedType {description:
                //"RefinedRust does currently not support returning impls".to_string()}),
            _ => Err(TranslationError::UnsupportedType {description: format!("Unknown unsupported type {}", ty)}),
        }
    }

    /// Translate a rustc_attr::IntType (this is different from the rustc_ty IntType).
    fn translate_int_type(&self, it: rustc_attr::IntType) -> Result<radium::IntType, TranslationError> {
        match it {
            rustc_attr::IntType::SignedInt(it) => {
                Ok(match it {
                   rustc_ast::IntTy::I8 => radium::IntType::I8,
                   rustc_ast::IntTy::I16 => radium::IntType::I16,
                   rustc_ast::IntTy::I32 => radium::IntType::I32,
                   rustc_ast::IntTy::I64 => radium::IntType::I64,
                   rustc_ast::IntTy::I128 => radium::IntType::I128,
                   rustc_ast::IntTy::Isize => radium::IntType::ISize,
                })
            },
            rustc_attr::IntType::UnsignedInt(it) => {
                Ok(match it {
                   rustc_ast::UintTy::U8 => radium::IntType::U8,
                   rustc_ast::UintTy::U16 => radium::IntType::U16,
                   rustc_ast::UintTy::U32 => radium::IntType::U32,
                   rustc_ast::UintTy::U64 => radium::IntType::U64,
                   rustc_ast::UintTy::U128 => radium::IntType::U128,
                   rustc_ast::UintTy::Usize => radium::IntType::USize,
                })
            },
        }
    }

    /// Translate a rustc_attr::IntType (this is different from the rustc_ty IntType).
    fn translate_integer_type(&self, it: rustc_abi::IntegerType) -> Result<radium::IntType, TranslationError> {
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
                }
                else {
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
                }
                else {
                    Ok(radium::IntType::USize)
                }
            },
        }
    }

    /// Translate a MIR type to the Caesium syntactic type we need when storing an element of the type,
    /// substituting all generics.
    pub fn translate_type_to_syn_type(&self, ty: &Ty<'tcx>) -> Result<radium::SynType, TranslationError> {
        // give an environment substituting in the generics
        //let env = &*self.synty_scope.borrow();
        self.translate_type(ty).map(|ty| {
            let mut st = ty.get_syn_type();
            let env = self.synty_scope.borrow();
            st.subst(env.as_ref());
            st
        })
    }

    /// Translates a syntactic type to an op type.
    pub fn translate_syn_type_to_op_type(&self, st: &radium::SynType) -> radium::OpType {
        st.optype(self.synty_scope.borrow().as_ref())
    }

    /// Translates a syntactic type to a layout term.
    pub fn translate_syn_type_to_layout(&self, st: &radium::SynType) -> radium::Layout {
        st.layout_term(self.synty_scope.borrow().as_ref())
    }

    /// Get the name for a field of an ADT or tuple type
    pub fn get_field_name_of(&self, f: &rustc_target::abi::FieldIdx, ty: Ty<'tcx>, variant: Option<usize>) -> Result<String, TranslationError> {
        let tcx = self.env.tcx();
        match ty.kind() {
            TyKind::Adt(def, _) => {
                info!("getting field name of {:?} at {} (variant {:?})", f, ty, variant);
                if def.is_struct() {
                    let i = def.variants().get(rustc_target::abi::VariantIdx::from_usize(0)).unwrap();
                    i.fields.get(*f).map(|f| f.ident(tcx).to_string())
                        .ok_or(TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty)))
                }
                else if def.is_enum() {
                    let variant = variant.unwrap();
                    let i = def.variants().get(rustc_target::abi::VariantIdx::from_usize(variant)).unwrap();
                    i.fields.get(*f).map(|f| f.ident(tcx).to_string())
                        .ok_or(TranslationError::UnknownError(format!("could not get field {:?} of {}", f, ty)))
                }
                else {
                    Err(TranslationError::UnsupportedFeature {description: format!("unsupported field access {:?}to ADT {:?}", f, ty)})
                }
            },
            TyKind::Tuple(_) => {
                Ok(f.index().to_string())
            },
            _ => Err(TranslationError::InvalidLayout),
        }
    }

    /// Get the name of a variant of an enum.
    pub fn get_variant_name_of(&self, ty: Ty<'tcx>, variant: rustc_target::abi::VariantIdx) -> Result<String, TranslationError> {
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


