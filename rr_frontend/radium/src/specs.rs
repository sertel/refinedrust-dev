// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Provides the Spec AST and utilities for interfacing with it.
use std::cell::{OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt::{Formatter, Write};
use std::ops::{Add, Range};
use std::{fmt, mem};

use derive_more::{Constructor, Display};
use indent_write::fmt::IndentWriter;
use itertools::Itertools;
use log::{info, warn};

use crate::{coq, push_str_list, write_list, BASE_INDENT};

#[derive(Clone, PartialEq, Debug)]
/// Encodes a RR type with an accompanying refinement.
pub struct TypeWithRef<'def>(pub Type<'def>, pub String);

impl<'def> Display for TypeWithRef<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} :@: {}", self.1, self.0)
    }
}

impl<'def> TypeWithRef<'def> {
    #[must_use]
    pub const fn new(ty: Type<'def>, rfn: String) -> Self {
        TypeWithRef(ty, rfn)
    }

    #[must_use]
    pub fn make_unit() -> Self {
        TypeWithRef(Type::Unit, "()".to_owned())
    }

    #[must_use]
    pub const fn ty(&self) -> &Type<'def> {
        &self.0
    }

    #[must_use]
    pub fn rfn(&self) -> &str {
        self.1.as_str()
    }
}

pub type Lft = String;

/// A universal lifetime that is not locally owned.
#[derive(Clone, Debug)]
pub enum UniversalLft {
    Function,
    Static,
    Local(Lft),
    External(Lft),
}

impl Display for UniversalLft {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Function => write!(f, "ϝ"),
            Self::Static => write!(f, "static"),
            Self::Local(lft) | Self::External(lft) => write!(f, "{}", lft),
        }
    }
}

/// A lifetime constraint enforces a relation between two external lifetimes.
type ExtLftConstr = (UniversalLft, UniversalLft);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum IntType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    ISize,
    USize,
}

impl Display for IntType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::I8 => write!(f, "I8"),
            Self::I16 => write!(f, "I16"),
            Self::I32 => write!(f, "I32"),
            Self::I64 => write!(f, "I64"),
            Self::I128 => write!(f, "I128"),

            Self::U8 => write!(f, "U8"),
            Self::U16 => write!(f, "U16"),
            Self::U32 => write!(f, "U32"),
            Self::U64 => write!(f, "U64"),
            Self::U128 => write!(f, "U128"),

            Self::ISize => write!(f, "ISize"),
            Self::USize => write!(f, "USize"),
        }
    }
}

impl IntType {
    /// Get the size in bytes of the Caesium representation.
    #[must_use]
    pub const fn size(self) -> u32 {
        match self {
            Self::I8 | Self::U8 => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 => 4,
            Self::I64 | Self::U64 | Self::ISize | Self::USize => 8,
            Self::I128 | Self::U128 => 16,
        }
    }

    /// Get the alignment in bytes of the Caesium representation.
    #[must_use]
    pub const fn alignment(self) -> u32 {
        match self {
            Self::I8 | Self::U8 => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 => 4,
            Self::I64 | Self::U64 | Self::ISize | Self::USize => 8,
            Self::I128 | Self::U128 => 16,
        }
    }
}

/// Representation of Caesium's optypes.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum OpType {
    Int(IntType),
    Bool,
    Char,
    Ptr,
    // a term for the struct_layout, and optypes for the individual fields
    Struct(coq::AppTerm<String, String>, Vec<OpType>),
    Untyped(Layout),
    Literal(coq::AppTerm<String, String>),
}

impl Display for OpType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "BoolOp"),
            Self::Char => write!(f, "CharOp"),
            Self::Int(it) => write!(f, "IntOp {}", it),
            Self::Ptr => write!(f, "PtrOp"),
            Self::Struct(sl, ops) => {
                write!(f, "StructOp {} [", sl)?;
                write_list!(f, ops, "; ")?;
                write!(f, "]")
            },
            Self::Untyped(ly) => write!(f, "UntypedOp ({})", ly),
            Self::Literal(ca) => write!(f, "{}", ca),
        }
    }
}

// NOTE: see ty::layout::layout_of_uncached for the rustc description of this.
pub static BOOL_REPR: IntType = IntType::U8;

/// A syntactic `RefinedRust` type.
/// Every semantic `RefinedRust` type has a corresponding syntactic type that determines its
/// representation in memory.
/// A syntactic type does not necessarily specify a concrete layout. A layout is only fixed once
/// a specific layout algorithm that resolves the non-deterministic choice of the compiler.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum SynType {
    Int(IntType),
    Bool,
    Char,
    Ptr,
    FnPtr,
    Untyped(Layout),
    Unit,
    Never,
    /// a Coq term, in case of generics. This Coq term is required to have type "syn_type".
    Literal(String),
    // no struct or enums - these are specified through literals.
}

impl Display for SynType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "BoolSynType"),
            Self::Char => write!(f, "CharSynType"),
            Self::Int(it) => write!(f, "(IntSynType {})", it),

            Self::Ptr => write!(f, "PtrSynType"),
            Self::FnPtr => write!(f, "FnPtrSynType"),

            Self::Untyped(ly) => write!(f, "(UntypedSynType {})", ly),
            Self::Unit | Self::Never => write!(f, "UnitSynType"),

            Self::Literal(ca) => write!(f, "{}", ca),
        }
    }
}

impl From<SynType> for Layout {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}
impl From<&SynType> for Layout {
    /// Get a Coq term for the layout of this syntactic type.
    /// This may call the Coq-level layout algorithm that we assume.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Untyped(ly) => ly.clone(),
            SynType::Unit | SynType::Never => Self::Unit,

            SynType::Literal(ca) => {
                let rhs = ca.to_owned();
                Self::Literal(coq::AppTerm::new("use_layout_alg'".to_owned(), vec![rhs]))
            },
        }
    }
}

impl From<SynType> for OpType {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}
impl From<&SynType> for OpType {
    /// Determine the optype used to access a value of this syntactic type.
    /// Note that we may also always use `UntypedOp`, but this here computes the more specific
    /// `op_type` that triggers more UB on invalid values.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Untyped(ly) => Self::Untyped(ly.clone()),
            SynType::Unit => Self::Struct(coq::AppTerm::new_lhs("unit_sl".to_owned()), Vec::new()),
            SynType::Never => Self::Untyped(Layout::Unit),

            SynType::Literal(ca) => {
                let rhs = ca.to_owned();
                Self::Literal(coq::AppTerm::new("use_op_alg'".to_owned(), vec![rhs]))
            },
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TypeIsRaw {
    Yes,
    No,
}

/// Meta information from parsing type annotations
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypeAnnotMeta {
    /// Used lifetime variables
    escaped_lfts: HashSet<Lft>,
    /// Used type variables
    escaped_tyvars: HashSet<LiteralTyParam>,
}

impl TypeAnnotMeta {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.escaped_lfts.is_empty() && self.escaped_tyvars.is_empty()
    }

    #[must_use]
    pub fn empty() -> Self {
        Self {
            escaped_lfts: HashSet::new(),
            escaped_tyvars: HashSet::new(),
        }
    }

    #[must_use]
    pub const fn new(tyvars: HashSet<LiteralTyParam>, lfts: HashSet<Lft>) -> Self {
        Self {
            escaped_lfts: lfts,
            escaped_tyvars: tyvars,
        }
    }

    pub fn join(&mut self, s: &Self) {
        let lfts: HashSet<_> = self.escaped_lfts.union(&s.escaped_lfts).cloned().collect();
        let tyvars: HashSet<_> = self.escaped_tyvars.union(&s.escaped_tyvars).cloned().collect();

        self.escaped_lfts = lfts;
        self.escaped_tyvars = tyvars;
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LiteralType {
    /// Rust name
    pub rust_name: Option<String>,
    /// Coq name of the type
    pub type_term: String,
    /// the refinement type
    pub refinement_type: coq::Type,
    /// the syntactic type
    pub syn_type: SynType,
}

pub type LiteralTypeRef<'def> = &'def LiteralType;

#[derive(Clone, PartialEq, Debug)]
pub struct LiteralTypeUse<'def> {
    /// definition
    pub def: LiteralTypeRef<'def>,
    /// parameters
    pub params: Vec<Type<'def>>,
    /// annotation information
    pub annot: TypeAnnotMeta,
}

impl<'def> LiteralTypeUse<'def> {
    #[must_use]
    pub fn new(s: LiteralTypeRef<'def>, params: Vec<Type<'def>>) -> Self {
        LiteralTypeUse {
            def: s,
            params,
            annot: TypeAnnotMeta::empty(),
        }
    }

    #[must_use]
    pub fn new_with_annot(s: LiteralTypeRef<'def>, params: Vec<Type<'def>>, annot: TypeAnnotMeta) -> Self {
        LiteralTypeUse {
            def: s,
            params,
            annot,
        }
    }

    /// Add the lifetimes appearing in this type to `s`.
    pub fn get_ty_lfts(&self, s: &mut HashSet<Lft>) {
        // TODO: use meta
        s.insert(format!("ty_lfts ({})", self.generate_type_term()));
    }

    /// Add the lifetime constraints in this type to `s`.
    pub fn get_ty_wf_elctx(&self, s: &mut HashSet<String>) {
        // TODO: use meta
        s.insert(format!("ty_wf_elctx ({})", self.generate_type_term()));
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    pub fn get_rfn_type(&self) -> String {
        let rfn_instantiations: Vec<String> =
            self.params.iter().map(|ty| ty.get_rfn_type().to_string()).collect();

        let rfn_type = self.def.refinement_type.to_string();
        let applied = coq::AppTerm::new(rfn_type, rfn_instantiations);
        applied.to_string()
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    pub fn generate_raw_syn_type_term(&self) -> SynType {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }
        let specialized_spec = coq::AppTerm::new(self.def.syn_type.clone(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    #[must_use]
    pub fn generate_syn_type_term(&self) -> SynType {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }
        let specialized_spec = coq::AppTerm::new(self.def.syn_type.clone(), param_sts).to_string();
        SynType::Literal(format!("({specialized_spec} : syn_type)"))
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    pub fn generate_type_term(&self) -> String {
        let mut param_tys = Vec::new();
        for p in &self.params {
            param_tys.push(format!("({})", p));
        }
        let specialized_term = coq::AppTerm::new(self.def.type_term.clone(), param_tys);
        specialized_term.to_string()
    }
}

/// The origin of a type parameter.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum TyParamOrigin {
    /// Declared in a surrounding trait declaration.
    SurroundingTrait,
    /// Declared in a surrounding trait impl
    SurroundingImpl,
    /// Associated type of a trait we assume.
    TraitAssoc,
    /// A direct parameter of a method or impl.
    Direct,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct LiteralTyParam {
    /// Rust name
    pub rust_name: String,
    /// Coq name of the type
    pub type_term: String,
    /// the refinement type
    pub refinement_type: String,
    /// the syntactic type
    pub syn_type: String,
    /// the declaration site of this type parameter
    pub origin: TyParamOrigin,
}

impl LiteralTyParam {
    #[must_use]
    pub fn new(rust_name: &str, base: &str) -> Self {
        Self {
            rust_name: rust_name.to_owned(),
            type_term: format!("{base}_ty"),
            refinement_type: format!("{base}_rt"),
            syn_type: format!("{base}_st"),
            origin: TyParamOrigin::Direct,
        }
    }

    #[must_use]
    pub fn new_with_origin(rust_name: &str, base: &str, origin: TyParamOrigin) -> Self {
        let mut x = Self::new(rust_name, base);
        x.origin = origin;
        x
    }

    #[must_use]
    pub fn make_literal_type(&self) -> LiteralType {
        LiteralType {
            rust_name: Some(self.rust_name.clone()),
            type_term: self.type_term.clone(),
            refinement_type: coq::Type::Literal(self.refinement_type.clone()),
            syn_type: SynType::Literal(self.syn_type.clone()),
        }
    }

    #[must_use]
    pub fn make_refinement_param(&self) -> coq::Param {
        coq::Param::new(coq::Name::Named(self.refinement_type.clone()), coq::Type::Type, false)
    }

    #[must_use]
    pub fn make_syntype_param(&self) -> coq::Param {
        coq::Param::new(coq::Name::Named(self.syn_type.clone()), coq::Type::SynType, false)
    }
}

/// Representation of (semantic) `RefinedRust` types.
/// 'def is the lifetime of the frontend for referencing struct definitions.
#[derive(Clone, PartialEq, Debug)]
pub enum Type<'def> {
    Int(IntType),
    Bool,
    Char,
    MutRef(Box<Type<'def>>, Lft),
    ShrRef(Box<Type<'def>>, Lft),
    BoxType(Box<Type<'def>>),
    /// a struct type, potentially instantiated with some type parameters
    /// the boolean indicates
    Struct(AbstractStructUse<'def>),
    /// an enum type, potentially instantiated with some type parameters
    Enum(AbstractEnumUse<'def>),
    /// literal types embedded as strings
    Literal(LiteralTypeUse<'def>),
    /// literal type parameters
    LiteralParam(LiteralTyParam),
    /// the uninit type given to uninitialized values
    Uninit(SynType),
    /// the unit type
    Unit,
    /// the Never type
    Never,
    /// dummy type that should be overridden by an annotation
    RawPtr,
}

impl<'def> Display for Type<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "bool_t"),
            Self::Char => write!(f, "char_t"),
            Self::Int(it) => write!(f, "(int {})", it),

            Self::MutRef(ty, lft) => write!(f, "(mut_ref {} {})", ty, lft),
            Self::ShrRef(ty, lft) => write!(f, "(shr_ref {} {})", ty, lft),
            Self::BoxType(ty) => write!(f, "(box {})", ty),
            Self::RawPtr => write!(f, "alias_ptr_t"),

            Self::Struct(su) => write!(f, "{}", su.generate_type_term()),
            Self::Enum(su) => write!(f, "{}", su.generate_type_term()),

            Self::Literal(lit) => write!(f, "{}", lit.generate_type_term()),
            Self::LiteralParam(p) => write!(f, "{}", p.type_term),

            Self::Uninit(ly) => write!(f, "(uninit ({}))", ly),
            Self::Unit => write!(f, "unit_t"),
            Self::Never => write!(f, "never_t"),
        }
    }
}

impl<'def> From<Type<'def>> for SynType {
    fn from(x: Type<'def>) -> Self {
        Self::from(&x)
    }
}
impl<'def> From<&Type<'def>> for SynType {
    /// Get the layout of a type.
    fn from(x: &Type<'def>) -> Self {
        match x {
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,
            Type::Int(it) => Self::Int(*it),

            Type::MutRef(..) | Type::ShrRef(..) | Type::BoxType(..) | Type::RawPtr => Self::Ptr,

            Type::Struct(s) => s.generate_syn_type_term(),
            Type::Enum(s) => s.generate_syn_type_term(),

            Type::Literal(lit) => lit.generate_syn_type_term(),
            Type::Uninit(st) => st.clone(),

            Type::Unit => Self::Unit,
            // NOTE: for now, just treat Never as a ZST
            Type::Never => Self::Never,

            Type::LiteralParam(lit) => Self::Literal(lit.syn_type.clone()),
        }
    }
}

impl<'def> Type<'def> {
    /// Make the first type in the type tree having an invariant not use the invariant.
    pub fn make_raw(&mut self) {
        match self {
            Self::Struct(su) => su.make_raw(),
            Self::MutRef(box ty, _) | Self::ShrRef(box ty, _) | Self::BoxType(box ty) => ty.make_raw(),
            _ => (),
        }
    }

    /// Determines the type this type is refined by.
    #[must_use]
    pub fn get_rfn_type(&self) -> coq::Type {
        match self {
            Self::Bool => coq::Type::Bool,
            Self::Char | Self::Int(_) => coq::Type::Z,

            Self::MutRef(box ty, _) => {
                coq::Type::Prod(vec![coq::Type::PlaceRfn(Box::new(ty.get_rfn_type())), coq::Type::Gname])
            },

            Self::ShrRef(box ty, _) | Self::BoxType(box ty) => {
                coq::Type::PlaceRfn(Box::new(ty.get_rfn_type()))
            },

            Self::RawPtr => coq::Type::Loc,

            Self::LiteralParam(lit) => coq::Type::Literal(lit.refinement_type.clone()),
            Self::Literal(lit) => coq::Type::Literal(lit.get_rfn_type()),

            Self::Struct(su) => {
                // NOTE: we don't need to subst, due to our invariant that the instantiations for
                // struct uses are already fully substituted
                coq::Type::Literal(su.get_rfn_type())
            },
            Self::Enum(su) => {
                // similar to structs, we don't need to subst
                su.get_rfn_type()
            },

            Self::Unit | Self::Never | Self::Uninit(_) => {
                // NOTE: could also choose to use an uninhabited type for Never
                coq::Type::Unit
            },
        }
    }

    pub fn get_ty_lfts(&self, s: &mut HashSet<Lft>) {
        match self {
            Self::Bool
            | Self::Char
            | Self::Int(_)
            | Self::Uninit(_)
            | Self::Unit
            | Self::Never
            | Self::RawPtr => (),

            Self::MutRef(box ty, lft) | Self::ShrRef(box ty, lft) => {
                s.insert(lft.to_owned());
                ty.get_ty_lfts(s);
            },

            Self::BoxType(box ty) => ty.get_ty_lfts(s),
            Self::Literal(lit) => lit.get_ty_lfts(s),

            Self::Struct(su) => su.get_ty_lfts(s),
            Self::Enum(su) => su.get_ty_lfts(s),

            Self::LiteralParam(lit) => {
                // TODO: use meta
                s.insert(format!("ty_lfts {}", lit.type_term));
            },
        }
    }

    pub fn get_ty_wf_elctx(&self, s: &mut HashSet<String>) {
        match self {
            Self::Bool
            | Self::Char
            | Self::Int(_)
            | Self::Uninit(_)
            | Self::Unit
            | Self::Never
            | Self::RawPtr => (),

            Self::MutRef(box ty, _) | Self::ShrRef(box ty, _) | Self::BoxType(box ty) => {
                ty.get_ty_wf_elctx(s);
            },

            Self::Literal(lit) => lit.get_ty_wf_elctx(s),

            Self::Struct(su) => su.get_ty_wf_elctx(s),
            Self::Enum(su) => su.get_ty_wf_elctx(s),

            Self::LiteralParam(lit) => {
                s.insert(format!("ty_wf_elctx {}", lit.type_term));
            },
        }
    }
}

/// Specification for location ownership of a type.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TyOwnSpec {
    loc: String,
    with_later: bool,
    rfn: String,
    /// type, with generics already fully substituted
    ty: String,
    /// literal lifetimes and types escaped in the annotation parser
    annot_meta: TypeAnnotMeta,
}

impl TyOwnSpec {
    #[must_use]
    pub const fn new(
        loc: String,
        rfn: String,
        ty: String,
        with_later: bool,
        annot_meta: TypeAnnotMeta,
    ) -> Self {
        Self {
            loc,
            with_later,
            rfn,
            ty,
            annot_meta,
        }
    }

    #[must_use]
    pub fn fmt_owned(&self, tid: &str) -> String {
        format!("{} ◁ₗ[{}, Owned {}] #({}) @ (◁ {})", self.loc, tid, self.with_later, self.rfn, self.ty)
    }

    #[must_use]
    pub fn fmt_shared(&self, tid: &str, lft: &str) -> String {
        format!("{} ◁ₗ[{}, Shared {}] #({}) @ (◁ {})", self.loc, tid, lft, self.rfn, self.ty)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum InvariantSpecFlags {
    /// fully persistent and timeless invariant
    Persistent,
    /// invariant with own sharing predicate,
    Plain,
    NonAtomic,
    Atomic,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum InvariantMode {
    All,
    OnlyShared,
    OnlyOwned,
}

#[derive(Clone, PartialEq, Debug)]
pub struct InvariantSpec {
    /// the name of the type definition
    type_name: String,
    flags: InvariantSpecFlags,

    /// name for the sharing lifetime that is used in the invariant specifications
    shr_lft_binder: String,

    /// the refinement type of this struct
    rfn_type: coq::Type,
    /// the binding pattern for the refinement of this type
    rfn_pat: coq::Pattern,

    /// existentials that are introduced in the invariant
    existentials: Vec<(coq::Name, coq::Type)>,

    /// an optional invariant as a separating conjunction,
    invariants: Vec<(IProp, InvariantMode)>,
    /// additional type ownership
    ty_own_invariants: Vec<TyOwnSpec>,

    /// the specification of the abstracted refinement under a context where rfn_pat is bound
    abstracted_refinement: Option<coq::Pattern>,
    // TODO add stuff for non-atomic/atomic invariants
    /// name, type, implicit or not
    coq_params: Vec<coq::Param>,
}

impl InvariantSpec {
    #[must_use]
    pub fn new(
        type_name: String,
        flags: InvariantSpecFlags,
        shr_lft_binder: String,
        rfn_type: coq::Type,
        rfn_pat: coq::Pattern,
        existentials: Vec<(coq::Name, coq::Type)>,
        invariants: Vec<(IProp, InvariantMode)>,
        ty_own_invariants: Vec<TyOwnSpec>,
        abstracted_refinement: Option<coq::Pattern>,
        coq_params: Vec<coq::Param>,
    ) -> Self {
        if flags == InvariantSpecFlags::Persistent {
            assert!(invariants.iter().all(|it| it.1 == InvariantMode::All) && ty_own_invariants.is_empty());
        }

        Self {
            type_name,
            flags,
            shr_lft_binder,
            rfn_type,
            rfn_pat,
            existentials,
            invariants,
            ty_own_invariants,
            abstracted_refinement,
            coq_params,
        }
    }

    /// Add the abstracted refinement, if it was not already provided.
    pub fn provide_abstracted_refinement(&mut self, abstracted_refinement: coq::Pattern) {
        if self.abstracted_refinement.is_some() {
            panic!("abstracted refinement for {} already provided", self.type_name);
        }
        self.abstracted_refinement = Some(abstracted_refinement);
    }

    fn make_existential_binders(&self) -> String {
        if self.existentials.is_empty() {
            return String::new();
        }

        let mut out = String::with_capacity(200);

        out.push_str("∃ ");
        push_str_list!(out, &self.existentials, " ", |(name, ty)| format!("({name} : {ty})"));
        out.push_str(", ");

        out
    }

    /// Assemble the owned invariant predicate for the plain mode.
    fn assemble_plain_owned_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();

        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_owned("π"))).unwrap();
        }

        for (inv, mode) in &self.invariants {
            match mode {
                InvariantMode::All | InvariantMode::OnlyOwned => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the sharing invariant predicate for the plain mode.
    fn assemble_plain_shared_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π {} inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            &self.shr_lft_binder,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_shared("π", &self.shr_lft_binder))).unwrap();
        }
        for (inv, mode) in &self.invariants {
            match mode {
                InvariantMode::All | InvariantMode::OnlyShared => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the list of lifetimes the invariant requires to be alive.
    fn assemble_ty_lfts(&self) -> String {
        let mut out = String::with_capacity(200);

        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_lfts ({}))", ty.type_term).unwrap();
            }
            for lft in &spec.annot_meta.escaped_lfts {
                write!(out, " ++ [{}]", lft).unwrap();
            }
        }

        out
    }

    /// Assemble the lifetime constraints that this type requires.
    fn assemble_ty_wf_elctx(&self) -> String {
        let mut out = String::with_capacity(200);
        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_wf_E ({}))", ty.type_term).unwrap();
            }
        }

        out
    }

    /// Assemble the invariant for the persistent mode.
    fn assemble_pers_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        // TODO: maybe use some other formulation, the destructing let will make the
        // persistence/timeless inference go nuts.
        write!(
            out,
            "λ inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for (inv, _) in &self.invariants {
            write!(out, "{} ∗ ", inv).unwrap();
        }
        write!(out, "True").unwrap();

        out
    }

    /// Generate the Coq definition of the type, without the surrounding context assumptions.
    fn generate_coq_type_def_core(
        &self,
        base_type: &str,
        base_rfn_type: &str,
        generics: &[String],
        context_names: &[String],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate the spec definition
        let spec_name = format!("{}_inv_spec", self.type_name);
        write!(
            out,
            "{indent}Program Definition {} : ex_inv_def ({}) ({}) := ",
            spec_name, base_rfn_type, self.rfn_type
        )
        .unwrap();

        match self.flags {
            InvariantSpecFlags::Persistent => {
                let inv = self.assemble_pers_invariant();
                write!(
                    out,
                    "mk_pers_ex_inv_def\n\
                       {indent}{indent}({})%I _ _\n\
                       {indent}.\n",
                    inv
                )
                .unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_timeless. Qed.\n").unwrap();
            },
            InvariantSpecFlags::Plain => {
                let own_inv = self.assemble_plain_owned_invariant();
                let shr_inv = self.assemble_plain_shared_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    out,
                    "mk_ex_inv_def\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({shr_inv})%I\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}{indent}_ _ _\n\
                    {indent}.\n"
                )
                .unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_plain_t_solve_shr_mono. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_plain_t_solve_shr. Qed.\n").unwrap();
            },
            _ => {
                panic!("unimplemented invariant spec flag: {:?}", self.flags);
            },
        }
        write!(out, "\n").unwrap();

        // generate the definition itself.
        write!(
            out,
            "{indent}Definition {} : type ({}) :=\n\
            {indent}{indent}ex_plain_t _ _ {spec_name} {}.\n",
            self.type_name, self.rfn_type, base_type
        )
        .unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.type_name).unwrap();
        write!(out, "{indent}Definition {}_rt : Type.\n", self.type_name).unwrap();
        write!(
            out,
            "{indent}Proof using {} {}. let __a := eval hnf in (rt_of {}) in exact __a. Defined.\n",
            generics.join(" "),
            context_names.join(" "),
            self.type_name
        )
        .unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}_rt.\n", self.type_name).unwrap();

        out
    }

    /// Generate the definition of the Coq type, including introduction of type parameters to the
    /// context.
    fn generate_coq_type_def(
        &self,
        base_type_name: &str,
        base_rfn_type: &str,
        generic_params: &[LiteralTyParam],
    ) -> String {
        let mut out = String::with_capacity(200);

        assert!(self.abstracted_refinement.is_some());

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.type_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add type parameters
        if !generic_params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in generic_params {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in generic_params {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }

        let (context_names, dep_sigma) = format_extra_context_items(&self.coq_params, &mut out).unwrap();

        // get the applied base_rfn_type
        let rfn_instantiations: Vec<String> =
            generic_params.iter().map(|names| names.refinement_type.clone()).collect();
        let applied_base_rfn_type = coq::AppTerm::new(base_rfn_type, rfn_instantiations.clone());

        // get the applied base type
        let base_type_app: Vec<String> = generic_params.iter().map(|names| names.type_term.clone()).collect();
        let applied_base_type = coq::AppTerm::new(base_type_name, base_type_app);

        write!(
            out,
            "{}",
            self.generate_coq_type_def_core(
                applied_base_type.to_string().as_str(),
                applied_base_rfn_type.to_string().as_str(),
                &rfn_instantiations,
                &context_names
            )
        )
        .unwrap();

        // finish
        write!(out, "End {}.\n", self.type_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.rt_def_name()).unwrap();
        if !context_names.is_empty() {
            let dep_sigma_str = if dep_sigma { "{_} " } else { "" };

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.rt_def_name(),
                dep_sigma_str,
                "_ ".repeat(generic_params.len()),
                "_ ".repeat(context_names.len())
            )
            .unwrap();
        }

        out
    }

    #[must_use]
    pub fn rt_def_name(&self) -> String {
        format!("{}_rt", self.type_name)
    }
}

/// Representation options for structs.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Struct representation options supported by Radium
pub enum StructRepr {
    ReprRust,
    ReprC,
    ReprTransparent,
}

impl Display for StructRepr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReprRust => write!(f, "StructReprRust"),
            Self::ReprC => write!(f, "StructReprC"),
            Self::ReprTransparent => write!(f, "StructReprTransparent"),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Enum representation options supported by Radium
pub enum EnumRepr {
    ReprRust,
    ReprC,
    ReprTransparent,
}

impl Display for EnumRepr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReprRust => write!(f, "EnumReprRust"),
            Self::ReprC => write!(f, "EnumReprC"),
            Self::ReprTransparent => write!(f, "EnumReprTransparent"),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Union representation options supported by Radium
pub enum UnionRepr {
    ReprRust,
    ReprC,
}

impl Display for UnionRepr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReprRust => write!(f, "UnionReprRust"),
            Self::ReprC => write!(f, "UnionReprC"),
        }
    }
}

/// Lookup a Rust-level type parameter identifier `name` in the given type parameter environment.
#[must_use]
pub fn lookup_ty_param<'a>(name: &'_ str, env: &'a [LiteralTyParam]) -> Option<&'a LiteralTyParam> {
    env.iter().find(|&names| names.rust_name == name)
}

/// Description of a variant of a struct or enum.
#[derive(Clone, PartialEq, Debug)]
pub struct AbstractVariant<'def> {
    /// the fields, closed under a surrounding scope
    fields: Vec<(String, Type<'def>)>,
    /// the refinement type of the plain struct
    rfn_type: coq::Type,
    /// the struct representation mode
    repr: StructRepr,
    /// the struct's name
    name: String,
    /// the Coq def name for the struct's plain tydef alias (without the optional invariant wrapper)
    plain_ty_name: String,
    /// the Coq def name for the struct's layout spec definition (of type struct_layout_spec)
    sls_def_name: String,
    st_def_name: String,
    /// the Coq def name for the struct's refinement type
    /// (used for using occurrences, but not for the definition itself)
    plain_rt_def_name: String,
}

impl<'def> AbstractVariant<'def> {
    /// Get the name of this variant
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The core of generating the sls definition, without the section + context intro.
    #[must_use]
    pub fn generate_coq_sls_def_core(&self, typarams: &[String], typarams_use: &[String]) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // intro to main def
        out.push_str(&format!(
            "{indent}Definition {} {} : struct_layout_spec := mk_sls \"{}\" [",
            self.sls_def_name,
            typarams.join(" "),
            self.name
        ));

        push_str_list!(out, &self.fields, ";", |(name, ty)| {
            let synty: SynType = ty.into();

            format!("\n{indent}{indent}(\"{name}\", {synty})")
        });

        out.push_str(&format!("] {}.\n", self.repr));

        // also generate a definition for the syntype
        out.push_str(&format!(
            "{indent}Definition {} {} : syn_type := {} {}.\n",
            self.st_def_name,
            typarams.join(" "),
            self.sls_def_name,
            typarams_use.join(" ")
        ));

        out
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    pub fn generate_coq_sls_def(&self, ty_params: &[LiteralTyParam]) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.sls_def_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let mut typarams = Vec::new();
        let mut typarams_use = Vec::new();
        for names in ty_params {
            typarams.push(format!("({} : syn_type)", names.syn_type));
            typarams_use.push(names.syn_type.clone());
        }
        out.push('\n');

        write!(out, "{}", self.generate_coq_sls_def_core(&typarams, &typarams_use)).unwrap();

        // finish
        write!(out, "End {}.\n", self.sls_def_name).unwrap();
        out
    }

    #[must_use]
    pub fn generate_coq_type_term(&self, sls_app: Vec<String>) -> String {
        let mut out = String::with_capacity(200);

        out.push_str(&format!("struct_t {} +[", coq::AppTerm::new(&self.sls_def_name, sls_app)));
        push_str_list!(out, &self.fields, ";", |(_, ty)| ty.to_string());
        out.push(']');

        out
    }

    #[must_use]
    pub fn generate_coq_type_def_core(
        &self,
        ty_params: &[LiteralTyParam],
        context_names: &[String],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate terms to apply the sls app to
        let mut sls_app = Vec::new();
        for names in ty_params {
            // TODO this is duplicated with the same processing for Type::Literal...
            let term = format!("(ty_syn_type {})", names.type_term);
            sls_app.push(term);
        }

        // intro to main def
        write!(out, "{}Definition {} : type ({}).\n", indent, self.plain_ty_name, self.rfn_type).unwrap();
        write!(
            out,
            "{indent}Proof using {} {}. exact ({}). Defined.\n",
            ty_params.iter().map(|x| x.type_term.clone()).collect::<Vec<_>>().join(" "),
            context_names.join(" "),
            self.generate_coq_type_term(sls_app)
        )
        .unwrap();

        // generate the refinement type definition
        let rt_params: Vec<_> = ty_params.iter().map(|x| x.refinement_type.clone()).collect();
        write!(out, "{indent}Definition {} : Type.\n", self.plain_rt_def_name).unwrap();
        write!(
            out,
            "{indent}Proof using {} {}. let __a := eval hnf in (rt_of {}) in exact __a. Defined.\n",
            rt_params.join(" "),
            context_names.join(" "),
            self.plain_ty_name
        )
        .unwrap();

        // make it Typeclasses Transparent
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.plain_rt_def_name).unwrap();

        out
    }

    /// Generate a Coq definition for the struct type alias.
    /// TODO: maybe we should also generate a separate alias def for the refinement type to make
    /// things more readable?
    #[must_use]
    pub fn generate_coq_type_def(
        &self,
        ty_params: &[LiteralTyParam],
        extra_context: &[coq::Param],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add type parameters, and build a list of terms to apply the sls def to
        if !ty_params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in ty_params {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in ty_params {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push('\n');

        // write coq parameters
        let (context_names, dep_sigma) = format_extra_context_items(extra_context, &mut out).unwrap();
        write!(out, "{}", self.generate_coq_type_def_core(ty_params, &context_names)).unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_def_name).unwrap();
        if !context_names.is_empty() {
            let dep_sigma_str = if dep_sigma { "{_} " } else { "" };

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.plain_rt_def_name,
                dep_sigma_str,
                "_ ".repeat(ty_params.len()),
                "_ ".repeat(extra_context.len())
            )
            .unwrap();
        }
        out
    }
}

fn format_extra_context_items<F>(items: &[coq::Param], f: &mut F) -> Result<(Vec<String>, bool), fmt::Error>
where
    F: Write,
{
    let mut context_names = Vec::new();
    let mut counter = 0;

    let mut depends_on_sigma = false;

    // write coq parameters
    if !items.is_empty() {
        write!(f, "{} (* Additional parameters *)\n", BASE_INDENT)?;
        write!(f, "{}Context ", BASE_INDENT)?;

        for it in items {
            let name = format!("_CTX{}", counter);
            counter += 1;

            write!(f, "{}", it.with_name(name.clone()))?;
            context_names.push(name);
            depends_on_sigma = depends_on_sigma || it.depends_on_sigma;
        }
        write!(f, ".\n")?;
    }
    write!(f, "\n")?;

    Ok((context_names, depends_on_sigma))
}

/// Description of a struct type.
// TODO: mechanisms for resolving mutually recursive types.
#[derive(Clone, PartialEq, Debug)]
pub struct AbstractStruct<'def> {
    /// an optional invariant/ existential abstraction for this struct
    invariant: Option<InvariantSpec>,

    /// the actual definition of the variant
    variant_def: AbstractVariant<'def>,

    /// names for the type parameters (for the Coq definitions)
    /// TODO: will make those options once we handle lifetime parameters properly.
    ty_params: Vec<LiteralTyParam>,
}

pub type AbstractStructRef<'def> = &'def AbstractStruct<'def>;

impl<'def> AbstractStruct<'def> {
    #[must_use]
    pub fn new(variant_def: AbstractVariant<'def>, ty_params: Vec<LiteralTyParam>) -> Self {
        AbstractStruct {
            invariant: None,
            variant_def,
            ty_params,
        }
    }

    /// Check if the struct has type parameters.
    #[must_use]
    pub fn has_type_params(&self) -> bool {
        !self.ty_params.is_empty()
    }

    /// Get the name of this struct
    #[must_use]
    pub fn name(&self) -> &str {
        self.variant_def.name()
    }

    #[must_use]
    pub fn sls_def_name(&self) -> &str {
        &self.variant_def.sls_def_name
    }

    #[must_use]
    pub fn st_def_name(&self) -> &str {
        &self.variant_def.st_def_name
    }

    #[must_use]
    pub fn plain_ty_name(&self) -> &str {
        &self.variant_def.plain_ty_name
    }

    /// Get the name of the struct, or an ADT defined on it, if available.
    #[must_use]
    pub fn public_type_name(&self) -> &str {
        match &self.invariant {
            Some(inv) => &inv.type_name,
            None => self.plain_ty_name(),
        }
    }

    #[must_use]
    pub fn plain_rt_def_name(&self) -> &str {
        &self.variant_def.plain_rt_def_name
    }

    #[must_use]
    pub fn public_rt_def_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.rt_def_name(),
            None => self.plain_rt_def_name().to_owned(),
        }
    }

    /// Add an invariant specification to this type.
    pub fn add_invariant(&mut self, spec: InvariantSpec) {
        if self.invariant.is_some() {
            panic!("already specified an invariant for type {}", self.name());
        }
        self.invariant = Some(spec);
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    pub fn generate_coq_sls_def(&self) -> String {
        self.variant_def.generate_coq_sls_def(&self.ty_params)
    }

    /// Generate a Coq definition for the struct type alias.
    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        let extra_context = if let Some(inv) = &self.invariant { inv.coq_params.as_slice() } else { &[] };

        self.variant_def.generate_coq_type_def(&self.ty_params, extra_context)
    }

    /// Generate an optional definition for the invariant of this type, if one has been specified.
    #[must_use]
    pub fn generate_optional_invariant_def(&self) -> Option<String> {
        self.invariant.as_ref().map(|spec| {
            spec.generate_coq_type_def(self.plain_ty_name(), self.plain_rt_def_name(), &self.ty_params)
        })
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> LiteralType {
        LiteralType {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name().to_owned(),
            refinement_type: coq::Type::Literal(self.public_rt_def_name()),
            syn_type: SynType::Literal(self.sls_def_name().to_owned()),
        }
    }
}

/// A builder for ADT variants without fancy invariants etc.
pub struct VariantBuilder<'def> {
    /// the fields
    fields: Vec<(String, Type<'def>)>,
    /// the variant's representation mode
    repr: StructRepr,
    /// the variants's name
    name: String,
}

impl<'def> VariantBuilder<'def> {
    #[must_use]
    pub fn finish(self) -> AbstractVariant<'def> {
        let sls_def_name: String = format!("{}_sls", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_def_name: String = format!("{}_rt", &self.name);

        let rfn_type = coq::Type::PList(
            "place_rfn".to_owned(),
            self.fields.iter().map(|(_, t)| t.get_rfn_type()).collect(),
        );

        AbstractVariant {
            rfn_type,
            fields: self.fields,
            repr: self.repr,
            name: self.name,
            plain_ty_name,
            sls_def_name,
            st_def_name,
            plain_rt_def_name,
        }
    }

    /// Finish building the struct type and generate an abstract struct definition.
    #[must_use]
    pub fn finish_as_struct(self, ty_params: Vec<LiteralTyParam>) -> AbstractStruct<'def> {
        let variant = self.finish();
        AbstractStruct {
            variant_def: variant,
            invariant: None,
            ty_params,
        }
    }

    /// Initialize a struct builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub fn new(name: String, repr: StructRepr) -> VariantBuilder<'def> {
        VariantBuilder {
            fields: Vec::new(),
            name,
            repr,
        }
    }

    /// Append a field to the struct def.
    pub fn add_field(&mut self, name: &str, ty: Type<'def>) {
        self.fields.push((name.to_owned(), ty));
    }
}

/// Create a struct representation of a tuple with `num_fields`, all of which are generic.
#[must_use]
pub fn make_tuple_struct_repr<'def>(num_fields: usize) -> AbstractStruct<'def> {
    let name = format!("tuple{}", num_fields);

    let mut ty_params = Vec::new();
    for i in 0..num_fields {
        let param_name = format!("T{}", i);
        ty_params.push(param_name);
    }
    let ty_param_defs: Vec<_> = ty_params.iter().map(|name| LiteralTyParam::new(name, name)).collect();

    let mut builder = VariantBuilder::new(name, StructRepr::ReprRust);

    for (i, lit) in ty_param_defs.iter().enumerate() {
        builder.add_field(&i.to_string(), Type::LiteralParam(lit.to_owned()));
    }

    builder.finish_as_struct(ty_param_defs)
}

/// A usage of an `AbstractStruct` that instantiates its type parameters.
#[derive(Clone, PartialEq, Debug)]
pub struct AbstractStructUse<'def> {
    /// reference to the struct's definition, or None if unit
    pub def: Option<&'def AbstractStruct<'def>>,
    /// Instantiations for type parameters
    pub ty_params: Vec<Type<'def>>,
    /// does this refer to the raw type without invariants?
    pub raw: TypeIsRaw,
}

impl<'def> AbstractStructUse<'def> {
    #[must_use]
    pub fn new(s: Option<&'def AbstractStruct<'def>>, params: Vec<Type<'def>>, raw: TypeIsRaw) -> Self {
        AbstractStructUse {
            def: s,
            ty_params: params,
            raw,
        }
    }

    /// Creates a new use of unit.
    #[must_use]
    pub const fn new_unit() -> Self {
        AbstractStructUse {
            def: None,
            ty_params: Vec::new(),
            raw: TypeIsRaw::Yes,
        }
    }

    /// Returns true iff this is a use of unit.
    #[must_use]
    pub const fn is_unit(&self) -> bool {
        self.def.is_none()
    }

    #[must_use]
    pub fn is_raw(&self) -> bool {
        self.raw == TypeIsRaw::Yes
    }

    pub fn make_raw(&mut self) {
        self.raw = TypeIsRaw::Yes;
    }

    /// Add the lifetimes appearing in this type to `s`.
    #[allow(clippy::unused_self)]
    pub fn get_ty_lfts(&self, _s: &mut HashSet<Lft>) {
        // TODO
    }

    /// Add the lifetime constraints in this type to `s`.
    #[allow(clippy::unused_self)]
    pub fn get_ty_wf_elctx(&self, _s: &mut HashSet<String>) {
        // TODO
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    pub fn get_rfn_type(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return coq::Type::Unit.to_string();
        };

        let rfn_instantiations: Vec<String> =
            self.ty_params.iter().map(|ty| ty.get_rfn_type().to_string()).collect();

        let inv = &def.invariant;

        if self.is_raw() || inv.is_none() {
            let rfn_type = def.plain_rt_def_name().to_owned();
            let applied = coq::AppTerm::new(rfn_type, rfn_instantiations);
            applied.to_string()
        } else {
            let rfn_type = inv.as_ref().unwrap().rt_def_name();
            let applied = coq::AppTerm::new(rfn_type, rfn_instantiations);
            applied.to_string()
        }
    }

    /// Generate a term for the `struct_layout` (of type `struct_layout`)
    #[must_use]
    pub fn generate_struct_layout_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return Layout::Unit.to_string();
        };

        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }

        // use_struct_layout_alg' ([my_spec] [params])
        let specialized_spec = format!("({})", coq::AppTerm::new(def.sls_def_name(), param_sts));
        coq::AppTerm::new("use_struct_layout_alg'".to_owned(), vec![specialized_spec]).to_string()
    }

    #[must_use]
    pub fn generate_struct_layout_spec_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            panic!("unit has no sls");
        };

        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }
        // TODO generates too many apps

        // use_struct_layout_alg' ([my_spec] [params])
        format!("({})", coq::AppTerm::new(def.sls_def_name(), param_sts))
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    pub fn generate_syn_type_term(&self) -> SynType {
        let Some(def) = self.def.as_ref() else {
            return SynType::Unit;
        };

        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }
        // TODO generates too many apps

        let specialized_spec = coq::AppTerm::new(def.st_def_name().to_owned(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    pub fn generate_type_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return Type::Unit.to_string();
        };

        let mut param_tys = Vec::new();
        for p in &self.ty_params {
            param_tys.push(format!("({})", p));
        }

        if !self.is_raw() && def.invariant.is_some() {
            let Some(inv) = &def.invariant else {
                unreachable!();
            };

            coq::AppTerm::new(inv.type_name.clone(), param_tys).to_string()
        } else {
            coq::AppTerm::new(def.plain_ty_name(), param_tys).to_string()
        }
    }
}

/// Specification of an enum in terms of a Coq type refining it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EnumSpec {
    /// the refinement type of the enum
    pub rfn_type: coq::Type,
    /// the refinement patterns for each of the variants
    /// eg. for options:
    /// - `(None, [], -[])`
    /// - `(Some, [x], -[x])`
    pub variant_patterns: Vec<(String, Vec<String>, String)>,
}

/// Enum to represent large discriminants
#[derive(Clone, Copy, Display, PartialEq, Debug, Eq)]
pub enum Int128 {
    #[display("{}", _0)]
    Signed(i128),
    #[display("{}", _0)]
    Unsigned(u128),
}
impl Add<u32> for Int128 {
    type Output = Self;

    fn add(self, other: u32) -> Self {
        match self {
            Self::Signed(i) => Self::Signed(i + i128::from(other)),
            Self::Unsigned(i) => Self::Unsigned(i + u128::from(other)),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct AbstractEnum<'def> {
    /// variants of this enum: name, variant, a mask describing which of the type parameters it uses, and the
    /// discriminant
    pub(crate) variants: Vec<(String, Option<&'def AbstractStruct<'def>>, Int128)>,

    /// specification
    spec: EnumSpec,
    /// the enum's name
    name: String,
    /// the representation of the enum
    repr: EnumRepr,

    /// an optional declaration of a Coq inductive for this enum
    optional_inductive_def: Option<coq::Inductive>,

    /// name of the plain enum type (without additional invariants)
    plain_ty_name: String,
    plain_rt_name: String,
    /// name of the enum_layout_spec definition
    els_def_name: String,
    st_def_name: String,
    /// name of the enum definition
    enum_def_name: String,

    /// type of the integer discriminant
    discriminant_type: IntType,

    /// these should be the same also across all the variants
    ty_params: Vec<LiteralTyParam>,
}

pub type AbstractEnumRef<'def> = &'def AbstractEnum<'def>;

impl<'def> AbstractEnum<'def> {
    /// Check whether this enum has any type parameters.
    #[must_use]
    pub fn has_type_params(&self) -> bool {
        !self.ty_params.is_empty()
    }

    /// Get the name of this enum.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub fn public_type_name(&self) -> &str {
        &self.plain_ty_name
    }

    #[must_use]
    pub fn public_rt_def_name(&self) -> &str {
        &self.plain_rt_name
    }

    #[must_use]
    pub fn els_def_name(&self) -> &str {
        &self.els_def_name
    }

    #[must_use]
    pub fn st_def_name(&self) -> &str {
        &self.st_def_name
    }

    #[must_use]
    pub fn get_variant(&self, i: usize) -> Option<&(String, Option<&'def AbstractStruct<'def>>, Int128)> {
        self.variants.get(i)
    }

    /// Generate a Coq definition for the enum layout spec, and all the `struct_layout_specs` for the
    /// variants.
    #[must_use]
    pub fn generate_coq_els_def(&self) -> String {
        let indent = "  ";

        let mut out = String::with_capacity(200);

        out.push_str(&format!("Section {}.\n", self.els_def_name));
        out.push_str(&format!("{indent}Context `{{RRGS : !refinedrustGS Σ}}.\n"));
        out.push('\n');

        // add syntype parameters
        let mut typarams = Vec::new();
        let mut typarams_use = Vec::new();

        if !self.ty_params.is_empty() {
            for names in &self.ty_params {
                typarams.push(format!("({} : syn_type)", names.syn_type));
                typarams_use.push(names.syn_type.clone());
            }
        }

        // generate all the component structs
        for (_, v, _) in &self.variants {
            let vbor = v.unwrap();

            out.push_str(&vbor.variant_def.generate_coq_sls_def_core(&typarams, &typarams_use));
            out.push('\n');
        }

        // intro to main def
        out.push_str(&format!(
            "{indent}Program Definition {} {}: enum_layout_spec := mk_els \"{}\" {} [",
            self.els_def_name,
            typarams.join(" "),
            self.name,
            self.discriminant_type
        ));

        push_str_list!(out, &self.variants, ";", |(name, var, _)| {
            let vbor = var.unwrap();

            format!("\n{}{}(\"{}\", {} {})", indent, indent, name, vbor.st_def_name(), typarams.join(" "))
        });

        // write the repr
        out.push_str(&format!("] {} [", self.repr));

        // now write the tag-discriminant list
        push_str_list!(out, &self.variants, "; ", |(name, _, discr)| format!("(\"{name}\", {discr})"));

        out.push_str("] _ _ _ _.\n");
        out.push_str(&format!("{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. done. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n"));
        out.push_str(&format!(
            "{indent}Next Obligation. repeat first [econstructor | init_cache; solve_goal]. all: unsafe_unfold_common_caesium_defs; simpl; lia. Qed.\n"
        ));
        out.push_str(&format!("{indent}Global Typeclasses Opaque {}.\n", self.els_def_name));

        // also write an st definition
        out.push_str(&format!(
            "{indent}Definition {} {} : syn_type := {} {}.\n",
            self.st_def_name,
            typarams.join(" "),
            self.els_def_name,
            typarams_use.join(" ")
        ));

        // finish
        out.push_str(&format!("End {}.\n", self.els_def_name));

        out
    }

    /// Generate a function that maps the refinement to the tag as a Coq string (`enum_tag`).
    fn generate_enum_tag(&self) -> String {
        let mut out = String::with_capacity(200);

        let spec = &self.spec;
        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((name, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => \"{name}\" ", coq::AppTerm::new(pat, apps.clone())).unwrap();
        }
        write!(out, "end").unwrap();

        out
    }

    /// Generate a function that maps the refinement to the variant type and refinement.
    /// Assumes that the generated code is placed in an environment where all the type parameters
    /// are available and the variant types have been instantiated already.
    fn generate_enum_ty(&self) -> String {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((_name, var, _), (pat, apps, rfn)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            let v = var.unwrap();
            // we can just use the plain name here, because we assume this is used in an
            // environment where all the type parametes are already instantiated.
            let ty = v.public_type_name();

            write!(out, "| {} => existT _ ({ty}, {rfn})", coq::AppTerm::new(pat, apps.clone())).unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps (valid) tags to the corresponding Coq type for the variant.
    fn generate_enum_match(&self) -> String {
        let conditions: Vec<_> = self
            .variants
            .iter()
            .map(|(name, var, _)| {
                let v = var.unwrap();
                let ty = v.public_type_name();

                format!("if (decide (variant = \"{name}\")) then Some $ existT _ {ty}")
            })
            .collect();
        format!("λ variant, {} else None", conditions.join(" else "))
    }

    fn generate_lfts(&self) -> String {
        // TODO: probably should build this up modularly over the fields

        let mut v: Vec<_> = self.ty_params.iter().map(|p| format!("(ty_lfts {})", p.type_term)).collect();
        v.push("[]".to_owned());
        v.join(" ++ ")
    }

    fn generate_wf_elctx(&self) -> String {
        // TODO: probably should build this up modularly over the fields
        let mut v: Vec<_> = self.ty_params.iter().map(|p| format!("(ty_wf_E {})", p.type_term)).collect();
        v.push("[]".to_owned());
        v.join(" ++ ")
    }

    fn generate_construct_enum(&self) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        for ((tag, s, _), (pat, args, res)) in self.variants.iter().zip(self.spec.variant_patterns.iter()) {
            write!(
                out,
                "{indent}Global Program Instance construct_enum_{}_{tag} {} ",
                self.name,
                args.join(" ")
            )
            .unwrap();

            // add st constraints on params
            let mut sls_app = Vec::new();
            for ty in &self.ty_params {
                write!(out, "{} `{{!TCDone ({} = ty_syn_type {})}} ", ty.syn_type, ty.syn_type, ty.type_term)
                    .unwrap();
                sls_app.push(ty.syn_type.clone());
            }
            let s = s.unwrap();
            let ty_def_term = s.variant_def.generate_coq_type_term(sls_app);

            write!(
                out,
                ": ConstructEnum {} \"{}\" ({}) {} {} := construct_enum _ _.\n",
                self.enum_def_name,
                tag,
                ty_def_term,
                res,
                coq::AppTerm::new(pat, args.clone())
            )
            .unwrap();
            write!(out, "{indent}Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.\n").unwrap();
        }

        out
    }

    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add type parameters, and build a list of terms to apply the els def to
        if !self.ty_params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in &self.ty_params {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in &self.ty_params {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push('\n');

        let rt_params: Vec<_> = self.ty_params.iter().map(|x| x.refinement_type.clone()).collect();

        // define types and type abstractions for all the component types.
        // TODO: we should actually use the abstracted types here.
        for (_name, variant, _) in &self.variants {
            let v = variant.unwrap();
            // TODO: might also need to handle extra context items
            write!(out, "{}\n", v.variant_def.generate_coq_type_def_core(&v.ty_params, &[])).unwrap();

            if let Some(inv) = &v.invariant {
                let inv_def = inv.generate_coq_type_def_core(
                    v.variant_def.plain_ty_name.as_str(),
                    v.variant_def.plain_rt_def_name.as_str(),
                    &rt_params,
                    &[],
                );
                write!(out, "{}\n", inv_def).unwrap();
            }
        }

        // write the Coq inductive, if applicable
        if let Some(ind) = &self.optional_inductive_def {
            let mut assertions = coq::TopLevelAssertions::empty();

            assertions.push(coq::TopLevelAssertion::Comment(format!(
                "auto-generated representation of {}",
                ind.name
            )));
            // TODO don't clone
            assertions.push(coq::TopLevelAssertion::InductiveDecl(ind.clone()));
            // prove that it is inhabited
            let instance_decl = coq::InstanceDecl {
                attrs: coq::Attributes::new(vec![coq::Attribute::Global]),
                name: None,
                params: coq::ParamList::new(vec![]),
                ty: coq::Type::Literal(format!("Inhabited {}", ind.name)),
                body: coq::DefBody::Script(
                    coq::ProofScript(vec![coq::ProofItem::Literal("solve_inhabited".to_owned())]),
                    coq::ProofScriptTerminator::Qed,
                ),
            };
            assertions.push(coq::TopLevelAssertion::InstanceDecl(instance_decl));

            let mut code_fmt = IndentWriter::new(BASE_INDENT, &mut out);
            write!(code_fmt, "\n{assertions}\n").unwrap();
        }

        // build the els term applied to generics
        // generate terms to apply the sls app to
        let mut els_app = Vec::new();
        for names in &self.ty_params {
            let term = format!("(ty_syn_type {})", names.type_term);
            els_app.push(term);
        }
        let els_app_term = coq::AppTerm::new(&self.els_def_name, els_app);

        // main def
        write!(
            out,
            "{indent}Program Definition {} : enum ({}) := mk_enum\n\
               {indent}{indent}({els_app_term})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}_ _ _.\n",
            self.enum_def_name,
            self.spec.rfn_type,
            self.generate_enum_tag(),
            self.generate_enum_ty(),
            self.generate_enum_match(),
            self.generate_lfts(),
            self.generate_wf_elctx(),
        )
        .unwrap();
        write!(out, "{indent}Next Obligation. intros []; set_solver. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. intros []; set_solver. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. intros []; naive_solver. Qed.\n\n").unwrap();

        // define the actual type
        write!(out, "{indent}Definition {} : type _ := enum_t {}.\n", self.plain_ty_name, self.enum_def_name)
            .unwrap();

        // generate the refinement type definition
        write!(out, "{indent}Definition {} : Type.\n", self.plain_rt_name).unwrap();
        write!(
            out,
            "{indent}Proof using {}. let __a := eval hnf in (rt_of {}) in exact __a. Defined.\n",
            rt_params.join(" "),
            self.plain_ty_name
        )
        .unwrap();

        // make it Typeclasses Transparent
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}.\n\n", self.plain_rt_name).unwrap();

        write!(out, "{}", self.generate_construct_enum()).unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_name).unwrap();
        write!(out, "Global Hint Unfold {} : solve_protected_eq_db.\n", self.plain_ty_name).unwrap();

        out
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> LiteralType {
        LiteralType {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name().to_owned(),
            refinement_type: coq::Type::Literal(self.public_rt_def_name().to_owned()),
            syn_type: SynType::Literal(self.els_def_name().to_owned()),
        }
    }
}

/// A builder for plain enums without fancy invariants etc.
pub struct EnumBuilder<'def> {
    /// the variants
    variants: Vec<(String, Option<&'def AbstractStruct<'def>>, Int128)>,
    /// the enum's name
    name: String,
    /// names for the type parameters (for the Coq definitions)
    ty_params: Vec<LiteralTyParam>,
    /// type of the integer discriminant
    discriminant_type: IntType,
    /// representation options for the enum
    repr: EnumRepr,
}

impl<'def> EnumBuilder<'def> {
    /// Finish building the enum type and generate an abstract enum definition.
    #[must_use]
    pub fn finish(
        self,
        optional_inductive_def: Option<coq::Inductive>,
        spec: EnumSpec,
    ) -> AbstractEnum<'def> {
        let els_def_name: String = format!("{}_els", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_name: String = format!("{}_rt", &self.name);
        let enum_def_name: String = format!("{}_enum", &self.name);

        AbstractEnum {
            variants: self.variants,
            name: self.name,
            plain_ty_name,
            plain_rt_name,
            els_def_name,
            st_def_name,
            enum_def_name,
            spec,
            optional_inductive_def,
            ty_params: self.ty_params,
            discriminant_type: self.discriminant_type,
            repr: self.repr,
        }
    }

    /// Initialize an enum builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub fn new(
        name: String,
        ty_param_defs: Vec<LiteralTyParam>,
        discriminant_type: IntType,
        repr: EnumRepr,
    ) -> EnumBuilder<'def> {
        EnumBuilder {
            variants: Vec::new(),
            name,
            ty_params: ty_param_defs,
            discriminant_type,
            repr,
        }
    }

    /// Append a variant to the struct def.
    /// `name` is also the Coq constructor of the refinement type we use.
    /// `used_params` is a mask describing which type parameters are used by this variant.
    pub fn add_variant(
        &mut self,
        name: &str,
        variant: Option<&'def AbstractStruct<'def>>,
        discriminant: Int128,
    ) {
        self.variants.push((name.to_owned(), variant, discriminant));
    }
}

/// A usage of an `AbstractEnum` that instantiates its type parameters.
#[derive(Clone, PartialEq, Debug)]
pub struct AbstractEnumUse<'def> {
    /// reference to the enum's definition
    pub def: &'def AbstractEnum<'def>,
    /// Instantiations for type parameters
    pub ty_params: Vec<Type<'def>>,
}

impl<'def> AbstractEnumUse<'def> {
    #[must_use]
    pub fn new(s: &'def AbstractEnum<'def>, params: Vec<Type<'def>>) -> Self {
        AbstractEnumUse {
            def: s,
            ty_params: params,
        }
    }

    /// Add the lifetimes appearing in this type to `s`.
    #[allow(clippy::unused_self)]
    pub fn get_ty_lfts(&self, _s: &mut HashSet<Lft>) {
        // TODO
    }

    /// Add the lifetime constraints in this type to `s`.
    #[allow(clippy::unused_self)]
    pub fn get_ty_wf_elctx(&self, _s: &mut HashSet<String>) {
        // TODO
    }

    /// Get the refinement type of an enum usage.
    /// This requires that all type parameters of the enum have been instantiated.
    #[must_use]
    pub fn get_rfn_type(&self) -> coq::Type {
        self.def.spec.rfn_type.clone()
    }

    /// Generate a term for the enum layout (of type `struct_layout`)
    #[must_use]
    pub fn generate_enum_layout_term(&self) -> String {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }

        // use_struct_layout_alg' ([my_spec] [params])
        let specialized_spec = format!("({})", coq::AppTerm::new(self.def.els_def_name.clone(), param_sts));
        coq::AppTerm::new("use_enum_layout_alg'".to_owned(), vec![specialized_spec]).to_string()
    }

    /// Generate a term for the enum layout spec (of type `enum_layout_spec`).
    #[must_use]
    pub fn generate_enum_layout_spec_term(&self) -> String {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }

        // use_struct_layout_alg' ([my_spec] [params])
        format!("({})", coq::AppTerm::new(self.def.els_def_name.clone(), param_sts))
    }

    /// Get the `syn_type` term for this enum use.
    #[must_use]
    pub fn generate_syn_type_term(&self) -> SynType {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in &self.ty_params {
            let st: SynType = p.into();
            param_sts.push(format!("({})", st));
        }

        // [my_spec] [params]
        let specialized_spec = coq::AppTerm::new(self.def.st_def_name.clone(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this enum use.
    #[must_use]
    pub fn generate_type_term(&self) -> String {
        let mut param_tys = Vec::new();
        for p in &self.ty_params {
            param_tys.push(format!("({})", p));
        }
        let term = coq::AppTerm::new(self.def.plain_ty_name.clone(), param_tys);
        term.to_string()
    }
}

/// Environment that gives concrete layouts to generics and opaque structs
type LayoutEnv = HashMap<String, Layout>;

/// A representation of Caesium layouts we are interested in.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Layout {
    // in the case of  32bits
    Ptr,

    // layout specified by the int type
    Int(IntType),

    // size 1, similar to u8/i8
    Bool,

    // size 4, similar to u32
    Char,

    // guaranteed to have size 0 and alignment 1.
    Unit,

    /// used for variable layout terms, e.g. for struct layouts or generics
    Literal(coq::AppTerm<String, String>),

    /// padding of a given number of bytes
    Pad(u32),
}

impl Display for Layout {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ptr => write!(f, "void*"),
            Self::Int(it) => write!(f, "(it_layout {})", it),
            Self::Bool => write!(f, "bool_layout"),
            Self::Char => write!(f, "char_layout"),
            Self::Unit => write!(f, "(layout_of unit_sl)"),
            Self::Literal(n) => write!(f, "{}", n),
            Self::Pad(s) => write!(f, "(Layout {}%nat 0%nat)", s),
        }
    }
}

impl Layout {
    #[must_use]
    pub fn size(&self, env: &LayoutEnv) -> Option<u32> {
        match self {
            Self::Unit => Some(0),
            Self::Bool => Some(1),
            Self::Char | Self::Ptr => Some(4),
            Self::Int(it) => Some(it.size()),
            Self::Literal(n) => {
                // TODO: this doesn't work if the layout is applied to things.
                match env.get(&n.lhs) {
                    None => None,
                    Some(ly) => ly.size(env),
                }
            },
            //Self::StructLayout(ly) => ly.size(env),
            Self::Pad(s) => Some(*s),
        }
    }

    #[must_use]
    pub fn alignment(&self, env: &LayoutEnv) -> Option<u32> {
        match self {
            Self::Bool | Self::Unit | Self::Pad(_) => Some(1),
            Self::Char | Self::Ptr => Some(4),
            Self::Int(it) => Some(it.alignment()),
            Self::Literal(n) => {
                // TODO: this doesn't work if the layout is applied to things.
                match env.get(&n.lhs) {
                    None => None,
                    Some(ly) => ly.alignment(env),
                }
            },
            //Self::StructLayout(ly) => ly.alignment(env),
        }
    }
}

// better representation of Iprops?
// - in particular for building the existential abstraction, direct support for existentials would be good.
// - DeBruijn probably not worth it, I don't need subst or anything like that. just try to keep variables
//   apart when generating them.

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CoqBinder(coq::Name, coq::Type);
impl CoqBinder {
    #[must_use]
    pub const fn new(n: coq::Name, t: coq::Type) -> Self {
        Self(n, t)
    }
}

impl Display for CoqBinder {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} : {}", self.0, self.1)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum IProp {
    True,
    Atom(String),
    Pure(String),
    // prop, name
    PureWithName(String, String),
    Sep(Vec<IProp>),
    Disj(Vec<IProp>),
    Conj(Vec<IProp>),
    Wand(Box<IProp>, Box<IProp>),
    Exists(Vec<CoqBinder>, Box<IProp>),
    All(Vec<CoqBinder>, Box<IProp>),
}

fn fmt_with_op<T>(v: &[T], op: &str, f: &mut Formatter<'_>) -> Result<(), fmt::Error>
where
    T: Display,
{
    if v.is_empty() {
        return write!(f, "True");
    }

    write_list!(f, v, &format!(" {op} "), "({})")
}

fn fmt_binders(b: &[CoqBinder], op: &str, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "{}", op)?;

    for CoqBinder(id, ty) in b {
        write!(f, " ({} : {})", id, ty)?;
    }
    Ok(())
}

impl Display for IProp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::True => write!(f, "True"),
            Self::Atom(a) => write!(f, "{a}"),
            Self::Pure(a) => write!(f, "⌜{a}⌝"),
            Self::PureWithName(p, name) => write!(f, "⌜name_hint \"{name}\" ({p})⌝"),
            Self::Sep(v) => fmt_with_op(v, "∗", f),
            Self::Disj(v) => fmt_with_op(v, "∨", f),
            Self::Conj(v) => fmt_with_op(v, "∧", f),
            Self::Wand(l, r) => write!(f, "({l}) -∗ {r}"),
            Self::Exists(b, p) => {
                fmt_binders(b, "∃", f)?;
                write!(f, ", {p}")
            },
            Self::All(b, p) => {
                fmt_binders(b, "∀", f)?;
                write!(f, ", {p}")
            },
        }
    }
}

/// Representation of an Iris predicate
#[derive(Clone, Debug)]
pub struct IPropPredicate {
    binders: Vec<CoqBinder>,
    prop: IProp,
}

impl IPropPredicate {
    #[must_use]
    pub fn new(binders: Vec<CoqBinder>, prop: IProp) -> Self {
        Self { binders, prop }
    }
}

impl Display for IPropPredicate {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        fmt_binders(&self.binders, "λ", f)?;
        write!(f, ", {}", self.prop)
    }
}

/// Representation of a loop invariant
#[derive(Clone, Debug)]
pub struct LoopSpec {
    /// the functional invariant as a predicate on the refinement of local variables.
    pub func_predicate: IPropPredicate,
}

/// A finished inner functions specification.
#[derive(Clone, Debug)]
pub enum InnerFunctionSpec<'def> {
    Lit(LiteralFunctionSpec<'def>),
    TraitDefault(InstantiatedTraitFunctionSpec<'def>),
}

impl<'def> InnerFunctionSpec<'def> {
    pub(crate) fn write_spec_term<F>(&self, f: &mut F, scope: &GenericScope<'def>) -> fmt::Result
    where
        F: fmt::Write,
    {
        match self {
            Self::Lit(lit) => lit.write_spec_term(f, scope),
            Self::TraitDefault(def) => def.write_spec_term(f, scope),
        }
    }

    #[must_use]
    pub fn get_params(&self) -> Option<&[(coq::Name, coq::Type)]> {
        match self {
            Self::Lit(lit) => Some(&lit.params),
            Self::TraitDefault(_) => None,
        }
    }

    #[must_use]
    fn needs_trait_req_params(&self) -> bool {
        match self {
            Self::Lit(_) => true,
            Self::TraitDefault(_) => false,
        }
    }
}

/// A Radium function specification.
#[derive(Clone, Debug)]
pub struct FunctionSpec<'def, T> {
    /// The name of the spec
    pub spec_name: String,
    pub function_name: String,

    /// Generics
    pub generics: GenericScope<'def>,

    /// Coq-level parameters the typing statement needs
    early_coq_params: coq::ParamList,
    late_coq_params: coq::ParamList,

    pub spec: T,
}

impl<'def, T> FunctionSpec<'def, T> {
    pub fn replace_spec<U>(self, new_spec: U) -> FunctionSpec<'def, U> {
        FunctionSpec {
            spec: new_spec,
            spec_name: self.spec_name,
            function_name: self.function_name,
            generics: self.generics,
            early_coq_params: self.early_coq_params,
            late_coq_params: self.late_coq_params,
        }
    }

    #[must_use]
    pub fn empty(spec_name: String, function_name: String, spec: T) -> Self {
        Self {
            spec_name,
            function_name,
            generics: GenericScope::empty(),
            early_coq_params: coq::ParamList::empty(),
            late_coq_params: coq::ParamList::empty(),
            spec,
        }
    }

    #[must_use]
    pub const fn new(
        spec_name: String,
        function_name: String,
        generics: GenericScope<'def>,
        early_params: coq::ParamList,
        late_params: coq::ParamList,
        spec: T,
    ) -> Self {
        Self {
            spec_name,
            function_name,
            generics,
            early_coq_params: early_params,
            late_coq_params: late_params,
            spec,
        }
    }

    #[must_use]
    pub fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    pub fn add_early_coq_param(&mut self, param: coq::Param) {
        self.early_coq_params.0.push(param);
    }
    pub fn add_late_coq_param(&mut self, param: coq::Param) {
        self.late_coq_params.0.push(param);
    }
}

impl<'def> FunctionSpec<'def, InnerFunctionSpec<'def>> {
    #[must_use]
    pub fn get_all_coq_params(&self) -> coq::ParamList {
        // Important: early parameters should always be first, as they include trait specs.
        // Important: the type parameters should be introduced before late parameters to ensure they are in
        // scope.
        let mut params = self.early_coq_params.clone();
        params.append(self.generics.get_coq_ty_params().0);
        params.append(self.late_coq_params.0.clone());

        // add trait reqs
        if self.spec.needs_trait_req_params() {
            for trait_use in &self.generics.trait_requirements {
                let spec_params_param_name = trait_use.make_spec_params_param_name();

                let spec_params_type_name = trait_use.trait_ref.spec_params_record.clone();

                let spec_param_name = trait_use.make_spec_param_name();
                let spec_attrs_param_name = trait_use.make_spec_attrs_param_name();
                let spec_type = format!("{} {spec_params_param_name}", trait_use.trait_ref.spec_record);

                // add the attr params
                let all_args: Vec<_> = trait_use
                    .params_inst
                    .iter()
                    .map(Type::get_rfn_type)
                    .chain(trait_use.get_assoc_ty_inst().into_iter().map(|x| x.get_rfn_type()))
                    .collect();
                let mut attr_param = format!("{} ", trait_use.trait_ref.spec_attrs_record);
                push_str_list!(attr_param, &all_args, " ");
                params.0.push(coq::Param::new(
                    coq::Name::Named(spec_attrs_param_name),
                    coq::Type::Literal(attr_param),
                    false,
                ));

                if !trait_use.is_used_in_self_trait {
                    // add the spec params
                    params.0.push(coq::Param::new(
                        coq::Name::Named(spec_params_param_name),
                        coq::Type::Literal(spec_params_type_name),
                        true,
                    ));
                    // add the spec itself
                    params.0.push(coq::Param::new(
                        coq::Name::Named(spec_param_name),
                        coq::Type::Literal(spec_type),
                        false,
                    ));
                }
            }
        }

        params
    }
}

impl<'def> FunctionSpec<'def, InnerFunctionSpec<'def>> {
    /// Check whether this spec is complete.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        match &self.spec {
            InnerFunctionSpec::Lit(lit) => lit.has_spec,
            InnerFunctionSpec::TraitDefault(_) => true,
        }
    }
}

impl<'def> Display for FunctionSpec<'def, InnerFunctionSpec<'def>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let params = self.get_all_coq_params();

        let mut term = String::with_capacity(100);
        self.spec.write_spec_term(&mut term, &self.generics)?;
            //let spec_precond = trait_use.make_spec_param_precond();
            // this should be proved after typarams are instantiated
            //spec_builder.add_late_precondition(spec_precond);


        let coq_def = coq::Definition {
            name: self.spec_name.clone(),
            params,
            ty: None,
            body: coq::DefBody::Term(coq::GallinaTerm::Literal(term)),
            kind: coq::DefinitionKind::Definition,
        };
        write!(f, "{coq_def}")
    }
}

// TODO: separate this into defining and using occurrence.
// extra_link_assum should not be part of a using occurrence.
/// A function specification below generics.
#[derive(Clone, Debug)]
pub struct LiteralFunctionSpec<'def> {
    pub params: Vec<(coq::Name, coq::Type)>,

    /// external lifetime context
    pub elctx: Vec<ExtLftConstr>,
    /// precondition as a separating conjunction
    pub pre: IProp,
    /// argument types including refinements
    pub args: Vec<TypeWithRef<'def>>,
    /// existential quantifiers for the postcondition
    pub existentials: Vec<(coq::Name, coq::Type)>,
    /// return type
    pub ret: TypeWithRef<'def>,
    /// postcondition as a separating conjunction
    pub post: IProp,

    // TODO remove
    pub has_spec: bool,
}

impl<'def> LiteralFunctionSpec<'def> {
    /// Format the external lifetime contexts, consisting of constraints between lifetimes.
    fn format_elctx(&self, scope: &GenericScope<'def>) -> String {
        let mut out = String::with_capacity(100);

        out.push_str("λ ϝ, [");

        // implied bounds on inputs/outputs
        push_str_list!(out, &self.elctx, "; ", |(lft1, lft2)| format!("({lft1}, {lft2})"));

        // all lifetime parameters outlive this function
        if !self.elctx.is_empty() && !scope.lfts.is_empty() {
            out.push_str("; ");
        }
        push_str_list!(out, &scope.lfts, "; ", |lft| format!("(ϝ, {lft})"));

        out.push(']');

        out
    }

    fn format_args(&self) -> String {
        let mut out = String::with_capacity(100);

        push_str_list!(out, &self.args, ", ");

        out
    }

    fn uncurry_typed_binders<'a, F>(v: F) -> (coq::Pattern, coq::Type)
    where
        F: IntoIterator<Item = &'a (coq::Name, coq::Type)>,
    {
        let mut v = v.into_iter().peekable();

        if v.peek().is_none() {
            return ("_".to_owned(), coq::Type::Literal("unit".to_owned()));
        }

        let mut pattern = String::with_capacity(100);
        let mut types = String::with_capacity(100);

        pattern.push('(');
        types.push('(');

        let mut need_sep = false;
        for (name, t) in v {
            if need_sep {
                pattern.push_str(", ");
                types.push_str(" * ");
            }

            pattern.push_str(&name.to_string());
            types.push_str(&t.to_string());

            need_sep = true;
        }

        pattern.push(')');
        types.push(')');

        (pattern, coq::Type::Literal(types))
    }

    /// Write the core spec term. Assumes that the coq parameters for the type parameters (as given by
    /// `get_coq_ty_params`) are in scope.
    pub(crate) fn write_spec_term<F>(&self, f: &mut F, scope: &GenericScope<'def>) -> Result<(), fmt::Error>
    where
        F: fmt::Write,
    {
        /* fn(∀ [lft_pat] : [lft_count] | | [param_pat] : [param_type]; [elctx]; [args]; [pre]; [trait_reqs])
               → ∃ [exist_pat] : [exist_type], [ret_type]; [post]
        */

        let param = Self::uncurry_typed_binders(self.params.iter());

        let existential = Self::uncurry_typed_binders(&self.existentials);

        // introduce generics
        write!(f, "fn(∀ ")?;
        scope.format(f, true, true, &[], &[])?;

        write!(
            f,
            " | {} : {}, ({}); ",
            param.0,
            param.1,
            self.format_elctx(scope).as_str()
        )?;
        if !self.args.is_empty() {
            write!(f, "{}; ", self.format_args().as_str())?;
        }
        write!(f, "(λ π : thread_id, {}) | ", self.pre)?;

        let mut late_pre = Vec::new();
        for trait_use in scope.get_trait_requirements() {
            if !trait_use.is_used_in_self_trait {
                let spec_precond = trait_use.make_spec_param_precond();
                late_pre.push(spec_precond);
            }
        }

        write!(f, "(λ π : thread_id, {}))\n", IProp::Sep(late_pre))?;

        write!(
            f,
            "  → ∃ {} : {}, {} @ {}; (λ π : thread_id, {})",
            existential.0, existential.1, self.ret.1, self.ret.0, self.post
        )?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct LiteralFunctionSpecBuilder<'def> {
    params: Vec<(coq::Name, coq::Type)>,
    elctx: Vec<ExtLftConstr>,
    pre: IProp,
    args: Vec<TypeWithRef<'def>>,
    existential: Vec<(coq::Name, coq::Type)>,
    ret: Option<TypeWithRef<'def>>,
    post: IProp,

    coq_names: HashSet<String>,

    /// true iff there are any annotations
    has_spec: bool,
}

impl<'def> LiteralFunctionSpecBuilder<'def> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            params: Vec::new(),
            elctx: Vec::new(),
            pre: IProp::Sep(Vec::new()),
            args: Vec::new(),
            existential: Vec::new(),
            ret: None,
            post: IProp::Sep(Vec::new()),
            coq_names: HashSet::new(),
            has_spec: false,
        }
    }

    fn push_coq_name(&mut self, name: &coq::Name) {
        if let coq::Name::Named(name) = &name {
            self.coq_names.insert(name.to_owned());
        }
    }

    /// Adds a (universally-quantified) parameter with a given Coq name for the spec.
    pub fn add_param(&mut self, name: coq::Name, t: coq::Type) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.push_coq_name(&name);
        self.params.push((name, t));
        Ok(())
    }

    /// Add a Coq type annotation for a parameter when no type is currently known.
    /// This can e.g. be used to later on add knowledge about the type of a refinement.
    pub fn add_param_type_annot(&mut self, name: &coq::Name, t: coq::Type) -> Result<(), String> {
        for (name0, t0) in &mut self.params {
            if *name0 == *name {
                if *t0 == coq::Type::Infer {
                    *t0 = t;
                }
                return Ok(());
            }
        }
        Err("could not find name".to_owned())
    }

    fn ensure_coq_bound(&self, name: &str) -> Result<(), String> {
        if !self.coq_names.contains(name) {
            return Err(format!("Unbound Coq name {} ", name));
        }

        Ok(())
    }

    fn ensure_coq_not_bound(&self, name: &coq::Name) -> Result<(), String> {
        if let coq::Name::Named(name) = &name {
            if self.coq_names.contains(name) {
                return Err(format!("Coq name is already bound: {}", name));
            }
        }
        Ok(())
    }

    /// Add a new universal lifetime constraint.
    pub fn add_lifetime_constraint(&mut self, lft1: UniversalLft, lft2: UniversalLft) {
        self.elctx.push((lft1, lft2));
    }

    /// Add a new function argument.
    pub fn add_arg(&mut self, arg: TypeWithRef<'def>) {
        self.args.push(arg);
    }

    /// Prepend a precondition. This will be the new precondition to be inserted first.
    /// Use only when the position of the precondition absolutely matters.
    pub fn prepend_precondition(&mut self, pre: IProp) {
        assert!(matches!(self.pre, IProp::Sep(_)));

        let IProp::Sep(v) = &mut self.pre else {
            unreachable!("An incorrect parameter has been given");
        };

        v.insert(0, pre);
    }

    /// Add a new (separating) conjunct to the function's precondition.
    pub fn add_precondition(&mut self, pre: IProp) {
        assert!(matches!(self.pre, IProp::Sep(_)));

        let IProp::Sep(v) = &mut self.pre else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(pre);
    }

    /// Add a new (separating) conjunct to the function's postcondition.
    pub fn add_postcondition(&mut self, post: IProp) {
        assert!(matches!(self.post, IProp::Sep(_)));

        let IProp::Sep(v) = &mut self.post else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(post);
    }

    /// Set the return type of the function
    pub fn set_ret_type(&mut self, ret: TypeWithRef<'def>) -> Result<(), String> {
        if self.ret.is_some() {
            return Err("Re-definition of return type".to_owned());
        }
        self.ret = Some(ret);
        Ok(())
    }

    /// Add an existentially-quantified variable to the postcondition.
    pub fn add_existential(&mut self, name: coq::Name, t: coq::Type) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.existential.push((name, t));
        // TODO: if we add some kind of name analysis to postcondition, we need to handle the
        // existential
        Ok(())
    }

    /// Add the information that attributes have been provided for this function.
    pub fn have_spec(&mut self) {
        self.has_spec = true;
    }

    /// Check whether a valid specification has been added.
    #[must_use]
    pub const fn has_spec(&self) -> bool {
        self.has_spec
    }

    /// Generate an actual function spec.
    pub fn into_function_spec(mut self) -> LiteralFunctionSpec<'def> {
        LiteralFunctionSpec {
            params: self.params,
            elctx: self.elctx,
            pre: self.pre,
            args: self.args,
            existentials: self.existential,
            ret: self.ret.unwrap_or_else(TypeWithRef::make_unit),
            post: self.post,
            has_spec: self.has_spec,
        }
    }
}

/// A specification for a particular instance of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitInstanceSpec<'def> {
    /// a map from the identifiers to the method specs
    pub methods: HashMap<String, &'def FunctionSpec<'def, InnerFunctionSpec<'def>>>,
}

/// Specification attribute declaration of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitSpecAttrsDecl {
    /// a map of attributes and their types
    pub attrs: HashMap<String, coq::Type>,
}

/// Implementation of the attributes of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitSpecAttrsInst {
    /// a map of attributes and their implementation
    pub attrs: HashMap<String, coq::GallinaTerm>,
}

/// A using occurrence of a trait spec.
#[derive(Debug, Clone)]
pub struct LiteralTraitSpec {
    /// Name of the trait
    pub name: String,
    /// Associated types
    pub assoc_tys: Vec<String>,

    /// The name of the Coq definition for the spec param information
    pub spec_params_record: String,
    /// The name of the Coq definition for the spec attributes
    pub spec_attrs_record: String,

    /// The name of the Coq definition for the spec information
    pub spec_record: String,

    /// The basic specification annotated on the trait definition
    /// (Coq def has self, type parameters, as well as associated types)
    pub base_spec: String,
    pub base_spec_params: String,

    /// The subsumption relation between specs
    /// (Coq def has no parameters)
    pub spec_subsumption: String,

    /// declared attributes of the trait
    pub declared_attrs: HashSet<String>,
}
pub type LiteralTraitSpecRef<'def> = &'def LiteralTraitSpec;

impl LiteralTraitSpec {
    /// Make the name for the method spec field of the spec record.
    #[must_use]
    pub fn make_spec_method_name(&self, method: &str) -> String {
        format!("{}_{method}_spec", self.name)
    }

    #[must_use]
    pub fn make_spec_method_params_name(&self, method: &str) -> String {
        format!("{}_{method}_spec_params", self.name)
    }

    #[must_use]
    pub fn make_spec_attr_name(&self, attr: &str) -> String {
        format!("{}_{attr}", self.name)
    }

    #[must_use]
    pub fn spec_record_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_record)
    }

    #[must_use]
    pub fn spec_record_params_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_params_record)
    }

    #[must_use]
    pub fn spec_record_attrs_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_attrs_record)
    }

    #[must_use]
    pub fn spec_incl_name(&self) -> String {
        self.spec_subsumption.clone()
    }

    #[must_use]
    pub fn make_fnspec_attr_param_name(&self) -> String {
        format!("{}_attrs", self.name)
    }
}

/// A reference to a trait instantiated with its parameters in the verification of a function.
#[derive(Debug, Clone)]
pub struct LiteralTraitSpecUse<'def> {
    pub trait_ref: LiteralTraitSpecRef<'def>,
    /// the instantiation for the type parameters (self is at 0)
    pub params_inst: Vec<Type<'def>>,

    /// optionally, an override for the trait specification we assume
    pub overridden_spec_def: Option<String>,

    /// the name including the generic args
    pub mangled_base: String,

    /// whether this is a usage in the scope of a trait decl of the same trait
    pub is_used_in_self_trait: bool,

    /// optional constraints for each associated type
    pub assoc_ty_constraints: HashMap<String, Type<'def>>,
}

impl<'def> LiteralTraitSpecUse<'def> {
    #[must_use]
    pub fn new(
        trait_ref: LiteralTraitSpecRef<'def>,
        params_inst: Vec<Type<'def>>,
        mangled_base: String,
        overridden_spec_def: Option<String>,
        is_used_in_self_trait: bool,
        assoc_ty_constraints: HashMap<String, Type<'def>>,
    ) -> Self {
        Self {
            trait_ref,
            params_inst,
            overridden_spec_def,
            mangled_base,
            is_used_in_self_trait,
            assoc_ty_constraints,
        }
    }

    /// Get the name for a spec parameter for this trait instance.
    #[must_use]
    pub fn make_spec_param_name(&self) -> String {
        format!("{}_spec", self.mangled_base)
    }

    /// Get the name for a spec params parameter for this trait instance.
    #[must_use]
    pub fn make_spec_params_param_name(&self) -> String {
        format!("{}_spec_params", self.mangled_base)
    }

    /// Get the name for a spec attrs parameter for this trait instance.
    #[must_use]
    pub fn make_spec_attrs_param_name(&self) -> String {
        format!("{}_spec_attrs", self.mangled_base)
    }

    /// Get the instantiation of associated types.
    #[must_use]
    pub fn get_assoc_ty_inst(&self) -> Vec<Type<'def>> {
        let mut assoc_tys = Vec::new();
        for x in &self.trait_ref.assoc_tys {
            let ty = self.make_assoc_type_use(x);
            assoc_tys.push(ty.clone());
        }
        assoc_tys
    }

    /// Get the associated types we need to quantify over.
    #[must_use]
    pub fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam> {
        let mut assoc_tys = Vec::new();
        for x in &self.trait_ref.assoc_tys {
            if self.assoc_ty_constraints.get(x).is_none() {
                assoc_tys.push(self.make_assoc_type_lit(x));
            }
        }
        assoc_tys
    }

    /// Make the precondition on the spec parameter we need to require.
    #[must_use]
    pub fn make_spec_param_precond(&self) -> IProp {
        // the spec we have to require for this verification
        let (spec_to_require, need_attrs) = if let Some(override_spec) = &self.overridden_spec_def {
            (override_spec.to_string(), false)
        } else {
            (self.trait_ref.base_spec.clone(), true)
        };

        // the spec gets all the rts, then all sts, then all semtys
        let all_args = self.params_inst.iter().cloned().chain(self.get_assoc_ty_inst()).collect();
        let specialized_spec = SpecializedTraitSpec::new_with_params(
            spec_to_require,
            Some(all_args),
            self.make_spec_attrs_param_name(),
            need_attrs,
        );

        let spec = format!(
            "trait_incl_marker ({} {} {specialized_spec})",
            self.trait_ref.spec_subsumption,
            self.make_spec_param_name(),
        );

        IProp::Pure(spec)
    }

    /// Make the name for the location parameter of a use of a method of this trait parameter.
    #[must_use]
    pub fn make_loc_name(&self, mangled_method_name: &str) -> String {
        format!("{}_{}_loc", self.mangled_base, mangled_method_name)
    }

    /// Make the term for the specification of the given method.
    #[must_use]
    pub fn make_method_spec_term(&self, method_name: &str) -> String {
        format!(
            "(@{} _ RRGS _ {})",
            self.trait_ref.make_spec_method_name(method_name),
            self.make_spec_param_name(),
        )
    }

    /// Make the names for the Coq-level parameters for an associated type of this instance.
    /// Warning: If you are making a using occurrence, use `make_assoc_type_use` instead.
    #[must_use]
    pub fn make_assoc_type_lit(&self, assoc_type: &str) -> LiteralTyParam {
        let rust_name = if self.is_used_in_self_trait {
            assoc_type.to_owned()
        } else {
            format!("{}_{}", self.mangled_base, assoc_type)
        };
        LiteralTyParam::new_with_origin(&rust_name, &rust_name, TyParamOrigin::TraitAssoc)
    }

    /// Check if this associated type is a fully generic parameter.
    #[must_use]
    pub fn is_assoc_type_generic(&self, assoc_type: &str) -> bool {
        self.assoc_ty_constraints.get(assoc_type).is_none()
    }

    /// Add a constraint on one of the associated types.
    pub fn specialize_assoc_type(&mut self, assoc_type: String, ty: Type<'def>) {
        self.assoc_ty_constraints.insert(assoc_type, ty);
    }

    /// Make a using occurrence of a particular associated type.
    #[must_use]
    pub fn make_assoc_type_use(&self, assoc_type: &str) -> Type<'def> {
        if let Some(cstr) = self.assoc_ty_constraints.get(assoc_type) {
            cstr.to_owned()
        } else {
            Type::LiteralParam(self.make_assoc_type_lit(assoc_type))
        }
    }
}

/// A specialized trait specification applied to some type parameters
#[derive(Clone, Debug)]
pub struct SpecializedTraitSpec<'def> {
    pub spec_name: String,
    /// if none, this is already maximally specialized (i.e. from a parameter)
    pub ty_params: Option<Vec<Type<'def>>>,
    /// the specialized spec attribute term
    pub specialized_attr: String,
    pub spec_needs_attr: bool,
}

impl<'def> SpecializedTraitSpec<'def> {
    #[must_use]
    pub const fn new_with_params(
        spec_name: String,
        ty_params: Option<Vec<Type<'def>>>,
        specialized_attr: String,
        spec_needs_attr: bool,
    ) -> Self {
        Self {
            spec_name,
            ty_params,
            specialized_attr,
            spec_needs_attr,
        }
    }
}

impl<'def> Display for SpecializedTraitSpec<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} ", self.spec_name)?;
        if let Some(params) = &self.ty_params {
            // specialize to rts
            write_list!(f, params, " ", |x| { format!("{}", x.get_rfn_type()) })?;
            // specialize to sts
            write!(f, " ")?;
            write_list!(f, params, " ", |x| { format!("{}", SynType::from(x)) })?;
            // specialize to further args
            if self.spec_needs_attr {
                write!(f, " {}", self.specialized_attr)?;
            }
            // specialize to semtys
            write!(f, " ")?;
            write_list!(f, params, " ", |x| { format!("<TY> {}", x) })?;
            write!(f, " <INST!>")?;
        } else if self.spec_needs_attr {
            write!(f, " {}", self.specialized_attr)?;
        }
        write!(f, ")")
    }
}

/// A scope of generics
#[derive(Clone, Debug)]
pub struct GenericScope<'def> {
    tys: Vec<LiteralTyParam>,
    trait_requirements: Vec<LiteralTraitSpecUse<'def>>,
    lfts: Vec<Lft>,
}

impl<'def> GenericScope<'def> {
    /// Create an empty scope.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            tys: Vec::new(),
            trait_requirements: Vec::new(),
            lfts: Vec::new(),
        }
    }

    #[must_use]
    pub fn get_ty_params(&self) -> &[LiteralTyParam] {
        &self.tys
    }

    #[must_use]
    pub fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam> {
        self.trait_requirements.iter().map(|x| x.get_assoc_ty_params()).concat()
    }

    #[must_use]
    pub fn get_all_ty_params(&self) -> Vec<LiteralTyParam> {
        self.get_ty_params().iter().cloned().chain(self.get_assoc_ty_params().into_iter()).collect()
    }

    #[must_use]
    pub fn get_lfts(&self) -> &[Lft] {
        &self.lfts
    }

    #[must_use]
    pub fn get_trait_requirements(&self) -> &[LiteralTraitSpecUse<'def>] {
        &self.trait_requirements
    }

    pub fn add_ty_param(&mut self, ty: LiteralTyParam) {
        self.tys.push(ty);
    }

    pub fn add_lft_param(&mut self, lft: Lft) {
        self.lfts.push(lft);
    }

    pub fn add_trait_requirement(&mut self, req: LiteralTraitSpecUse<'def>) {
        self.trait_requirements.push(req);
    }

    pub fn append(&mut self, other: &Self) {
        for ty in &other.tys {
            self.tys.push(ty.to_owned());
        }
        for lft in &other.lfts {
            self.lfts.push(lft.to_owned());
        }
        for req in &other.trait_requirements {
            self.trait_requirements.push(req.to_owned());
        }
    }

    #[must_use]
    pub fn get_num_lifetimes(&self) -> usize {
        self.lfts.len()
    }

    #[must_use]
    pub fn get_num_ty_params(&self) -> usize {
        self.tys.len()
    }

    /// Format this generic scope.
    pub fn format<F>(
        &self,
        f: &mut F,
        only_core: bool,
        as_fn: bool,
        extra_tys: &[LiteralTyParam],
        extra_lfts: &[Lft],
    ) -> fmt::Result
    where
        F: Write,
    {
        let mut lft_pattern = String::with_capacity(100);
        write!(lft_pattern, "( *[")?;
        write_list!(lft_pattern, self.lfts.iter().chain(extra_lfts), "; ", |x| { format!("{}", x) })?;
        write!(lft_pattern, "])")?;

        let assoc_ty_params = self.get_assoc_ty_params();

        let mut typarams_pattern = String::with_capacity(100);
        write!(typarams_pattern, "( *[")?;
        write_list!(typarams_pattern, self.tys.iter().chain(&assoc_ty_params).chain(extra_tys), "; ", |x| {
            format!("{}", x.type_term)
        })?;
        write!(typarams_pattern, "])")?;

        let mut typarams_ty_list = String::with_capacity(100);
        write!(typarams_ty_list, "[")?;
        write_list!(typarams_ty_list, self.tys.iter().chain(&assoc_ty_params).chain(extra_tys), "; ", |x| {
            if as_fn {
                format!("({}, {})", x.refinement_type, x.syn_type)
            } else {
                format!("{}", x.refinement_type)
            }
        })?;
        write!(typarams_ty_list, "]")?;

        if only_core {
            write!(
                f,
                "{lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list (Type * syn_type)%type)",
                self.lfts.len() + extra_lfts.len()
            )
        } else {
            write!(
                f,
                "spec! {lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list Type),",
                self.lfts.len() + extra_lfts.len()
            )
        }
    }

    /// Get the Coq parameters that need to be in scope for the type parameters of this function.
    #[must_use]
    fn get_coq_ty_params(&self) -> coq::ParamList {
        let assoc_ty_params = self.get_assoc_ty_params();
        let mut ty_coq_params = Vec::new();
        for names in self.tys.iter().chain(&assoc_ty_params) {
            ty_coq_params.push(coq::Param::new(
                coq::Name::Named(names.refinement_type.clone()),
                coq::Type::Type,
                false,
            ));
        }
        for names in self.tys.iter().chain(&assoc_ty_params) {
            ty_coq_params.push(coq::Param::new(
                coq::Name::Named(names.syn_type.clone()),
                coq::Type::SynType,
                false,
            ));
        }
        coq::ParamList(ty_coq_params)
    }

    /// Get the Coq parameters that need to be in scope for the type parameters of this function.
    #[must_use]
    pub fn get_coq_ty_st_params(&self) -> coq::ParamList {
        let assoc_ty_params = self.get_assoc_ty_params();
        let mut ty_coq_params = Vec::new();
        for names in self.tys.iter().chain(&assoc_ty_params) {
            ty_coq_params.push(names.make_syntype_param());
        }
        coq::ParamList::new(ty_coq_params)
    }

    /// Get the direct Coq parameters that need to be in scope for the type parameters of this function.
    #[must_use]
    pub fn get_direct_coq_ty_st_params(&self) -> coq::ParamList {
        let mut ty_coq_params = Vec::new();
        for names in &self.tys {
            if names.origin == TyParamOrigin::Direct {
                ty_coq_params.push(names.make_syntype_param());
            }
        }
        coq::ParamList::new(ty_coq_params)
    }

    #[must_use]
    pub fn get_direct_coq_ty_rt_params(&self) -> coq::ParamList {
        let mut ty_coq_params = Vec::new();
        for names in &self.tys {
            if names.origin == TyParamOrigin::Direct {
                ty_coq_params.push(names.make_refinement_param());
            }
        }
        coq::ParamList::new(ty_coq_params)
    }

    #[must_use]
    pub fn get_direct_coq_ty_params(&self) -> coq::ParamList {
        let mut rt_params = self.get_direct_coq_ty_rt_params();
        let st_params = self.get_direct_coq_ty_st_params();
        rt_params.append(st_params.0);
        rt_params
    }
}

impl<'def> Display for GenericScope<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f, false, false, &[], &[])
    }
}

/// Generate the record instances for a trait impl.
/// - `scope` quantifies the generics of this instance
/// - `assoc_types` has the associated types that we quantify over
/// - `params_inst` is the instantiation of the trait's type parameters
/// - `assoc_inst` is the instantiation of the trait's associated types
/// - `spec` is the specification of all the functions
/// - `of_trait` gives the trait of which we make an instance
/// -
fn make_trait_instance<'def>(
    scope: &GenericScope<'def>,
    assoc_types: &[LiteralTyParam],
    param_inst: &[Type<'def>],
    assoc_inst: &[Type<'def>],
    spec: &TraitInstanceSpec<'def>,
    of_trait: LiteralTraitSpecRef<'def>,
    is_base_spec: bool,
    spec_record_name: &str,
    spec_record_params_name: &str,
) -> Result<coq::TopLevelAssertions, fmt::Error> {
    let mut assertions = Vec::new();

    // write the param record decl
    let mut def_rts_params = Vec::new();
    for param in scope.tys.iter().chain(assoc_types) {
        let rt_param =
            coq::Param::new(coq::Name::Named(param.refinement_type.clone()), coq::Type::Type, false);
        def_rts_params.push(rt_param);
    }
    let def_rts_params = coq::ParamList::new(def_rts_params);
    let def_rts_params_uses = def_rts_params.make_using_terms();

    let param_record_term = if spec.methods.is_empty() {
        coq::GallinaTerm::Literal(of_trait.spec_record_params_constructor_name())
    } else {
        let mut components = Vec::new();
        for (item_name, spec) in &spec.methods {
            let record_item_name = of_trait.make_spec_method_params_name(item_name);

            // we only require the direct Coq type parameters
            let params = spec.generics.get_direct_coq_ty_rt_params();

            let mut body = String::with_capacity(100);
            write!(body, "<get_params_of> {} ", spec.spec_name)?;

            // instantiate with all the refinement types the instance is parametric over
            write_list!(body, &scope.tys, " ", |x| { format!("{}", x.refinement_type) })?;
            write!(body, " ")?;
            // pass the function's own generics
            write_list!(body, &params.0, " ", |x| { x.get_name().unwrap_or("unnamed").to_owned() })?;
            write!(body, " ")?;
            // finally pass the associated types
            write_list!(body, &assoc_types, " ", |x| { format!("{}", x.refinement_type) })?;

            let item = coq::RecordBodyItem {
                name: record_item_name,
                params,
                term: coq::GallinaTerm::Literal(body),
            };
            components.push(item);
        }
        let record_body = coq::RecordBodyTerm { items: components };
        coq::GallinaTerm::RecordBody(record_body)
    };
    let param_record_definition = coq::Definition {
        name: spec_record_params_name.to_owned(),
        params: def_rts_params,
        ty: Some(coq::Type::Literal(of_trait.spec_params_record.clone())),
        body: coq::DefBody::Term(param_record_term),
        kind: coq::DefinitionKind::Definition,
    };
    assertions.push(coq::TopLevelAssertion::Definition(param_record_definition));

    // write the attr record decl, if provided
    let mut attrs_type_rts = Vec::new();
    for param in param_inst.iter().chain(assoc_inst) {
        attrs_type_rts.push(format!("{}", param.get_rfn_type()));
    }
    let attrs_type = coq::AppTerm::new(of_trait.spec_attrs_record.clone(), attrs_type_rts);
    let attrs_type = coq::Type::Literal(format!("{attrs_type}"));

    // write the spec record decl
    let mut def_params = Vec::new();
    // all rts
    for param in scope.tys.iter().chain(assoc_types) {
        let rt_param =
            coq::Param::new(coq::Name::Named(param.refinement_type.clone()), coq::Type::Type, false);
        def_params.push(rt_param);
    }
    // all sts
    for param in scope.tys.iter().chain(assoc_types) {
        let st_param = coq::Param::new(coq::Name::Named(param.syn_type.clone()), coq::Type::SynType, false);
        def_params.push(st_param);
    }
    // then, the attrs. these also get the associated types
    if is_base_spec {
        def_params.push(coq::Param::new(coq::Name::Named("_ATTRS".to_owned()), attrs_type, false));
    }
    let def_params = coq::ParamList::new(def_params);

    // for this, we assume that the semantic type parameters are all in scope
    let body_term = if spec.methods.is_empty() {
        // special-case this, as we cannot use record constructor syntax for empty records
        coq::GallinaTerm::Literal(format!("@{} _", of_trait.spec_record_constructor_name()))
    } else {
        let mut components = Vec::new();
        for (item_name, spec) in &spec.methods {
            let record_item_name = of_trait.make_spec_method_name(item_name);

            let direct_params = spec.generics.get_direct_coq_ty_params();

            let params = spec.generics.get_coq_ty_params();
            let param_uses = params.make_using_terms();

            let mut body = String::with_capacity(100);

            write!(body, "{} ", spec.spec_name)?;
            write_list!(body, &param_uses, " ")?;

            // then the attrs
            if is_base_spec {
                write!(body, " _ATTRS")?;
            }

            // instantiate with the scope's items
            for x in &scope.tys {
                write!(body, " <TY> {}", x.type_term)?;
            }
            for x in &scope.lfts {
                write!(body, " <LFT> {x}")?;
            }
            // instantiate with associated types, making sure to skip over the function's own generics
            let offset = spec.generics.get_direct_coq_ty_rt_params().0.len();
            for x in assoc_types {
                write!(body, " <TY>@{{ {offset} }} {}", x.type_term)?;
            }

            // provide type annotation
            let num_lifetimes = spec.generics.get_num_lifetimes() - scope.lfts.len();
            write!(body, " : (spec_with {num_lifetimes} [")?;
            write_list!(
                body,
                spec.generics.tys.iter().filter(|x| x.origin == TyParamOrigin::Direct),
                "; ",
                |x| x.refinement_type.clone()
            )?;
            write!(body, "] (_ ({spec_record_params_name} ")?;
            write_list!(body, &def_rts_params_uses, " ")?;
            write!(body, ") ")?;
            write_list!(
                body,
                spec.generics.tys.iter().filter(|x| x.origin == TyParamOrigin::Direct),
                " ",
                |_| "_".to_owned()
            )?;
            write!(body, "→ _))")?;

            let item = coq::RecordBodyItem {
                name: record_item_name,
                params: direct_params,
                term: coq::GallinaTerm::Literal(body),
            };
            components.push(item);
        }
        let record_body = coq::RecordBodyTerm { items: components };
        coq::GallinaTerm::RecordBody(record_body)
    };
    // add the surrounding quantifiers over the semantic types
    // TODO
    let mut term_with_specs = String::with_capacity(100);
    scope.format(&mut term_with_specs, false, false, assoc_types, &[])?;
    write!(term_with_specs, " {body_term}")?;

    let mut ty_annot = String::with_capacity(100);
    write!(ty_annot, "spec_with _ _ ({} ({spec_record_params_name} ", of_trait.spec_record)?;
    write_list!(ty_annot, &def_rts_params_uses, " ")?;
    write!(ty_annot, "))")?;

    let definition = coq::Definition {
        name: spec_record_name.to_owned(),
        params: def_params,
        ty: Some(coq::Type::Literal(ty_annot)),
        body: coq::DefBody::Term(coq::GallinaTerm::Literal(term_with_specs)),
        kind: coq::DefinitionKind::Definition,
    };
    assertions.push(coq::TopLevelAssertion::Definition(definition));

    Ok(coq::TopLevelAssertions(assertions))
}

/// When translating a trait declaration, we should generate this, bundling all the components of
/// the trait together.
#[derive(Constructor, Clone, Debug)]
pub struct TraitSpecDecl<'def> {
    /// A reference to all the Coq definition names we should generate.
    pub lit: LiteralTraitSpecRef<'def>,

    /// a list of extra things we assume in the Coq context
    pub extra_coq_context: coq::ParamList,

    /// The generics this trait uses
    pub generics: GenericScope<'def>,

    /// associated types
    pub assoc_types: Vec<LiteralTyParam>,

    /// The default specification from the trait declaration
    pub default_spec: TraitInstanceSpec<'def>,

    /// the spec attributes
    pub attrs: TraitSpecAttrsDecl,
}

impl<'def> Display for TraitSpecDecl<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Section {}.\n", self.lit.name)?;
        write!(f, "Context `{{RRGS : !refinedrustGS Σ}}.\n")?;

        let spec_record_constructor = self.lit.spec_record_constructor_name();
        let spec_param_record_constructor = self.lit.spec_record_params_constructor_name();
        let spec_attrs_record_constructor = self.lit.spec_record_attrs_constructor_name();

        // write spec param record
        let mut record_items = Vec::new();
        for (item_name, item_spec) in &self.default_spec.methods {
            let record_item_name = self.lit.make_spec_method_params_name(item_name);

            // params are the rt of the direct type parameters
            let params = item_spec.generics.get_direct_coq_ty_rt_params();

            let item = coq::RecordDeclItem {
                name: record_item_name,
                params,
                ty: coq::Type::Type,
            };
            record_items.push(item);
        }
        let spec_param_record = coq::Record {
            name: self.lit.spec_params_record.clone(),
            params: coq::ParamList::empty(),
            ty: coq::Type::Type,
            constructor: Some(spec_param_record_constructor),
            body: record_items,
        };
        write!(f, "{spec_param_record}\n")?;

        // write attr record
        let mut record_items = Vec::new();
        for (item_name, item_ty) in &self.attrs.attrs {
            let record_item_name = self.lit.make_spec_attr_name(item_name);

            let item = coq::RecordDeclItem {
                name: record_item_name,
                params: coq::ParamList::empty(),
                ty: item_ty.to_owned(),
            };
            record_items.push(item);
        }
        // this is parametric in the params and associated types
        let mut attr_params = Vec::new();
        for param in self.generics.get_ty_params().iter().chain(self.assoc_types.iter()) {
            attr_params.push(coq::Param::new(
                coq::Name::Named(param.refinement_type.clone()),
                coq::Type::Type,
                true,
            ));
        }
        let spec_attr_record = coq::Record {
            name: self.lit.spec_attrs_record.clone(),
            params: coq::ParamList::new(attr_params),
            ty: coq::Type::Type,
            constructor: Some(spec_attrs_record_constructor.clone()),
            body: record_items,
        };
        write!(f, "{spec_attr_record}\n")?;
        write!(f, "Global Arguments {} : clear implicits.\n", self.lit.spec_attrs_record)?;
        write!(f, "Global Arguments {} ", spec_attrs_record_constructor)?;
        let attr_param_count = self.generics.get_num_ty_params() + self.assoc_types.len();
        for i in 0..attr_param_count {
            write!(f, " {{_}}")?;
        }
        write!(f, ".\n")?;

        // write spec record
        let mut record_items = Vec::new();
        for (item_name, item_spec) in &self.default_spec.methods {
            let record_item_name = self.lit.make_spec_method_name(item_name);
            let record_params_item_name = self.lit.make_spec_method_params_name(item_name);

            // params are the rt and st of the direct type parameters
            let params = item_spec.generics.get_direct_coq_ty_params();

            // get number of lifetime parameters of the function
            let num_lifetimes = item_spec.generics.get_num_lifetimes();

            let rt_param_uses = item_spec.generics.get_direct_coq_ty_rt_params().make_using_terms();
            let mut ty_term = String::with_capacity(100);
            write!(ty_term, "spec_with {num_lifetimes} [")?;
            write_list!(ty_term, &rt_param_uses, "; ")?;
            write!(ty_term, "] (_P.({record_params_item_name}) ")?;
            write_list!(ty_term, &rt_param_uses, " ")?;
            write!(ty_term, " → fn_params)")?;

            let item = coq::RecordDeclItem {
                name: record_item_name,
                params,
                ty: coq::Type::Literal(ty_term),
            };
            record_items.push(item);
        }
        let spec_params = vec![coq::Param::new(
            coq::Name::Named("_P".to_owned()),
            coq::Type::Literal(self.lit.spec_params_record.clone()),
            true,
        )];
        let spec_record = coq::Record {
            name: self.lit.spec_record.clone(),
            params: coq::ParamList::new(spec_params),
            ty: coq::Type::Type,
            constructor: Some(spec_record_constructor),
            body: record_items,
        };
        write!(f, "{spec_record}\n")?;

        // clear the implicit argument
        write!(f, "Global Arguments {} : clear implicits.\n", self.lit.spec_record)?;

        // write spec incl relation
        let spec_incl_name = self.lit.spec_incl_name();
        let spec_param_name1 = "spec1".to_owned();
        let spec_param_name2 = "spec2".to_owned();
        let spec_param_type1 = format!("{} _P1", self.lit.spec_record);
        let spec_param_type2 = format!("{} _P2", self.lit.spec_record);
        let spec_incl_params = vec![
            // the two spec params
            coq::Param::new(
                coq::Name::Named("_P1".to_owned()),
                coq::Type::Literal(self.lit.spec_params_record.clone()),
                true,
            ),
            coq::Param::new(
                coq::Name::Named("_P2".to_owned()),
                coq::Type::Literal(self.lit.spec_params_record.clone()),
                true,
            ),
            // the two actual specs
            coq::Param::new(
                coq::Name::Named(spec_param_name1.clone()),
                coq::Type::Literal(spec_param_type1),
                false,
            ),
            coq::Param::new(
                coq::Name::Named(spec_param_name2.clone()),
                coq::Type::Literal(spec_param_type2),
                false,
            ),
        ];
        let mut incls = Vec::new();
        for (name, decl) in &self.default_spec.methods {
            let param_uses = decl.generics.get_direct_coq_ty_params().make_using_terms();
            let record_item_name = self.lit.make_spec_method_name(name);
            let incl_term = coq::GallinaTerm::All(
                decl.generics.get_direct_coq_ty_params(),
                Box::new(coq::GallinaTerm::App(Box::new(coq::AppTerm::new(
                    coq::GallinaTerm::Literal("function_subtype".to_owned()),
                    vec![
                        coq::GallinaTerm::App(Box::new(coq::AppTerm::new(
                            coq::GallinaTerm::RecordProj(
                                Box::new(coq::GallinaTerm::Literal(spec_param_name1.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.clone(),
                        ))),
                        coq::GallinaTerm::App(Box::new(coq::AppTerm::new(
                            coq::GallinaTerm::RecordProj(
                                Box::new(coq::GallinaTerm::Literal(spec_param_name2.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.clone(),
                        ))),
                    ],
                )))),
            );
            incls.push(incl_term);
        }
        let body = coq::GallinaTerm::Infix("∧".to_owned(), incls);

        let spec_incl_def = coq::Definition {
            name: spec_incl_name,
            params: coq::ParamList::new(spec_incl_params),
            ty: Some(coq::Type::Prop),
            body: coq::DefBody::Term(body),
            kind: coq::DefinitionKind::Definition,
        };
        write!(f, "{spec_incl_def}\n")?;

        // write the individual function specs
        for (item_name, item_spec) in &self.default_spec.methods {
            write!(f, "{item_spec}\n")?;
        }

        // use the identity instantiation of the trait
        let param_inst: Vec<_> =
            self.generics.get_ty_params().iter().map(|x| Type::LiteralParam(x.to_owned())).collect();
        let assoc_inst: Vec<_> = self.assoc_types.iter().map(|x| Type::LiteralParam(x.to_owned())).collect();

        // write the bundled records
        let base_decls = make_trait_instance(
            &self.generics,
            &self.assoc_types,
            &param_inst,
            &assoc_inst,
            &self.default_spec,
            self.lit,
            true,
            &self.lit.base_spec,
            &self.lit.base_spec_params,
        )?;
        write!(f, "{base_decls}\n")?;

        write!(f, "End {}.\n", self.lit.name)
    }
}

/// Coq Names used for the spec of a trait impl.
#[derive(Constructor, Clone, Debug)]
pub struct LiteralTraitImpl {
    /// The name of the record instance for spec information
    pub spec_record: String,
    pub spec_params_record: String,
    pub spec_attrs_record: String,
    /// The name of the proof that the base spec is implied by the more specific spec
    pub spec_subsumption_proof: String,
}
pub type LiteralTraitImplRef<'def> = &'def LiteralTraitImpl;

/// A full instantiation of a trait spec.
#[derive(Constructor, Clone, Debug)]
pub struct TraitRefInst<'def> {
    pub of_trait: LiteralTraitSpecRef<'def>,
    /// type parameters this is generic over
    pub generics: GenericScope<'def>,
    pub lft_inst: Vec<Lft>,
    /// the instantiation for the type parameters (including self)
    pub params_inst: Vec<Type<'def>>,
    /// the implementation of the associated types
    /// NOTE: in the same order as in the trait definition
    pub assoc_types_inst: Vec<Type<'def>>,
    /// the spec attributes
    pub attrs: TraitSpecAttrsInst,
}

impl<'def> TraitRefInst<'def> {
    #[must_use]
    pub fn get_trait_param_inst(&self) -> &[Type<'def>] {
        &self.params_inst
    }

    #[must_use]
    pub fn get_trait_assoc_inst(&self) -> &[Type<'def>] {
        &self.assoc_types_inst
    }
}

/// When translating an impl block, we should generate this, which bundles all components of the
/// implementation together.
#[derive(Constructor, Clone, Debug)]
pub struct TraitImplSpec<'def> {
    /// Coq names to use
    pub names: LiteralTraitImplRef<'def>,

    /// the instantiation of the trait
    pub trait_ref: TraitRefInst<'def>,

    /// the name of the Coq def of the method definition and all type parameters it needs
    pub methods: TraitInstanceSpec<'def>,
}

impl<'def> TraitImplSpec<'def> {
    /// Generate the definition of the attribute record of this trait impl.
    #[must_use]
    pub fn generate_attr_decl(&self) -> coq::TopLevelAssertion {
        let attrs = &self.trait_ref.attrs;
        let attrs_name = &self.names.spec_attrs_record;
        let param_inst = &self.trait_ref.params_inst;
        let assoc_inst = &self.trait_ref.assoc_types_inst;
        let of_trait = &self.trait_ref.of_trait;

        let mut def_rts_params = Vec::new();
        for param in &self.trait_ref.generics.tys {
            let rt_param =
                coq::Param::new(coq::Name::Named(param.refinement_type.clone()), coq::Type::Type, false);
            def_rts_params.push(rt_param);
        }
        let def_rts_params = coq::ParamList::new(def_rts_params);
        let def_rts_params_uses = def_rts_params.make_using_terms();

        // write the attr record decl
        let mut attrs_type_rts = Vec::new();
        for param in param_inst.iter().chain(assoc_inst) {
            attrs_type_rts.push(format!("{}", param.get_rfn_type()));
        }
        let attrs_type = coq::AppTerm::new(of_trait.spec_attrs_record.clone(), attrs_type_rts);
        let attrs_type = coq::Type::Literal(format!("{attrs_type}"));
        let attr_record_term = if attrs.attrs.is_empty() {
            coq::GallinaTerm::Literal(of_trait.spec_record_attrs_constructor_name())
        } else {
            let mut components = Vec::new();
            for (attr_name, inst) in &attrs.attrs {
                let record_item_name = of_trait.make_spec_attr_name(attr_name);

                let item = coq::RecordBodyItem {
                    name: record_item_name,
                    params: coq::ParamList::empty(),
                    term: inst.to_owned(),
                };
                components.push(item);
            }
            let record_body = coq::RecordBodyTerm { items: components };
            coq::GallinaTerm::RecordBody(record_body)
        };
        let attr_record_definition = coq::Definition {
            name: attrs_name.to_owned(),
            params: def_rts_params,
            ty: Some(attrs_type),
            body: coq::DefBody::Term(attr_record_term),
            kind: coq::DefinitionKind::Definition,
        };
        coq::TopLevelAssertion::Definition(attr_record_definition)
    }
    /*
    fn generate_proof(&self) -> coq::TopLevelAssertion {
        let mut params = Vec::new();
        for x in &self.ty_params {
            params.push(coq::Param::new(coq::Name::Named(x.refinement_type.to_owned()), coq::Type::Type, false));
            params.push(coq::Param::new(coq::Name::Named(x.syn_type.to_owned()), coq::Type::SynType, false));
        }

        // TODO: compute the applied spec
        // TODO: does everything with the types work out? do we need the semantic types in scope too?
        //let applied_spec = ;
        let lemma_ty = coq::Type::Literal(
            format!("trait_incl_marker ({} {} {})", self.of_trait.spec_subsumption, applied_spec, self.base_spec_term())
        );

        coq::TopLevelAssertion::Definition(
            coq::Definition {
                kind: coq::DefinitionKind::Lemma,
                name: self.names.spec_subsumption_proof.to_owned(),
                params: coq::ParamList::new(params),
                ty: Some(lemma_ty),
                body: coq::DefBody::Script(
                    coq::ProofScript(vec![coq::ProofItem::Literal("solve_trait_incl".to_owned())]),
                    coq::ProofScriptTerminator::Qed)
        })
    }
    */
}

impl<'def> Display for TraitImplSpec<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This relies on all the impl's functions already having been printed
        write!(f, "{}\n", coq::TopLevelAssertion::SectionStart(self.names.spec_record.clone()))?;
        {
            let mut f = IndentWriter::new(BASE_INDENT, &mut *f);
            write!(f, "{}\n", coq::TopLevelAssertion::ContextDecl(coq::ContextDecl::refinedrust()))?;

            let assoc_types = self.trait_ref.generics.get_assoc_ty_params();

            // write the bundled records
            let base_decls = make_trait_instance(
                &self.trait_ref.generics,
                &assoc_types,
                &self.trait_ref.params_inst,
                &self.trait_ref.assoc_types_inst,
                &self.methods,
                self.trait_ref.of_trait,
                false,
                &self.names.spec_record,
                &self.names.spec_params_record,
            )?;
            write!(f, "{base_decls}\n")?;
        }

        write!(f, "{}\n", coq::TopLevelAssertion::SectionEnd(self.names.spec_record.clone()))
    }
}

/// Function specification that arises from the instantiation of the default spec of a trait.
/// the surrounding `GenericScope` should have:
/// - the instance's generics
/// - the function's generics, marked as direct
#[derive(Clone, Constructor, Debug)]
pub struct InstantiatedTraitFunctionSpec<'def> {
    /// the trait we are instantiating
    trait_ref: TraitRefInst<'def>,
    /// name of the trait method we are instantiating
    trait_method_name: String,
    /// attribute term that we are instantiating with
    trait_attr_term: String,
}

impl<'def> InstantiatedTraitFunctionSpec<'def> {
    fn write_spec_term<F>(&self, f: &mut F, scope: &GenericScope<'def>) -> fmt::Result
    where
        F: fmt::Write,
    {
        // TODO: probably we need to handle the trait requirements in some way here, if the trait
        // extends other traits

        // write the scope
        write!(f, "fnspec!")?;
        self.trait_ref.generics.format(f, true, true, &[], &[])?;
        write!(f, ", ")?;

        // apply the trait's base spec
        let mut params = Vec::new();
        // add rt params
        for ty in &self.trait_ref.params_inst {
            params.push(format!("{}", ty.get_rfn_type()));
        }
        for ty in &self.trait_ref.assoc_types_inst {
            params.push(format!("{}", ty.get_rfn_type()));
        }
        // add syntype params
        for ty in &self.trait_ref.params_inst {
            params.push(format!("{}", SynType::from(ty)));
        }
        for ty in &self.trait_ref.assoc_types_inst {
            params.push(format!("{}", SynType::from(ty)));
        }

        // also instantiate with the attrs that are quantified on the outside
        params.push(self.trait_attr_term.clone());

        let mut applied_base_spec = String::with_capacity(100);
        write!(applied_base_spec, "{}", coq::AppTerm::new(&self.trait_ref.of_trait.base_spec, params))?;
        // instantiate semantic types
        for ty in &self.trait_ref.params_inst {
            write!(applied_base_spec, " <TY> {ty}")?;
        }
        for ty in &self.trait_ref.assoc_types_inst {
            write!(applied_base_spec, " <TY> {ty}")?;
        }
        // instantiate lifetimes
        for lft in &self.trait_ref.lft_inst {
            write!(applied_base_spec, " <LFT> {lft}")?;
        }
        write!(applied_base_spec, " <INST!>")?;

        // now we need to project out the concrete function specification
        // we pass as parameters the rts and sts
        // for that, look in the generic scope for direct parameters
        let mut spec_params = scope.get_direct_coq_ty_rt_params();
        spec_params.append(scope.get_direct_coq_ty_st_params().0);
        let spec_params = spec_params.make_using_terms();

        write!(
            f,
            "({applied_base_spec}).({}) ",
            self.trait_ref.of_trait.make_spec_method_name(&self.trait_method_name)
        )?;
        write_list!(f, &spec_params, " ")?;

        write!(f, " <MERGE!>")?;

        Ok(())
    }
}
