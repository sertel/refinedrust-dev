// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
/// Provides the Spec AST and utilities for interfacing with it.
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter, Write};

use indent_write::fmt::IndentWriter;

pub use crate::coq::*;

#[derive(Clone, Debug, PartialEq)]
/// Encodes a RR type with an accompanying refinement.
pub struct TypeWithRef<'def>(Type<'def>, String);

impl<'def> Display for TypeWithRef<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} @ {}", self.1, self.0)
    }
}

impl<'def> TypeWithRef<'def> {
    pub fn new(ty: Type<'def>, rfn: String) -> Self {
        TypeWithRef(ty, rfn)
    }

    pub fn make_unit() -> Self {
        TypeWithRef(Type::Unit, "()".to_string())
    }

    pub fn ty(&self) -> &Type<'def> {
        &self.0
    }

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
            Self::Local(lft) => write!(f, "{}", lft),
            Self::External(lft) => write!(f, "{}", lft),
        }
    }
}

/// A lifetime constraint enforces a relation between two external lifetimes.
type ExtLftConstr = (UniversalLft, UniversalLft);

#[derive(Hash, Copy, Clone, Debug, Eq, PartialEq)]
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
            IntType::I8 => write!(f, "I8"),
            IntType::I16 => write!(f, "I16"),
            IntType::I32 => write!(f, "I32"),
            IntType::I64 => write!(f, "I64"),
            IntType::I128 => write!(f, "I128"),
            IntType::U8 => write!(f, "U8"),
            IntType::U16 => write!(f, "U16"),
            IntType::U32 => write!(f, "U32"),
            IntType::U64 => write!(f, "U64"),
            IntType::U128 => write!(f, "U128"),
            IntType::ISize => write!(f, "ISize"),
            IntType::USize => write!(f, "USize"),
        }
    }
}

impl IntType {
    /// Get the size in bytes of the Caesium representation.
    pub fn size(&self) -> u32 {
        match self {
            Self::I8 => 1,
            Self::I16 => 2,
            Self::I32 => 4,
            Self::I64 => 8,
            Self::I128 => 16,
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
            Self::U128 => 16,
            Self::USize => 8,
            Self::ISize => 8,
        }
    }

    /// Get the alignment in bytes of the Caesium representation.
    pub fn alignment(&self) -> u32 {
        match self {
            Self::I8 => 1,
            Self::I16 => 2,
            Self::I32 => 4,
            Self::I64 => 8,
            Self::I128 => 16,
            Self::U8 => 1,
            Self::U16 => 2,
            Self::U32 => 4,
            Self::U64 => 8,
            Self::U128 => 16,
            Self::ISize => 8,
            Self::USize => 8,
        }
    }
}

/// Representation of Caesium's optypes.
#[derive(Clone, Debug, PartialEq)]
pub enum OpType {
    IntOp(IntType),
    BoolOp,
    CharOp,
    PtrOp,
    // a term for the struct_layout, and optypes for the individual fields
    StructOp(CoqAppTerm<String>, Vec<OpType>),
    UntypedOp(Layout),
    Literal(CoqAppTerm<String>),
}
impl Display for OpType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::IntOp(it) => write!(f, "IntOp {}", it),
            Self::BoolOp => write!(f, "BoolOp"),
            Self::CharOp => write!(f, "CharOp"),
            Self::PtrOp => write!(f, "PtrOp"),
            Self::StructOp(sl, ops) => {
                write!(f, "StructOp {} [", sl)?;
                let mut need_sep = false;
                for op in ops.iter() {
                    if need_sep {
                        write!(f, "; ")?;
                    }
                    need_sep = true;
                    write!(f, "{}", op)?;
                }
                write!(f, "]")
            },
            Self::UntypedOp(ly) => write!(f, "UntypedOp ({})", ly),
            Self::Literal(ca) => write!(f, "{}", ca),
        }
    }
}

/*
impl From<Layout> for OpType {
    fn from(ly: Layout) -> OpType {
        match ly {
            Layout::PtrLayout => OpType::PtrOp,
            Layout::IntLayout(it) => OpType::IntOp(it),
            Layout::BoolLayout => OpType::IntOp(BOOL_REPR),
            // TODO: handle structs?
            layout  => OpType::UntypedOp(layout),
        }
    }
}
*/

// NOTE: see ty::layout::layout_of_uncached for the rustc description of this.
pub static BOOL_REPR: IntType = IntType::U8;

/// A syntactic RefinedRust type.
/// Every semantic RefinedRust type has a corresponding syntactic type that determines its
/// representation in memory.
/// A syntactic type does not necessarily specify a concrete layout. A layout is only fixed once
/// a specific layout algorithm that resolves the non-deterministic choice of the compiler.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    /// a variable that is bound, e.g., by a surrounding struct def
    Var(usize),
    // no struct or enums - these are specified through literals.
}

impl Display for SynType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(it) => write!(f, "IntSynType {}", it),
            Self::Bool => write!(f, "BoolSynType"),
            Self::Char => write!(f, "CharSynType"),
            Self::Ptr => write!(f, "PtrSynType"),
            Self::FnPtr => write!(f, "FnPtrSynType"),
            Self::Untyped(ly) => write!(f, "UntypedSynType {}", ly),
            Self::Unit => write!(f, "UnitSynType"),
            Self::Never => write!(f, "UnitSynType"),
            Self::Literal(ca) => write!(f, "{}", ca),
            Self::Var(i) => write!(f, "#{}", i),
        }
    }
}

impl SynType {
    fn layout_term_core<F, G>(&self, env: &[Option<F>], to_syntype: G) -> Layout
    where
        G: Fn(&F) -> SynType,
    {
        match self {
            Self::Int(it) => Layout::IntLayout(*it),
            Self::Bool => Layout::BoolLayout,
            Self::Char => Layout::CharLayout,
            Self::Ptr => Layout::PtrLayout,
            Self::FnPtr => Layout::PtrLayout,
            Self::Untyped(ly) => ly.clone(),
            Self::Unit => Layout::UnitLayout,
            Self::Never => Layout::UnitLayout,
            Self::Literal(ca) => {
                let rhs = format!("{}", ca);
                Layout::Literal(CoqAppTerm::new("use_layout_alg'".to_string(), vec![rhs]))
            },
            Self::Var(i) => {
                let a = env.get(*i).unwrap().as_ref().unwrap();
                to_syntype(a).layout_term_core(env, to_syntype)
            },
        }
    }

    /// Get a Coq term for the layout of this syntactic type.
    /// This may call the Coq-level layout algorithm that we assume.
    pub fn layout_term_typaram(&self, env: &[Option<LiteralTyParam>]) -> Layout {
        self.layout_term_core(env, |x| SynType::Literal(x.syn_type.clone()))
    }

    /// See `layout_term_typaram`.
    pub fn layout_term(&self, env: &[Option<SynType>]) -> Layout {
        self.layout_term_core(env, |x| x.clone())
    }

    fn optype_core<F, G>(&self, env: &[Option<F>], to_syntype: G) -> OpType
    where
        G: Fn(&F) -> SynType,
    {
        match self {
            Self::Int(it) => OpType::IntOp(*it),
            Self::Bool => OpType::BoolOp,
            Self::Char => OpType::CharOp,
            Self::Ptr => OpType::PtrOp,
            Self::FnPtr => OpType::PtrOp,
            Self::Untyped(ly) => OpType::UntypedOp(ly.clone()),
            Self::Unit => OpType::StructOp(CoqAppTerm::new_lhs("unit_sl".to_string()), Vec::new()),
            Self::Never => OpType::UntypedOp(Layout::UnitLayout),
            Self::Literal(ca) => {
                let rhs = format!("{}", ca);
                OpType::Literal(CoqAppTerm::new("use_op_alg'".to_string(), vec![rhs]))
            },
            Self::Var(i) => {
                let a = env.get(*i).unwrap().as_ref().unwrap();
                to_syntype(a).optype_core(env, to_syntype)
            },
        }
    }

    /// Determine the optype used to access a value of this syntactic type.
    /// Note that we may also always use UntypedOp, but this here computes the more specific
    /// op_type that triggers more UB on invalid values.
    pub fn optype_typaram<'def>(&self, env: &[Option<LiteralTyParam>]) -> OpType {
        self.optype_core(env, |x| SynType::Literal(x.syn_type.clone()))
    }

    /// See `optype_typaram`.
    pub fn optype(&self, env: &[Option<SynType>]) -> OpType {
        self.optype_core(env, |x| x.clone())
    }

    /// Check if the SynType contains a free variable `Var(i)`.
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Var(_) => false,
            _ => true,
        }
    }

    /// Substitute variables `Var` according to the given substitution (variable `i` is mapped to
    /// index `i` in the vector).
    /// The types in `substi` should not contain variables themselves, as this substitution
    /// operation is capture-incurring!
    pub fn subst(&mut self, substi: &[Option<SynType>]) {
        match self {
            Self::Var(i) => {
                if let Some(Some(ta)) = substi.get(*i) {
                    assert!(ta.is_closed());
                    *self = ta.clone();
                }
            },
            _ => (),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Copy)]
pub enum TypeIsRaw {
    Yes,
    No,
}

/// Meta information from parsing type annotations
#[derive(Clone, Debug, PartialEq)]
pub struct TypeAnnotMeta {
    /// Used lifetime variables
    escaped_lfts: HashSet<Lft>,
    /// Used type variables
    escaped_tyvars: HashSet<LiteralTyParam>,
}

impl TypeAnnotMeta {
    pub fn is_empty(&self) -> bool {
        self.escaped_lfts.is_empty() && self.escaped_tyvars.is_empty()
    }

    pub fn empty() -> TypeAnnotMeta {
        TypeAnnotMeta {
            escaped_lfts: HashSet::new(),
            escaped_tyvars: HashSet::new(),
        }
    }

    pub fn new(tyvars: HashSet<LiteralTyParam>, lfts: HashSet<Lft>) -> Self {
        Self {
            escaped_lfts: lfts,
            escaped_tyvars: tyvars,
        }
    }

    pub fn join(&mut self, s: &TypeAnnotMeta) {
        let lfts: HashSet<_> = self.escaped_lfts.union(&s.escaped_lfts).cloned().collect();
        let tyvars: HashSet<_> = self.escaped_tyvars.union(&s.escaped_tyvars).cloned().collect();

        self.escaped_lfts = lfts;
        self.escaped_tyvars = tyvars;
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LiteralType {
    /// Rust name
    pub rust_name: Option<String>,
    /// Coq name of the type
    pub type_term: String,
    /// the refinement type
    pub refinement_type: CoqType,
    /// the syntactic type
    pub syn_type: SynType,
}

pub type LiteralTypeRef<'def> = &'def LiteralType;

#[derive(Clone, Debug, PartialEq)]
pub struct LiteralTypeUse<'def> {
    /// definition
    pub def: LiteralTypeRef<'def>,
    /// parameters
    pub params: Vec<Type<'def>>,
    /// annotation information
    pub annot: TypeAnnotMeta,
}

impl<'def> LiteralTypeUse<'def> {
    /// `params` should not contain `Var`
    pub fn new(s: LiteralTypeRef<'def>, params: Vec<Type<'def>>) -> Self {
        LiteralTypeUse {
            def: s,
            params,
            annot: TypeAnnotMeta::empty(),
        }
    }

    /// `params` should not contain `Var`
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
    pub fn get_rfn_type(&self) -> String {
        let rfn_instantiations: Vec<String> =
            self.params.iter().map(|ty| ty.get_rfn_type(&[]).to_string()).collect();

        let rfn_type = self.def.refinement_type.to_string();
        let applied = CoqAppTerm::new(rfn_type, rfn_instantiations);
        applied.to_string()
    }

    /// Get the syn_type term for this struct use.
    pub fn generate_syn_type_term(&self) -> SynType {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in self.params.iter() {
            let st = p.get_syn_type();
            param_sts.push(format!("({})", st));
        }
        let specialized_spec = CoqAppTerm::new(self.def.syn_type.clone(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this struct use.
    pub fn generate_type_term(&self) -> String {
        let mut param_tys = Vec::new();
        for p in self.params.iter() {
            param_tys.push(format!("({})", p));
        }
        let specialized_term = CoqAppTerm::new(self.def.type_term.clone(), param_tys);
        specialized_term.to_string()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LiteralTyParam {
    /// Rust name
    pub rust_name: String,
    /// Coq name of the type
    pub type_term: String,
    /// the refinement type
    pub refinement_type: String,
    /// the syntactic type
    pub syn_type: String,
}

/// Representation of (semantic) RefinedRust types.
/// 'def is the lifetime of the frontend for referencing struct definitions.
#[derive(Clone, Debug, PartialEq)]
pub enum Type<'def> {
    /// variable that is bound, e.g., by a surrounding struct definition
    Var(usize),
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
            Self::Int(it) => write!(f, "(int {})", it),
            Self::Bool => write!(f, "bool_t"),
            Self::Char => write!(f, "char_t"),
            Self::MutRef(ty, lft) => {
                write!(f, "(mut_ref {} {})", ty, lft)
            },
            Self::ShrRef(ty, lft) => {
                write!(f, "(shr_ref {} {})", ty, lft)
            },
            Self::BoxType(ty) => {
                write!(f, "(box {})", ty)
            },
            Self::Struct(su) => {
                write!(f, "{}", su.generate_type_term())
            },
            Self::Enum(su) => {
                write!(f, "{}", su.generate_type_term())
            },
            Self::Literal(lit) => {
                write!(f, "{}", lit.generate_type_term())
            },
            Self::LiteralParam(p) => {
                write!(f, "{}", p.type_term)
            },
            Self::Uninit(ly) => {
                write!(f, "(uninit ({}))", ly)
            },
            Self::Unit => write!(f, "unit_t"),
            Self::Var(i) => write!(f, "#{}", i),
            Self::Never => write!(f, "never_t"),
            Self::RawPtr => write!(f, "alias_ptr_t"),
        }
    }
}

impl<'def> Type<'def> {
    /// Make the first type in the type tree having an invariant not use the invariant.
    pub fn make_raw(&mut self) {
        match self {
            Self::Struct(su) => su.make_raw(),
            Self::MutRef(box ty, _) => ty.make_raw(),
            Self::ShrRef(box ty, _) => ty.make_raw(),
            Self::BoxType(box ty) => ty.make_raw(),
            _ => (),
        }
    }

    /// Determines the type this type is refined by.
    /// `env` gives the environment for `Var(i)` constructors.
    pub fn get_rfn_type(&self, env: &[Option<CoqType>]) -> CoqType {
        match self {
            Self::Int(_) => CoqType::Z,
            Self::Bool => CoqType::Bool,
            Self::Char => CoqType::Z,
            Self::MutRef(box ty, _) => {
                CoqType::Prod(vec![CoqType::PlaceRfn(Box::new(ty.get_rfn_type(env))), CoqType::Gname])
            },
            Self::ShrRef(box ty, _) => CoqType::PlaceRfn(Box::new(ty.get_rfn_type(env))),
            Self::BoxType(box ty) => CoqType::PlaceRfn(Box::new(ty.get_rfn_type(env))),
            Self::LiteralParam(lit) => CoqType::Literal(lit.refinement_type.clone()),
            Self::Literal(lit) => CoqType::Literal(lit.get_rfn_type()),
            Self::Uninit(_) => CoqType::Unit,
            Self::Struct(su) =>
            // NOTE: we don't need to subst, due to our invariant that the instantiations for
            // struct uses are already fully substituted
            {
                CoqType::Literal(su.get_rfn_type())
            },
            Self::Enum(su) =>
            // similar to structs, we don't need to subst
            {
                su.get_rfn_type()
            },
            Self::Unit => CoqType::Unit,
            Self::Never => CoqType::Unit, // NOTE: could also choose to use an uninhabited type here
            Self::Var(i) => env.get(*i).unwrap().as_ref().unwrap().clone(),
            Self::RawPtr => CoqType::Loc,
        }
    }

    /// Get the layout of a type.
    pub fn get_syn_type(&self) -> SynType {
        match self {
            Self::Int(it) => SynType::Int(*it),
            Self::Bool => SynType::Bool,
            Self::Char => SynType::Char,
            Self::MutRef(..) => SynType::Ptr,
            Self::ShrRef(..) => SynType::Ptr,
            Self::BoxType(..) => SynType::Ptr,
            Self::Struct(s) => s.generate_syn_type_term(),
            Self::Enum(s) => s.generate_syn_type_term(),
            Self::LiteralParam(lit) => SynType::Literal(lit.syn_type.clone()),
            Self::Literal(lit) => lit.generate_syn_type_term(),
            Self::Uninit(st) => st.clone(),
            Self::Unit => SynType::Unit,
            // NOTE: for now, just treat Never as a ZST
            Self::Never => SynType::Never,
            Self::Var(i) => SynType::Var(*i),
            Self::RawPtr => SynType::Ptr,
        }
    }

    pub fn get_ty_lfts(&self, s: &mut HashSet<Lft>) {
        match self {
            Self::Int(_) => (),
            Self::Bool => (),
            Self::Char => (),
            Self::MutRef(box ty, lft) => {
                s.insert(lft.to_string());
                ty.get_ty_lfts(s)
            },
            Self::ShrRef(box ty, lft) => {
                s.insert(lft.to_string());
                ty.get_ty_lfts(s)
            },
            Self::BoxType(box ty) => ty.get_ty_lfts(s),
            Self::LiteralParam(lit) => {
                // TODO: use meta
                s.insert(format!("ty_lfts {}", lit.type_term));
            },
            Self::Literal(lit) => lit.get_ty_lfts(s),
            Self::Uninit(_) => (),
            Self::Struct(su) => su.get_ty_lfts(s),
            Self::Enum(su) => su.get_ty_lfts(s),
            Self::Unit => (),
            Self::Never => (),
            Self::Var(_i) => {
                s.insert("RAW".to_string());
            },
            Self::RawPtr => (),
        }
    }

    pub fn get_ty_wf_elctx(&self, s: &mut HashSet<String>) {
        match self {
            Self::Int(_) => (),
            Self::Bool => (),
            Self::Char => (),
            Self::MutRef(box ty, _lft) => ty.get_ty_wf_elctx(s),
            Self::ShrRef(box ty, _lft) => ty.get_ty_wf_elctx(s),
            Self::BoxType(box ty) => ty.get_ty_wf_elctx(s),
            Self::LiteralParam(lit) => {
                s.insert(format!("ty_wf_elctx {}", lit.type_term));
            },
            Self::Literal(lit) => lit.get_ty_wf_elctx(s),
            Self::Uninit(_) => (),
            Self::Struct(su) => su.get_ty_wf_elctx(s),
            Self::Enum(su) => su.get_ty_wf_elctx(s),
            Self::Unit => (),
            Self::Never => (),
            Self::Var(_i) => {
                s.insert("RAW".to_string());
            },
            Self::RawPtr => (),
        }
    }

    /// Check if the Type contains a free variable `Var(i)`.
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::MutRef(box t, _) => t.is_closed(),
            Self::ShrRef(box t, _) => t.is_closed(),
            Self::BoxType(box t) => t.is_closed(),
            _ => true,
        }
    }

    fn subst_core<F, G>(&mut self, substi: &[Option<F>], to_type: &G)
    where
        G: Fn(&F) -> Type<'def>,
    {
        match self {
            Self::MutRef(box t, _) => t.subst_core(substi, to_type),
            Self::ShrRef(box t, _) => t.subst_core(substi, to_type),
            Self::BoxType(box t) => t.subst_core(substi, to_type),
            Self::Struct(s) => {
                // the struct def itself should be closed, but the arguments to it may contain
                // further variables
                s.ty_params.iter_mut().map(|a| a.subst_core(substi, to_type)).count();
            },
            Self::Enum(s) => {
                s.ty_params.iter_mut().map(|a| a.subst_core(substi, to_type)).count();
            },
            Self::Var(i) => {
                if let Some(Some(ta)) = substi.get(*i) {
                    let ta_ty: Type<'def> = to_type(ta);
                    assert!(ta_ty.is_closed());
                    *self = ta_ty;
                }
            },
            _ => (),
        }
    }

    /// Substitute variables `Var` according to the given substitution (variable `i` is mapped to
    /// index `i` in the vector).
    /// The types in `substi` should not contain variables themselves, as this substitution
    /// operation is capture-incurring!
    pub fn subst(&mut self, substi: &[Option<Type<'def>>]) {
        self.subst_core(substi, &|x| x.clone())
    }

    /// Substitute variables `Var` with `substi`. See `subst` for documentation.
    pub fn subst_params(&mut self, substi: &[Option<LiteralTyParam>]) {
        self.subst_core(substi, &|x| Type::LiteralParam(x.clone()))
    }
}

/// Specification for location ownership of a type.
#[derive(Clone, Debug, PartialEq)]
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
    pub fn new(loc: String, rfn: String, ty: String, with_later: bool, annot_meta: TypeAnnotMeta) -> Self {
        TyOwnSpec {
            loc,
            with_later,
            rfn,
            ty,
            annot_meta,
        }
    }

    pub fn fmt_owned(&self, tid: &str) -> String {
        format!("{} ◁ₗ[{}, Owned {}] #({}) @ (◁ {})", self.loc, tid, self.with_later, self.rfn, self.ty)
    }

    pub fn fmt_shared(&self, tid: &str, lft: &str) -> String {
        format!("{} ◁ₗ[{}, Shared {}] #({}) @ (◁ {})", self.loc, tid, lft, self.rfn, self.ty)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum InvariantSpecFlags {
    /// fully persistent and timeless invariant
    Persistent,
    /// invariant with own sharing predicate,
    Plain,
    NonAtomic,
    Atomic,
}

#[derive(Clone, Debug, PartialEq)]
pub enum InvariantMode {
    All,
    OnlyShared,
    OnlyOwned,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InvariantSpec {
    /// the name of the type definition
    type_name: String,
    flags: InvariantSpecFlags,

    /// name for the sharing lifetime that is used in the invariant specifications
    shr_lft_binder: String,

    /// the refinement type of this struct
    rfn_type: CoqType,
    /// the binding pattern for the refinement of this type
    rfn_pat: CoqPattern,

    /// existentials that are introduced in the invariant
    existentials: Vec<(CoqName, CoqType)>,

    /// an optional invariant as a separating conjunction,
    invariants: Vec<(IProp, InvariantMode)>,
    /// additional type ownership
    ty_own_invariants: Vec<TyOwnSpec>,

    /// the specification of the abstracted refinement under a context where rfn_pat is bound
    abstracted_refinement: Option<CoqPattern>,
    // TODO add stuff for non-atomic/atomic invariants
    /// name, type, implicit or not
    coq_params: Vec<CoqParam>,
}

impl InvariantSpec {
    pub fn new(
        type_name: String,
        flags: InvariantSpecFlags,
        shr_lft_binder: String,
        rfn_type: CoqType,
        rfn_pat: CoqPattern,
        existentials: Vec<(CoqName, CoqType)>,
        invariants: Vec<(IProp, InvariantMode)>,
        ty_own_invariants: Vec<TyOwnSpec>,
        abstracted_refinement: Option<CoqPattern>,
        coq_params: Vec<CoqParam>,
    ) -> Self {
        match flags {
            InvariantSpecFlags::Persistent => {
                assert!(
                    invariants.iter().all(|it| it.1 == InvariantMode::All) && ty_own_invariants.is_empty()
                );
            },
            _ => (),
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
    pub fn provide_abstracted_refinement(&mut self, abstracted_refinement: CoqPattern) {
        if self.abstracted_refinement.is_some() {
            panic!("abstracted refinement for {} already provided", self.type_name);
        }
        self.abstracted_refinement = Some(abstracted_refinement);
    }

    fn make_existential_binders(&self) -> String {
        let mut out = String::with_capacity(200);

        if self.existentials.len() > 0 {
            write!(out, "∃ ").unwrap();
            let mut needs_sep = false;
            for (name, ty) in self.existentials.iter() {
                if needs_sep {
                    write!(out, " ").unwrap();
                }
                needs_sep = true;
                write!(out, "({} : {})", name, ty).unwrap();
            }
            write!(out, ", ").unwrap();
        }

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
        for own in self.ty_own_invariants.iter() {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_owned("π"))).unwrap();
        }

        for (inv, mode) in self.invariants.iter() {
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
        for own in self.ty_own_invariants.iter() {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_shared("π", &self.shr_lft_binder))).unwrap();
        }
        for (inv, mode) in self.invariants.iter() {
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
        for spec in self.ty_own_invariants.iter() {
            for ty in spec.annot_meta.escaped_tyvars.iter() {
                write!(out, " ++ (ty_lfts ({}))", ty.type_term).unwrap();
            }
            for lft in spec.annot_meta.escaped_lfts.iter() {
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
        for spec in self.ty_own_invariants.iter() {
            for ty in spec.annot_meta.escaped_tyvars.iter() {
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
        for (inv, _) in self.invariants.iter() {
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
            "{indent}Proof using {}. let __a := eval hnf in (rt_of {}) in exact __a. Defined.\n",
            generics.join(" "),
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
        write!(out, "{}Context `{{!typeGS Σ}}.\n", indent).unwrap();

        // add type parameters
        if generic_params.len() > 0 {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in generic_params.iter() {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in generic_params.iter() {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }

        // write coq parameters
        write!(out, "{} (* Additional parameters *)\n", indent).unwrap();
        if !self.coq_params.is_empty() {
            write!(out, "{}Context", indent).unwrap();
            for param in self.coq_params.iter() {
                write!(out, " {}", param).unwrap();
            }
            write!(out, ".\n").unwrap();
        }
        write!(out, "\n").unwrap();

        // get the applied base_rfn_type
        let rfn_instantiations: Vec<String> =
            generic_params.iter().map(|names| names.refinement_type.clone()).collect();
        let applied_base_rfn_type = CoqAppTerm::new(base_rfn_type, rfn_instantiations.clone());

        // get the applied base type
        let base_type_app: Vec<String> = generic_params.iter().map(|names| names.type_term.clone()).collect();
        let applied_base_type = CoqAppTerm::new(base_type_name, base_type_app);

        write!(
            out,
            "{}",
            self.generate_coq_type_def_core(
                applied_base_type.to_string().as_str(),
                applied_base_rfn_type.to_string().as_str(),
                &rfn_instantiations
            )
        )
        .unwrap();

        // finish
        write!(out, "End {}.\n", self.type_name).unwrap();
        write!(out, "Global Arguments {}_rt : clear implicits.\n", self.type_name).unwrap();

        out
    }

    pub fn rt_def_name(&self) -> String {
        format!("{}_rt", self.type_name)
    }
}

/// Representation options for structs.
#[derive(Debug, Clone, Copy, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
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
pub fn lookup_ty_param<'a, 'b>(name: &'a str, env: &'b [LiteralTyParam]) -> Option<&'b LiteralTyParam> {
    for names in env.iter() {
        if names.rust_name == name {
            return Some(names);
        }
    }
    None
}

pub type AbstractVariantRef<'def> = &'def RefCell<Option<AbstractVariant<'def>>>;

/// Description of a variant of a struct or enum.
#[derive(PartialEq, Debug, Clone)]
pub struct AbstractVariant<'def> {
    /// the fields. The types are closed, i.e. have no `Var` variables (but may have literals
    /// referring to the Coq binders introduced by a surrounding AbstractStruct)
    fields: Vec<(String, Type<'def>)>,
    /// `fields` with type variables substituted with literal coq strings for their definition
    subst_fields: Vec<(String, Type<'def>)>,
    /// the refinement type of the plain struct
    rfn_type: CoqType,
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
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The core of generating the sls definition, without the section + context intro.
    pub fn generate_coq_sls_def_core(&self, typarams: &[String], typarams_use: &[String]) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // intro to main def
        write!(
            out,
            "{indent}Definition {} {} : struct_layout_spec := mk_sls \"{}\" [",
            self.sls_def_name,
            typarams.join(" "),
            self.name
        )
        .unwrap();
        let mut needs_sep = false;
        for (name, ty) in self.subst_fields.iter() {
            if needs_sep {
                out.push_str(";");
            }
            needs_sep = true;
            let synty = ty.get_syn_type();
            write!(out, "\n{indent}{indent}(\"{}\", {})", name, synty).unwrap();
        }
        write!(out, "] {}.\n", self.repr).unwrap();

        // also generate a definition for the syntype
        write!(
            out,
            "{indent}Definition {} {} : syn_type := {} {}.\n",
            self.st_def_name,
            typarams.join(" "),
            self.sls_def_name,
            typarams_use.join(" ")
        )
        .unwrap();

        out
    }

    /// Generate a Coq definition for the struct layout spec.
    pub fn generate_coq_sls_def(&self, ty_params: &[LiteralTyParam]) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.sls_def_name).unwrap();
        write!(out, "{}Context `{{!typeGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let mut typarams = Vec::new();
        let mut typarams_use = Vec::new();
        if ty_params.len() > 0 {
            for names in ty_params.iter() {
                typarams.push(format!("({} : syn_type)", names.syn_type));
                typarams_use.push(format!("{}", names.syn_type));
            }
        }
        out.push_str("\n");

        write!(out, "{}", self.generate_coq_sls_def_core(&typarams, &typarams_use)).unwrap();

        // finish
        write!(out, "End {}.\n", self.sls_def_name).unwrap();
        out
    }

    pub fn generate_coq_type_term(&self, sls_app: Vec<String>) -> String {
        let mut out = String::with_capacity(200);

        write!(out, "struct_t {} +[", CoqAppTerm::new(&self.sls_def_name, sls_app)).unwrap();

        let mut needs_sep = false;
        for (_name, ty) in self.subst_fields.iter() {
            if needs_sep {
                out.push_str("; ");
            }
            needs_sep = true;
            write!(out, "{}", ty).unwrap();
        }
        out.push_str("]");

        out
    }

    pub fn generate_coq_type_def_core(&self, ty_params: &[LiteralTyParam]) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate terms to apply the sls app to
        let mut sls_app = Vec::new();
        for names in ty_params.iter() {
            // TODO this is duplicated with the same processing for Type::Literal...
            let term = format!("(ty_syn_type {})", names.type_term);
            sls_app.push(term);
        }

        // intro to main def
        write!(
            out,
            "{}Definition {} : type ({}) := {}.\n",
            indent,
            self.plain_ty_name,
            self.rfn_type,
            self.generate_coq_type_term(sls_app)
        )
        .unwrap();

        // generate the refinement type definition
        let rt_params: Vec<_> = ty_params.iter().map(|x| x.refinement_type.clone()).collect();
        write!(out, "{indent}Definition {} : Type.\n", self.plain_rt_def_name).unwrap();
        write!(
            out,
            "{indent}Proof using {}. let __a := eval hnf in (rt_of {}) in exact __a. Defined.\n",
            rt_params.join(" "),
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
    pub fn generate_coq_type_def(&self, ty_params: &[LiteralTyParam]) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{!typeGS Σ}}.\n", indent).unwrap();

        // add type parameters, and build a list of terms to apply the sls def to
        if ty_params.len() > 0 {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in ty_params.iter() {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in ty_params.iter() {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push_str("\n");

        write!(out, "{}", self.generate_coq_type_def_core(ty_params)).unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_def_name).unwrap();
        out
    }
}

pub type AbstractStructRef<'def> = &'def RefCell<Option<AbstractStruct<'def>>>;

/// Description of a struct type.
// TODO: mechanisms for resolving mutually recursive types.
#[derive(Clone, Debug, PartialEq)]
pub struct AbstractStruct<'def> {
    /// an optional invariant/ existential abstraction for this struct
    invariant: Option<InvariantSpec>,

    /// the actual definition of the variant
    variant_def: AbstractVariant<'def>,

    /// names for the type parameters (for the Coq definitions) in De Bruijn representation
    /// (that is, in the Coq definition, we will substitute the variable `Var(0)` in `fields`
    /// for the first element of this vector)
    /// TODO: will make those options once we handle lifetime parameters properly.
    ty_params: Vec<LiteralTyParam>,
}

impl<'def> AbstractStruct<'def> {
    pub fn new(variant_def: AbstractVariant<'def>, ty_params: Vec<LiteralTyParam>) -> Self {
        AbstractStruct {
            invariant: None,
            variant_def,
            ty_params,
        }
    }

    /// Check if the struct has type parameters.
    pub fn has_type_params(&self) -> bool {
        self.ty_params.len() > 0
    }

    /// Get the name of this struct
    pub fn name(&self) -> &str {
        &self.variant_def.name()
    }

    pub fn sls_def_name(&self) -> &str {
        &self.variant_def.sls_def_name
    }

    pub fn st_def_name(&self) -> &str {
        &self.variant_def.st_def_name
    }

    pub fn plain_ty_name(&self) -> &str {
        &self.variant_def.plain_ty_name
    }

    /// Get the name of the struct, or an ADT defined on it, if available.
    pub fn public_type_name(&self) -> &str {
        match self.invariant {
            Some(ref inv) => &inv.type_name,
            None => self.plain_ty_name(),
        }
    }

    pub fn plain_rt_def_name(&self) -> &str {
        &self.variant_def.plain_rt_def_name
    }

    pub fn public_rt_def_name(&self) -> String {
        match self.invariant {
            Some(ref inv) => inv.rt_def_name().to_string(),
            None => self.plain_rt_def_name().to_string(),
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
    pub fn generate_coq_sls_def(&self) -> String {
        self.variant_def.generate_coq_sls_def(&self.ty_params)
    }

    /// Generate a Coq definition for the struct type alias.
    /// TODO: maybe we should also generate a separate alias def for the refinement type to make
    /// things more readable?
    pub fn generate_coq_type_def(&self) -> String {
        self.variant_def.generate_coq_type_def(&self.ty_params)
    }

    /// Generate an optional definition for the invariant of this type, if one has been specified.
    pub fn generate_optional_invariant_def(&self) -> Option<String> {
        match self.invariant {
            None => None,
            Some(ref spec) => Some(spec.generate_coq_type_def(
                self.plain_ty_name(),
                &self.plain_rt_def_name(),
                &self.ty_params,
            )),
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
    pub fn finish(self, ty_params: &[LiteralTyParam]) -> AbstractVariant<'def> {
        let sls_def_name: String = format!("{}_sls", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_def_name: String = format!("{}_rt", &self.name);

        let ty_env: Vec<Option<Type<'def>>> =
            ty_params.iter().map(|lit| Some(Type::LiteralParam(lit.clone()))).collect();

        // create a fully substituted version of the types now
        let subst_fields: Vec<_> = self
            .fields
            .iter()
            .map(|(name, ty)| {
                let mut ty2 = ty.clone();
                ty2.subst(&ty_env);
                (name.clone(), ty2)
            })
            .collect();

        let rfn_type = CoqType::PList(
            "place_rfn".to_string(),
            subst_fields.iter().map(|(_, t)| t.get_rfn_type(&[])).collect(),
        );

        AbstractVariant {
            rfn_type,
            fields: self.fields,
            subst_fields,
            repr: self.repr,
            name: self.name,
            plain_ty_name,
            sls_def_name,
            st_def_name,
            plain_rt_def_name,
        }
    }

    /// Finish building the struct type and generate an abstract struct definition.
    pub fn finish_as_struct(self, ty_params: Vec<LiteralTyParam>) -> AbstractStruct<'def> {
        let variant = self.finish(&ty_params);
        AbstractStruct {
            variant_def: variant,
            invariant: None,
            ty_params,
        }
    }

    /// Initialize a struct builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    pub fn new(name: String, repr: StructRepr) -> VariantBuilder<'def> {
        VariantBuilder {
            fields: Vec::new(),
            name,
            repr,
        }
    }

    /// Append a field to the struct def.
    pub fn add_field(&mut self, name: &str, ty: Type<'def>) {
        self.fields.push((name.to_string(), ty));
    }
}

/// Create a struct representation of a tuple with `num_fields`, all of which are generic.
pub fn make_tuple_struct_repr<'def>(num_fields: usize) -> AbstractStruct<'def> {
    let name = format!("tuple{}", num_fields);

    let mut ty_params = Vec::new();
    for i in 0..num_fields {
        let param_name = format!("T{}", i);
        ty_params.push(param_name);
    }
    let ty_param_defs = ty_params
        .iter()
        .map(|name| LiteralTyParam {
            rust_name: name.clone(),
            type_term: format!("{}_ty", name),
            refinement_type: format!("{}_rt", name),
            syn_type: format!("{}_st", name),
        })
        .collect();

    let mut builder = VariantBuilder::new(name, StructRepr::ReprRust);

    for i in 0..num_fields {
        builder.add_field(&i.to_string(), Type::Var(num_fields - i - 1));
    }

    builder.finish_as_struct(ty_param_defs)
}

/// A usage of an `AbstractStruct` that instantiates its type parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct AbstractStructUse<'def> {
    /// reference to the struct's definition, or None if unit
    pub def: Option<AbstractStructRef<'def>>,
    /// Instantiations for type parameters. These should _not_ contain `Var` constructors.
    pub ty_params: Vec<Type<'def>>,
    /// does this refer to the raw type without invariants?
    pub raw: TypeIsRaw,
}

impl<'def> AbstractStructUse<'def> {
    /// `params` should not contain `Var`
    pub fn new(s: AbstractStructRef<'def>, params: Vec<Type<'def>>, raw: TypeIsRaw) -> Self {
        AbstractStructUse {
            def: Some(s),
            ty_params: params,
            raw,
        }
    }

    /// Creates a new use of unit.
    pub fn new_unit() -> Self {
        AbstractStructUse {
            def: None,
            ty_params: Vec::new(),
            raw: TypeIsRaw::Yes,
        }
    }

    /// Returns true iff this is a use of unit.
    pub fn is_unit(&self) -> bool {
        self.def.is_none()
    }

    pub fn is_raw(&self) -> bool {
        self.raw == TypeIsRaw::Yes
    }

    pub fn make_raw(&mut self) {
        self.raw = TypeIsRaw::Yes;
    }

    /// Add the lifetimes appearing in this type to `s`.
    pub fn get_ty_lfts(&self, _s: &mut HashSet<Lft>) {
        // TODO
    }

    /// Add the lifetime constraints in this type to `s`.
    pub fn get_ty_wf_elctx(&self, _s: &mut HashSet<String>) {
        // TODO
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    pub fn get_rfn_type(&self) -> String {
        if let Some(def) = self.def.as_ref() {
            let rfn_instantiations: Vec<String> =
                self.ty_params.iter().map(|ty| ty.get_rfn_type(&[]).to_string()).collect();

            let def = def.borrow();
            let def = def.as_ref();
            let inv = &def.unwrap().invariant.as_ref();

            if self.is_raw() || inv.is_none() {
                let rfn_type = def.unwrap().plain_rt_def_name().to_string();
                let applied = CoqAppTerm::new(rfn_type, rfn_instantiations);
                applied.to_string()
            } else {
                let inv = inv.unwrap();
                let rfn_type = inv.rt_def_name();
                let applied = CoqAppTerm::new(rfn_type, rfn_instantiations);
                applied.to_string()
            }
        } else {
            CoqType::Unit.to_string()
        }
    }

    /// Generate a term for the struct_layout (of type struct_layout)
    pub fn generate_struct_layout_term(&self) -> String {
        if let Some(def) = self.def.as_ref() {
            // first get the syntys for the type params
            let mut param_sts = Vec::new();
            for p in self.ty_params.iter() {
                let st = p.get_syn_type();
                param_sts.push(format!("({})", st));
            }

            // use_struct_layout_alg' ([my_spec] [params])
            let specialized_spec =
                format!("({})", CoqAppTerm::new(def.borrow().as_ref().unwrap().sls_def_name(), param_sts));
            CoqAppTerm::new("use_struct_layout_alg'".to_string(), vec![specialized_spec]).to_string()
        } else {
            Layout::UnitLayout.to_string()
        }
    }

    pub fn generate_struct_layout_spec_term(&self) -> String {
        if let Some(def) = self.def.as_ref() {
            // first get the syntys for the type params
            let mut param_sts = Vec::new();
            for p in self.ty_params.iter() {
                let st = p.get_syn_type();
                param_sts.push(format!("({})", st));
            }
            // TODO generates too many apps

            // use_struct_layout_alg' ([my_spec] [params])
            let specialized_spec =
                format!("({})", CoqAppTerm::new(def.borrow().as_ref().unwrap().sls_def_name(), param_sts));
            specialized_spec.to_string()
        } else {
            panic!("unit has no sls");
        }
    }

    /// Get the syn_type term for this struct use.
    pub fn generate_syn_type_term(&self) -> SynType {
        if let Some(def) = self.def.as_ref() {
            // first get the syntys for the type params
            let mut param_sts = Vec::new();
            for p in self.ty_params.iter() {
                let st = p.get_syn_type();
                param_sts.push(format!("({})", st));
            }
            // TODO generates too many apps

            let specialized_spec =
                CoqAppTerm::new(def.borrow().as_ref().unwrap().st_def_name().to_string(), param_sts);
            SynType::Literal(format!("{}", specialized_spec))
        } else {
            SynType::Unit
        }
    }

    /// Generate a string representation of this struct use.
    pub fn generate_type_term(&self) -> String {
        if let Some(def) = self.def.as_ref() {
            let mut param_tys = Vec::new();
            for p in self.ty_params.iter() {
                param_tys.push(format!("({})", p));
            }
            let def = def.borrow();
            let def = def.as_ref().unwrap();
            if !self.is_raw() && def.invariant.is_some() {
                if let Some(ref inv) = def.invariant {
                    let term = CoqAppTerm::new(inv.type_name.clone(), param_tys);
                    term.to_string()
                } else {
                    unreachable!();
                }
            } else {
                let term = CoqAppTerm::new(def.plain_ty_name(), param_tys);
                term.to_string()
            }
        } else {
            Type::Unit.to_string()
        }
    }
}

/// Specification of an enum in terms of a Coq type refining it.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumSpec {
    /// the refinement type of the enum
    pub rfn_type: CoqType,
    /// the refinement patterns for each of the variants
    /// eg. for options:
    /// - (None, [], -[])
    /// - (Some, [x], -[x])
    pub variant_patterns: Vec<(String, Vec<String>, String)>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct AbstractEnum<'def> {
    /// variants of this enum: name, variant, a mask describing which of the type parameters it uses, and the
    /// discriminant
    pub(crate) variants: Vec<(String, AbstractStructRef<'def>, Vec<bool>, i128)>,

    /// specification
    spec: EnumSpec,
    /// the enum's name
    name: String,
    /// the representation of the enum
    repr: EnumRepr,

    /// an optional declaration of a Coq inductive for this enum
    optional_inductive_def: Option<CoqInductive>,

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

impl<'def> AbstractEnum<'def> {
    /// Check whether this enum has any type parameters.
    pub fn has_type_params(&self) -> bool {
        self.ty_params.len() > 0
    }

    /// Get the name of this enum.
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn public_type_name(&self) -> &str {
        &self.plain_ty_name
    }

    pub fn public_rt_def_name(&self) -> &str {
        &self.plain_rt_name
    }

    pub fn els_def_name(&self) -> &str {
        &self.els_def_name
    }

    pub fn st_def_name(&self) -> &str {
        &self.st_def_name
    }

    pub fn get_variant(&self, i: usize) -> Option<&(String, AbstractStructRef<'def>, Vec<bool>, i128)> {
        self.variants.get(i)
    }

    /// Generate a Coq definition for the enum layout spec, and all the struct_layout_specs for the
    /// variants.
    pub fn generate_coq_els_def(&self) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.els_def_name).unwrap();
        write!(out, "{}Context `{{!typeGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let mut typarams = Vec::new();
        let mut typarams_use = Vec::new();
        if self.ty_params.len() > 0 {
            for names in self.ty_params.iter() {
                typarams.push(format!("({} : syn_type)", names.syn_type));
                typarams_use.push(format!("{}", names.syn_type));
            }
        }
        out.push_str("\n");

        let mut variant_typarams = Vec::new();

        // generate all the component structs
        for (_, v, mask, _) in self.variants.iter() {
            let vbor = v.borrow();
            let vbor = vbor.as_ref().unwrap();

            let mut typarams = Vec::new();
            let mut typarams_use = Vec::new();
            for (name, mask) in self.ty_params.iter().zip(mask.iter()) {
                if *mask {
                    typarams.push(format!("({} : syn_type)", name.syn_type.to_string()));
                    typarams_use.push(name.syn_type.to_string());
                }
            }
            write!(out, "{}\n", vbor.variant_def.generate_coq_sls_def_core(&typarams, &typarams_use))
                .unwrap();
            variant_typarams.push(typarams);
        }

        // intro to main def
        write!(
            out,
            "{indent}Program Definition {} {}: enum_layout_spec := mk_els \"{}\" {} [",
            self.els_def_name,
            typarams.join(" "),
            self.name,
            self.discriminant_type
        )
        .unwrap();
        let mut needs_sep = false;

        for ((name, var, _, _), masked_typarams) in self.variants.iter().zip(variant_typarams.iter()) {
            if needs_sep {
                out.push_str(";");
            }
            needs_sep = true;

            let vbor = var.borrow();
            let vbor = vbor.as_ref().unwrap();

            write!(
                out,
                "\n{}{}(\"{}\", {} {})",
                indent,
                indent,
                name,
                vbor.st_def_name(),
                masked_typarams.join(" ")
            )
            .unwrap();
        }
        // write the repr
        write!(out, "] {} [", self.repr).unwrap();
        // now write the tag-discriminant list
        needs_sep = false;
        for (name, _, _, discr) in self.variants.iter() {
            if needs_sep {
                out.push_str("; ");
            }
            needs_sep = true;

            write!(out, "(\"{}\", {})", name, discr).unwrap();
        }
        out.push_str("] _ _ _ _.\n");
        write!(out, "{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. done. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. repeat first [econstructor | init_cache; solve_goal]. Qed.\n")
            .unwrap();
        write!(out, "{indent}Global Typeclasses Opaque {}.\n", self.els_def_name).unwrap();

        // also write an st definition
        write!(
            out,
            "{indent}Definition {} {} : syn_type := {} {}.\n",
            self.st_def_name,
            typarams.join(" "),
            self.els_def_name,
            typarams_use.join(" ")
        )
        .unwrap();

        // finish
        write!(out, "End {}.\n", self.els_def_name).unwrap();

        out
    }

    /// Generate a function that maps the refinement to the tag as a Coq string (`enum_tag`).
    fn generate_enum_tag(&self) -> String {
        let mut out = String::with_capacity(200);

        let spec = &self.spec;
        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((name, _, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => \"{name}\" ", CoqAppTerm::new(pat, apps.clone())).unwrap();
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
        for ((_name, var, _, _), (pat, apps, rfn)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            let v = var.borrow();
            let v = v.as_ref().unwrap();
            // we can just use the plain name here, because we assume this is used in an
            // environment where all the type parametes are already instantiated.
            let ty = v.public_type_name();

            write!(out, "| {} => existT _ ({ty}, {rfn})", CoqAppTerm::new(pat, apps.clone())).unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps (valid) tags to the corresponding Coq type for the variant.
    fn generate_enum_match(&self) -> String {
        let _spec = &self.spec;

        let conditions: Vec<_> = self
            .variants
            .iter()
            .map(|(name, var, _, _)| {
                let v = var.borrow();
                let v = v.as_ref().unwrap();
                let ty = v.public_type_name();

                format!("if (decide (variant = \"{name}\")) then Some $ existT _ {ty}")
            })
            .collect();
        format!("λ variant, {} else None", conditions.join(" else "))
    }

    fn generate_lfts(&self) -> String {
        // TODO: probably should build this up modularly over the fields

        let mut v: Vec<_> = self.ty_params.iter().map(|p| format!("(ty_lfts {})", p.type_term)).collect();
        v.push("[]".to_string());
        format!("{}", v.join(" ++ "))
    }

    fn generate_wf_elctx(&self) -> String {
        // TODO: probably should build this up modularly over the fields
        let mut v: Vec<_> = self.ty_params.iter().map(|p| format!("(ty_wf_E {})", p.type_term)).collect();
        v.push("[]".to_string());
        format!("{}", v.join(" ++ "))
    }

    fn generate_construct_enum(&self) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        for ((tag, s, mask, _), (pat, args, res)) in
            self.variants.iter().zip(self.spec.variant_patterns.iter())
        {
            write!(
                out,
                "{indent}Global Program Instance construct_enum_{}_{tag} {} ",
                self.name,
                args.join(" ")
            )
            .unwrap();

            // add st constraints on params
            let mut sls_app = Vec::new();
            for (ty, m) in self.ty_params.iter().zip(mask.iter()) {
                if *m {
                    write!(
                        out,
                        "{} `{{!TCDone ({} = ty_syn_type {})}} ",
                        ty.syn_type, ty.syn_type, ty.type_term
                    )
                    .unwrap();
                    sls_app.push(ty.syn_type.clone());
                }
            }
            let s2 = s.borrow();
            let s3 = s2.as_ref().unwrap();
            let ty_def_term = s3.variant_def.generate_coq_type_term(sls_app);

            write!(
                out,
                ": ConstructEnum {} \"{}\" ({}) {} {} := construct_enum _ _.\n",
                self.enum_def_name,
                tag,
                ty_def_term,
                res,
                CoqAppTerm::new(pat, args.clone())
            )
            .unwrap();
            write!(out, "{indent}Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.\n").unwrap();
        }

        out
    }

    pub fn generate_coq_type_def(&self) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{!typeGS Σ}}.\n", indent).unwrap();

        // add type parameters, and build a list of terms to apply the els def to
        if self.ty_params.len() > 0 {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in self.ty_params.iter() {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");

            write!(out, "{}Context", indent).unwrap();
            for names in self.ty_params.iter() {
                write!(out, " ({} : type ({}))", names.type_term, names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push_str("\n");

        let rt_params: Vec<_> = self.ty_params.iter().map(|x| x.refinement_type.clone()).collect();

        // define types and type abstractions for all the component types.
        // TODO: we should actually use the abstracted types here.
        for (_name, variant, _, _) in self.variants.iter() {
            let v = variant.borrow();
            let v = v.as_ref().unwrap();
            write!(out, "{}\n", v.variant_def.generate_coq_type_def_core(&v.ty_params)).unwrap();

            if let Some(inv) = &v.invariant {
                let inv_def = inv.generate_coq_type_def_core(
                    v.variant_def.plain_ty_name.as_str(),
                    v.variant_def.plain_rt_def_name.as_str(),
                    &rt_params,
                );
                write!(out, "{}\n", inv_def).unwrap();
            }
        }

        // write the Coq inductive, if applicable
        if let Some(ref ind) = self.optional_inductive_def {
            let mut assertions = CoqTopLevelAssertions::empty();

            assertions.push(CoqTopLevelAssertion::Comment(format!(
                "auto-generated representation of {}",
                ind.name
            )));
            // TODO don't clone
            assertions.push(CoqTopLevelAssertion::InductiveDecl(ind.clone()));
            // prove that it is inhabited
            let instance_decl = CoqInstanceDecl {
                name: None,
                params: CoqParamList::empty(),
                ty: CoqType::Literal(format!("Inhabited {}", ind.name)),
                body: CoqDefBody::Script(
                    CoqProofScript(vec![CoqProofItem::Literal(format!("solve_inhabited"))]),
                    CoqProofScriptTerminator::Qed,
                ),
            };
            assertions.push(CoqTopLevelAssertion::InstanceDecl(instance_decl));

            let mut code_fmt = IndentWriter::new(BASE_INDENT, &mut out);
            write!(code_fmt, "\n").unwrap();
            write!(code_fmt, "{assertions}").unwrap();
        }

        // build the els term applied to generics
        // generate terms to apply the sls app to
        let mut els_app = Vec::new();
        for names in self.ty_params.iter() {
            let term = format!("(ty_syn_type {})", names.type_term);
            els_app.push(term);
        }
        let els_app_term = CoqAppTerm::new(&self.els_def_name, els_app);

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
}

pub type AbstractEnumRef<'def> = &'def RefCell<Option<AbstractEnum<'def>>>;

/// A builder for plain enums without fancy invariants etc.
pub struct EnumBuilder<'def> {
    /// the variants
    variants: Vec<(String, AbstractStructRef<'def>, Vec<bool>, i128)>,
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
    pub fn finish(self, optional_inductive_def: Option<CoqInductive>, spec: EnumSpec) -> AbstractEnum<'def> {
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
        variant: AbstractStructRef<'def>,
        used_params: Vec<bool>,
        discriminant: i128,
    ) {
        self.variants.push((name.to_string(), variant, used_params, discriminant));
    }
}

/// A usage of an `AbstractEnum` that instantiates its type parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct AbstractEnumUse<'def> {
    /// reference to the enum's definition
    pub def: AbstractEnumRef<'def>,
    /// Instantiations for type parameters. These should _not_ contain `Var` constructors.
    pub ty_params: Vec<Type<'def>>,
}

impl<'def> AbstractEnumUse<'def> {
    /// `params` should not contain `Var`
    pub fn new(s: AbstractEnumRef<'def>, params: Vec<Type<'def>>) -> Self {
        AbstractEnumUse {
            def: s,
            ty_params: params,
        }
    }

    /// Add the lifetimes appearing in this type to `s`.
    pub fn get_ty_lfts(&self, _s: &mut HashSet<Lft>) {
        // TODO
    }

    /// Add the lifetime constraints in this type to `s`.
    pub fn get_ty_wf_elctx(&self, _s: &mut HashSet<String>) {
        // TODO
    }

    /// Get the refinement type of an enum usage.
    /// This requires that all type parameters of the enum have been instantiated.
    pub fn get_rfn_type(&self) -> CoqType {
        let env = Vec::new(); // we use the empty environment per our assumption
        let rfn_instantiations: Vec<CoqType> =
            self.ty_params.iter().map(|ty| ty.get_rfn_type(&env)).collect();

        let mut rfn_type = self.def.borrow().as_ref().unwrap().spec.rfn_type.clone();
        rfn_type.subst(&rfn_instantiations);

        assert!(rfn_type.is_closed());
        rfn_type
    }

    /// Generate a term for the enum layout (of type struct_layout)
    pub fn generate_enum_layout_term(&self) -> String {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in self.ty_params.iter() {
            let st = p.get_syn_type();
            param_sts.push(format!("({})", st));
        }

        // use_struct_layout_alg' ([my_spec] [params])
        let specialized_spec = format!(
            "({})",
            CoqAppTerm::new(self.def.borrow().as_ref().unwrap().els_def_name.clone(), param_sts)
        );
        CoqAppTerm::new("use_enum_layout_alg'".to_string(), vec![specialized_spec]).to_string()
    }

    /// Generate a term for the enum layout spec (of type enum_layout_spec).
    pub fn generate_enum_layout_spec_term(&self) -> String {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in self.ty_params.iter() {
            let st = p.get_syn_type();
            param_sts.push(format!("({})", st));
        }

        // use_struct_layout_alg' ([my_spec] [params])
        let specialized_spec = format!(
            "({})",
            CoqAppTerm::new(self.def.borrow().as_ref().unwrap().els_def_name.clone(), param_sts)
        );
        specialized_spec.to_string()
    }

    /// Get the syn_type term for this enum use.
    pub fn generate_syn_type_term(&self) -> SynType {
        // first get the syntys for the type params
        let mut param_sts = Vec::new();
        for p in self.ty_params.iter() {
            let st = p.get_syn_type();
            param_sts.push(format!("({})", st));
        }

        // [my_spec] [params]
        let specialized_spec =
            CoqAppTerm::new(self.def.borrow().as_ref().unwrap().st_def_name.clone(), param_sts);
        SynType::Literal(format!("{}", specialized_spec))
    }

    /// Generate a string representation of this enum use.
    pub fn generate_type_term(&self) -> String {
        let mut param_tys = Vec::new();
        for p in self.ty_params.iter() {
            param_tys.push(format!("({})", p));
        }
        let def = self.def.borrow();
        let def = def.as_ref().unwrap();
        let term = CoqAppTerm::new(def.plain_ty_name.clone(), param_tys);
        term.to_string()
    }
}

/// Environment that gives concrete layouts to generics and opaque structs
type LayoutEnv = HashMap<String, Layout>;

/// A representation of Caesium layouts we are interested in.
#[derive(Hash, Clone, Debug, Eq, PartialEq)]
pub enum Layout {
    // in the case of  32bits
    PtrLayout,
    // layout specified by the int type
    IntLayout(IntType),
    // size 1, similar to u8/i8
    BoolLayout,
    // size 4, similar to u32
    CharLayout,
    // guaranteed to have size 0 and alignment 1.
    UnitLayout,
    /// used for variable layout terms, e.g. for struct layouts or generics
    Literal(CoqAppTerm<String>),
    /// padding of a given number of bytes
    PadLayout(u32),
}

impl Display for Layout {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::PtrLayout => write!(f, "void*"),
            Self::IntLayout(it) => write!(f, "(it_layout {})", it),
            Self::BoolLayout => write!(f, "bool_layout"),
            Self::CharLayout => write!(f, "char_layout"),
            Self::UnitLayout => write!(f, "(layout_of unit_sl)"),
            Self::Literal(n) => write!(f, "{}", n),
            Self::PadLayout(s) => write!(f, "(Layout {}%nat 0%nat)", s),
        }
    }
}

impl Layout {
    pub fn size(&self, env: &LayoutEnv) -> Option<u32> {
        match self {
            Self::PtrLayout => Some(4),
            Self::IntLayout(it) => Some(it.size()),
            Self::BoolLayout => Some(1),
            Self::CharLayout => Some(4),
            Self::UnitLayout => Some(0),
            Self::Literal(n) => {
                // TODO: this doesn't work if the layout is applied to things.
                match env.get(&n.lhs) {
                    None => None,
                    Some(ly) => ly.size(env),
                }
            },
            //Self::StructLayout(ly) => ly.size(env),
            Self::PadLayout(s) => Some(*s),
        }
    }

    pub fn alignment(&self, env: &LayoutEnv) -> Option<u32> {
        match self {
            Self::PtrLayout => Some(4),
            Self::IntLayout(it) => Some(it.alignment()),
            Self::BoolLayout => Some(1),
            Self::CharLayout => Some(4),
            Self::UnitLayout => Some(1),
            Self::Literal(n) => {
                // TODO: this doesn't work if the layout is applied to things.
                match env.get(&n.lhs) {
                    None => None,
                    Some(ly) => ly.alignment(env),
                }
            },
            //Self::StructLayout(ly) => ly.alignment(env),
            Self::PadLayout(_) => Some(1),
        }
    }
}

// better representation of Iprops?
// - in particular for building the existential abstraction, direct support for existentials would be good.
// - DeBruijn probably not worth it, I don't need subst or anything like that. just try to keep variables
//   apart when generating them.

#[derive(Debug, Clone, PartialEq)]
pub struct CoqBinder(CoqName, CoqType);
impl CoqBinder {
    pub fn new(n: CoqName, t: CoqType) -> Self {
        CoqBinder(n, t)
    }
}

impl Display for CoqBinder {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} : {}", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq)]
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
    if v.len() > 0 {
        let mut needs_sep = false;
        for s in v.iter() {
            if needs_sep {
                write!(f, " {} ", op)?;
            }
            needs_sep = true;
            write!(f, "({})", s)?;
        }
    } else {
        write!(f, "True")?;
    }
    Ok(())
}

fn fmt_binders(b: &[CoqBinder], op: &str, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "{}", op)?;

    for CoqBinder(id, ty) in b.iter() {
        write!(f, " ({} : {})", id, ty)?;
    }
    Ok(())
}

impl Display for IProp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::True => write!(f, "True"),
            Self::Atom(a) => write!(f, "{}", a),
            Self::Pure(a) => write!(f, "⌜{}⌝", a),
            Self::PureWithName(p, name) => write!(f, "⌜name_hint \"{name}\" ({p})⌝"),
            Self::Sep(v) => fmt_with_op(&v, "∗", f),
            Self::Disj(v) => fmt_with_op(&v, "∨", f),
            Self::Conj(v) => fmt_with_op(&v, "∧", f),
            Self::Wand(l, r) => {
                write!(f, "({}) -∗ {}", l, r)
            },
            Self::Exists(b, p) => {
                fmt_binders(b, "∃", f)?;
                write!(f, ", {}", p)
            },
            Self::All(b, p) => {
                fmt_binders(b, "∀", f)?;
                write!(f, ", {}", p)
            },
        }
    }
}

/// Representation of an Iris predicate
#[derive(Debug, Clone)]
pub struct IPropPredicate {
    binders: Vec<CoqBinder>,
    prop: IProp,
}

impl IPropPredicate {
    pub fn new(binders: Vec<CoqBinder>, prop: IProp) -> IPropPredicate {
        IPropPredicate { binders, prop }
    }
}

impl Display for IPropPredicate {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        fmt_binders(&self.binders, "λ", f)?;
        write!(f, ", {}", self.prop)
    }
}

/// Representation of a loop invariant
#[derive(Debug, Clone)]
pub struct LoopSpec {
    /// the functional invariant as a predicate on the refinement of local variables.
    pub func_predicate: IPropPredicate,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CoqParam {
    pub name: CoqName,
    pub ty: CoqType,
    pub implicit: bool,
}

impl CoqParam {
    pub fn new(name: CoqName, ty: CoqType, implicit: bool) -> Self {
        Self { name, ty, implicit }
    }

    pub fn format(&self, f: &mut Formatter, make_implicits: bool) -> fmt::Result {
        if self.implicit {
            if make_implicits { write!(f, "`{{{}}}", self.ty) } else { write!(f, "`({})", self.ty) }
        } else {
            write!(f, "({} : {})", self.name, self.ty)
        }
    }
}

impl Display for CoqParam {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.format(f, true)
    }
}

/**
 * A Caesium function specification.
 */
#[derive(Debug)]
pub struct FunctionSpec<'def> {
    /// Coq-level parameters the typing statement needs (bool is for implicit or not)
    pub coq_params: Vec<CoqParam>,
    /// Function name
    pub function_name: String,
    /// The name of the spec
    pub spec_name: String,

    /// lifetime parameters (available in the typing proof)
    pub lifetimes: Vec<Lft>,
    pub params: Vec<(CoqName, CoqType)>,
    pub ty_params: Vec<(CoqName, CoqType)>,
    /// external lifetime context
    pub elctx: Vec<ExtLftConstr>,
    /// precondition as a separating conjunction
    pub pre: IProp,
    /// argument types including refinements
    pub args: Vec<TypeWithRef<'def>>,
    /// existential quantifiers for the postcondition
    pub existentials: Vec<(CoqName, CoqType)>,
    /// return type
    pub ret: TypeWithRef<'def>,
    /// postcondition as a separating conjunction
    pub post: IProp,
    /// true iff any attributes have been provided
    has_spec: bool,
}

impl<'def> FunctionSpec<'def> {
    fn format_elctx(&self) -> String {
        let mut out = String::with_capacity(100);
        out.push_str("λ ϝ, [");
        let mut need_sep = false;
        for (ref lft1, ref lft2) in self.elctx.iter() {
            if need_sep {
                out.push_str(", ");
            }
            out.push_str(format!("({}, {})", lft1, lft2).as_str());
            need_sep = true;
        }
        out.push_str("]");
        out
    }

    pub(crate) fn format_coq_params(&self) -> String {
        let mut out = String::with_capacity(100);
        if self.coq_params.len() == 0 {
        } else {
            let mut need_sep = false;
            for param in self.coq_params.iter() {
                if need_sep {
                    out.push_str(" ");
                }
                out.push_str(format!("{}", param).as_str());
                need_sep = true;
            }
        }
        out
    }

    fn format_args(&self) -> String {
        let mut out = String::with_capacity(100);
        if self.args.len() == 0 {
        } else {
            let mut need_sep = false;
            for type_with_rfn in self.args.iter() {
                if need_sep {
                    out.push_str(", ");
                }
                out.push_str(format!("{}", type_with_rfn).as_str());
                need_sep = true;
            }
        }
        out
    }

    pub fn has_spec(&self) -> bool {
        self.has_spec
    }

    fn uncurry_typed_binders<'a, F>(v: F) -> (CoqPattern, CoqType)
    where
        F: IntoIterator<Item = &'a (CoqName, CoqType)>,
    {
        let mut v = v.into_iter().peekable();
        if v.peek().is_none() {
            ("_".to_string(), CoqType::Literal("unit".to_string()))
        } else {
            let mut pattern = String::with_capacity(100);
            let mut types = String::with_capacity(100);

            pattern.push_str("(");
            types.push_str("(");
            let mut need_sep = false;
            for (name, t) in v.into_iter() {
                if need_sep {
                    pattern.push_str(", ");
                    types.push_str(" * ");
                }
                pattern.push_str(format!("{}", name).as_str());
                types.push_str(format!("{}", t).as_str());
                need_sep = true;
            }
            pattern.push_str(")");
            types.push_str(")");
            (pattern, CoqType::Literal(types))
        }
    }
}

impl<'def> Display for FunctionSpec<'def> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        /* Definition type_of_[name] [coq_params] :
           fn(∀ [lft_pat] : [lft_count] | [param_pat] : [param_type]; [elctx]; [args]; [pre])
               → ∃ [exist_pat] : [exist_type], [ret_type]; [post]
        */

        let mut lft_pattern = String::with_capacity(100);
        write!(lft_pattern, "(()")?;
        for name in self.lifetimes.iter() {
            write!(lft_pattern, ", ")?;
            write!(lft_pattern, "{}", name)?;
        }
        write!(lft_pattern, ")")?;

        let param = Self::uncurry_typed_binders(self.params.iter().chain(self.ty_params.iter()));
        let existential = Self::uncurry_typed_binders(&self.existentials);

        write!(f, "Definition {} {} :=\n", self.spec_name, self.format_coq_params().as_str())?;
        write!(
            f,
            "  fn(∀ {} : {} | {} : {}, ({}); ",
            lft_pattern,
            self.lifetimes.len(),
            param.0,
            param.1,
            self.format_elctx().as_str()
        )?;
        if self.args.len() == 0 {
            write!(f, "(λ π : thread_id, {}))\n", self.pre)?;
        } else {
            write!(f, "{}; (λ π : thread_id, {}))\n", self.format_args().as_str(), self.pre)?;
        }
        write!(
            f,
            "    → ∃ {} : {}, {}; (λ π : thread_id, {}).",
            existential.0, existential.1, self.ret, self.post
        )?;
        Ok(())
    }
}

// architecture:
// - this should be largely independent of the spec interface provided to the user, i.e. should be relatively
//   low-level
// - should be flexible enough to be later on used for more natural specs.
#[derive(Debug)]
pub struct FunctionSpecBuilder<'def> {
    /// Coq-level parameters the typing statement needs, bool is true if implicit
    coq_params: Vec<CoqParam>,
    late_coq_params: Vec<CoqParam>,

    lifetimes: Vec<Lft>,
    params: Vec<(CoqName, CoqType)>,
    ty_params: Vec<(CoqName, CoqType)>,
    elctx: Vec<ExtLftConstr>,
    pre: IProp,
    args: Vec<TypeWithRef<'def>>,
    existential: Vec<(CoqName, CoqType)>,
    ret: Option<TypeWithRef<'def>>,
    post: IProp,

    coq_names: HashSet<String>,

    /// true iff there are any annotations
    has_spec: bool,
}

impl<'def> FunctionSpecBuilder<'def> {
    pub fn new() -> Self {
        Self {
            coq_params: Vec::new(),
            late_coq_params: Vec::new(),
            lifetimes: Vec::new(),
            params: Vec::new(),
            ty_params: Vec::new(),
            elctx: Vec::new(),
            pre: IProp::Sep(Vec::new()),
            args: Vec::new(),
            existential: Vec::new(),
            ret: None,
            post: IProp::Sep(Vec::new()),
            coq_names: HashSet::new(),
            //ty_params: Vec::new(),
            has_spec: false,
        }
    }

    fn push_coq_name(&mut self, name: &CoqName) {
        if let CoqName::Named(ref name) = name {
            self.coq_names.insert(name.to_string());
        }
    }

    /// Adds a (universally-quantified) parameter with a given Coq name for the spec.
    pub fn add_param(&mut self, name: CoqName, t: CoqType) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.push_coq_name(&name);
        self.params.push((name, t));
        Ok(())
    }

    /// Add a lifetime parameter.
    pub fn add_lifetime(&mut self, name: Lft) -> Result<(), String> {
        let cname = CoqName::Named(name.clone());
        self.ensure_coq_not_bound(&cname)?;
        self.push_coq_name(&cname);
        self.lifetimes.push(name);
        Ok(())
    }

    /// Add a type parameter.
    pub fn add_ty_param(&mut self, name: CoqName, t: CoqType) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.push_coq_name(&name);
        self.ty_params.push((name, t));
        Ok(())
    }

    /// Add a Coq type annotation for a parameter when no type is currently known.
    /// This can e.g. be used to later on add knowledge about the type of a refinement.
    pub fn add_param_type_annot(&mut self, name: &CoqName, t: CoqType) -> Result<(), String> {
        for (name0, t0) in self.params.iter_mut() {
            if *name0 == *name {
                match *t0 {
                    CoqType::Infer => {
                        *t0 = t;
                    },
                    _ => (),
                }
                return Ok(());
            }
        }
        Err("could not find name".to_string())
    }

    fn ensure_coq_bound(&self, name: &str) -> Result<(), String> {
        if !self.coq_names.contains(name) { Err(format!("Unbound Coq name {} ", name)) } else { Ok(()) }
    }

    fn ensure_coq_not_bound(&self, name: &CoqName) -> Result<(), String> {
        if let CoqName::Named(ref name) = name {
            if self.coq_names.contains(name) {
                return Err(format!("Coq name is already bound: {}", name));
            }
        }
        Ok(())
    }

    /// Add a Coq-level param that comes before the type parameters.
    pub fn add_coq_param(&mut self, name: CoqName, t: CoqType, implicit: bool) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.coq_params.push(CoqParam::new(name, t, implicit));
        Ok(())
    }

    /// Add a Coq-level param that comes after the type parameters.
    pub fn add_late_coq_param(&mut self, name: CoqName, t: CoqType, implicit: bool) -> Result<(), String> {
        self.ensure_coq_not_bound(&name)?;
        self.late_coq_params.push(CoqParam::new(name, t, implicit));
        Ok(())
    }

    /// Variant of [add_coq_param] that can never fail and makes the parameter anonymous.
    pub fn add_unnamed_coq_param(&mut self, t: CoqType, implicit: bool) {
        self.coq_params.push(CoqParam::new(CoqName::Unnamed, t, implicit));
    }

    /// Variant of [add_late_coq_param] that can never fail and makes the parameter anonymous.
    pub fn add_unnamed_late_coq_param(&mut self, t: CoqType, implicit: bool) {
        self.late_coq_params.push(CoqParam::new(CoqName::Unnamed, t, implicit));
    }

    /// Add a new universal lifetime constraint.
    pub fn add_lifetime_constraint(&mut self, lft1: UniversalLft, lft2: UniversalLft) -> Result<(), String> {
        if let UniversalLft::Local(ref s) = lft1 {
            let _ = self.ensure_coq_bound(s)?;
        }
        if let UniversalLft::Local(ref s) = lft2 {
            let _ = self.ensure_coq_bound(s)?;
        }
        self.elctx.push((lft1, lft2));
        Ok(())
    }

    /// Add a new function argument.
    pub fn add_arg(&mut self, arg: TypeWithRef<'def>) -> Result<(), String> {
        self.args.push(arg);
        Ok(())
    }

    /// Prepend a precondition. This will be the new precondition to be inserted first.
    /// Use only when the position of the precondition absolutely matters.
    pub fn prepend_precondition(&mut self, pre: IProp) -> Result<(), String> {
        if let IProp::Sep(v) = &mut self.pre {
            v.insert(0, pre);
        } else {
            //self.pre  = IProp::Sep(vec![self.pre, pre]);
            panic!();
        }
        Ok(())
    }

    /// Add a new (separating) conjunct to the function's precondition.
    pub fn add_precondition(&mut self, pre: IProp) -> Result<(), String> {
        if let IProp::Sep(v) = &mut self.pre {
            v.push(pre);
        } else {
            //self.pre  = IProp::Sep(vec![self.pre, pre]);
            panic!();
        }
        Ok(())
    }

    /// Add a new (separating) conjunct to the function's postcondition.
    pub fn add_postcondition(&mut self, post: IProp) -> Result<(), String> {
        if let IProp::Sep(v) = &mut self.post {
            v.push(post);
        } else {
            //self.post  = IProp::Sep(vec![self.post, post]);
            panic!();
        }
        Ok(())
    }

    /// Set the return type of the function
    pub fn set_ret_type(&mut self, ret: TypeWithRef<'def>) -> Result<(), String> {
        if let Some(_) = self.ret {
            return Err("Re-definition of return type".to_string());
        }
        self.ret = Some(ret);
        Ok(())
    }

    /// Add an existentially-quantified variable to the postcondition.
    pub fn add_existential(&mut self, name: CoqName, t: CoqType) -> Result<(), String> {
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

    /// Generate an actual function spec.
    /// `name` is the designated name of the function.
    /// `code_params` are the parameters the code body needs to be provided (e.g., locations of
    /// other functions).
    pub fn into_function_spec(mut self, name: &str, spec_name: &str) -> FunctionSpec<'def> {
        self.coq_params.extend(self.late_coq_params.into_iter());
        let ret = self.ret.unwrap_or(TypeWithRef::make_unit());
        FunctionSpec {
            function_name: name.to_string(),
            spec_name: spec_name.to_string(),
            coq_params: self.coq_params,
            lifetimes: self.lifetimes,
            params: self.params,
            ty_params: self.ty_params,
            elctx: self.elctx,
            pre: self.pre,
            args: self.args,
            existentials: self.existential,
            ret,
            post: self.post,
            has_spec: self.has_spec,
        }
    }
}
