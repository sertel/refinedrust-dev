// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Provides the Coq AST for code and specifications as well as utilities for
/// constructing them.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{Display, Formatter, Write as fWrite};
use std::io::Write;
use std::{fmt, io};

use indent_write::io::IndentWriter;
use log::info;

use crate::specs::*;

fn make_indent(i: usize) -> String {
    " ".repeat(i)
}

fn fmt_list<H>(f: &mut Formatter<'_>, elems: H, sep: &str, wrap: &str) -> fmt::Result
where
    H: IntoIterator,
    H::Item: Display,
{
    let mut needs_sep = false;
    for e in elems.into_iter() {
        if needs_sep {
            write!(f, "{}", sep)?;
        }
        needs_sep = true;
        write!(f, "{}{}{}", wrap, e, wrap)?;
    }
    Ok(())
}

fn fmt_option<H>(f: &mut Formatter<'_>, o: &Option<H>) -> fmt::Result
where
    H: Display,
{
    match o {
        Some(h) => write!(f, "Some ({})", h),
        None => write!(f, "None"),
    }
}

/// A representation of syntactic Rust types that we can use in annotations for the RefinedRust
/// type system.
#[derive(Debug, Clone, PartialEq)]
pub enum RustType {
    Lit(Vec<String>, Vec<RustType>),
    TyVar(String),
    Int(IntType),
    Bool,
    Char,
    Unit,
    MutRef(Box<RustType>, Lft),
    ShrRef(Box<RustType>, Lft),
    PrimBox(Box<RustType>),
    Struct(String, Vec<RustType>),
    Array(usize, Box<RustType>),
}

impl Display for RustType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(path, rhs) => {
                write!(f, "RSTLitType [")?;
                fmt_list(f, path, "; ", "\"")?;
                write!(f, "] [")?;
                fmt_list(f, rhs, "; ", "")?;
                write!(f, "]")
            },
            Self::TyVar(var) => {
                write!(f, "RSTTyVar \"{}\"", var)
            },
            Self::Int(it) => {
                write!(f, "RSTInt {}", it)
            },
            Self::Bool => {
                write!(f, "RSTBool")
            },
            Self::Char => {
                write!(f, "RSTChar")
            },
            Self::Unit => {
                write!(f, "RSTUnit")
            },
            Self::MutRef(ty, lft) => {
                write!(f, "RSTRef Mut \"{}\" ({})", lft, ty)
            },
            Self::ShrRef(ty, lft) => {
                write!(f, "RSTRef Shr \"{}\" ({})", lft, ty)
            },
            Self::PrimBox(ty) => {
                write!(f, "RSTBox ({})", ty)
            },
            Self::Struct(sls, tys) => {
                write!(f, "RSTStruct ({}) [", sls)?;
                fmt_list(f, tys, "; ", "")?;
                write!(f, "]")
            },
            Self::Array(len, ty) => {
                write!(f, "RSTArray {} ({})", len, ty)
            },
        }
    }
}

impl RustType {
    pub fn of_type<'def>(ty: &Type<'def>, env: &[Option<LiteralTyParam>]) -> Self {
        info!("Translating rustType: {:?}", ty);
        match ty {
            Type::Var(var) => {
                // this must be a generic type variable
                let ty = env.get(*var).unwrap().as_ref().unwrap();
                Self::TyVar(ty.rust_name.clone())
            },
            Type::Int(it) => Self::Int(it.clone()),
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,
            Type::MutRef(ty, lft) => {
                let ty = Self::of_type(ty, env);
                Self::MutRef(Box::new(ty), lft.clone())
            },
            Type::ShrRef(ty, lft) => {
                let ty = Self::of_type(ty, env);
                Self::ShrRef(Box::new(ty), lft.clone())
            },
            Type::BoxType(ty) => {
                let ty = Self::of_type(ty, env);
                Self::PrimBox(Box::new(ty))
            },
            Type::Struct(as_use) => {
                let is_raw = as_use.is_raw();
                if let Some(def) = as_use.def {
                    // translate type parameter instantiations
                    let typarams: Vec<_> =
                        as_use.ty_params.iter().map(|ty| RustType::of_type(ty, env)).collect();
                    let def = def.borrow();
                    let def = def.as_ref().unwrap();
                    let ty_name = if is_raw {
                        def.plain_ty_name().to_string()
                    } else {
                        def.public_type_name().to_string()
                    };
                    Self::Lit(vec![ty_name], typarams)
                } else {
                    Self::Unit
                }
            },
            Type::Enum(ae_use) => {
                let typarams: Vec<_> = ae_use.ty_params.iter().map(|ty| RustType::of_type(ty, env)).collect();
                let def = ae_use.def.borrow();
                let def = def.as_ref().unwrap();
                Self::Lit(vec![def.public_type_name().to_string()], typarams)
            },
            Type::LiteralParam(lit) => Self::TyVar(lit.rust_name.clone()),
            Type::Literal(lit) => {
                let typarams: Vec<_> = lit.params.iter().map(|ty| RustType::of_type(ty, env)).collect();
                Self::Lit(vec![lit.def.type_term.clone()], typarams)
            },
            Type::Uninit(_) => {
                panic!("RustType::of_type: uninit is not a Rust type");
            },
            Type::Unit => Self::Unit,
            Type::Never => {
                panic!("RustType::of_type: cannot translate Never type");
            },
            Type::RawPtr => Self::Lit(vec!["alias_ptr_t".to_string()], vec![]),
        }
    }
}

/**
 * Caesium literals.
 *
 * This is much more constrained than the Coq version of values, as we do not need to represent
 * runtime values.
 */
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    LitI8(i8),
    LitI16(i16),
    LitI32(i32),
    LitI64(i64),
    LitI128(i128),
    LitU8(u8),
    LitU16(u16),
    LitU32(u32),
    LitU64(u64),
    LitU128(u128),
    LitBool(bool),
    // dummy literal for ZST values (e.g. ())
    LitZST,
    //TODO: add chars
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut format_int = |i: String, it: IntType| write!(f, "I2v ({}) {}", i.as_str(), it);
        match self {
            Self::LitI8(i) => format_int(i.to_string(), IntType::I8),
            Self::LitI16(i) => format_int(i.to_string(), IntType::I16),
            Self::LitI32(i) => format_int(i.to_string(), IntType::I32),
            Self::LitI64(i) => format_int(i.to_string(), IntType::I64),
            Self::LitI128(i) => format_int(i.to_string(), IntType::I128),
            Self::LitU8(i) => format_int(i.to_string(), IntType::U8),
            Self::LitU16(i) => format_int(i.to_string(), IntType::U16),
            Self::LitU32(i) => format_int(i.to_string(), IntType::U32),
            Self::LitU64(i) => format_int(i.to_string(), IntType::U64),
            Self::LitU128(i) => format_int(i.to_string(), IntType::U128),
            Self::LitBool(b) => write!(f, "val_of_bool {}", b.to_string()),
            Self::LitZST => write!(f, "zst_val"),
        }
    }
}

/**
 * Caesium expressions
 */
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    /// a Coq-level parameter with a given Coq name
    MetaParam(String),
    Literal(Literal),
    UnOp {
        o: Unop,
        ot: OpType,
        e: Box<Expr>,
    },
    BinOp {
        o: Binop,
        ot1: OpType,
        ot2: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
    },
    // dereference an lvalue
    Deref {
        ot: OpType,
        e: Box<Expr>,
    },
    // lvalue to rvalue conversion
    Use {
        ot: OpType,
        e: Box<Expr>,
    },
    // the borrow-operator to get a reference
    Borrow {
        lft: Lft,
        bk: BorKind,
        ty: Option<RustType>,
        e: Box<Expr>,
    },
    // the address-of operator to get a raw pointer
    AddressOf {
        mt: Mutability,
        e: Box<Expr>,
    },
    Call {
        f: Box<Expr>,
        lfts: Vec<Lft>,
        args: Vec<Expr>,
    },
    If {
        ot: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
        e3: Box<Expr>,
    },
    FieldOf {
        e: Box<Expr>,
        sls: String,
        name: String,
    },
    /// an annotated expression
    Annot {
        a: Annotation,
        e: Box<Expr>,
    },
    StructInitE {
        sls: CoqAppTerm<String>,
        components: Vec<(String, Expr)>,
    },
    EnumInitE {
        els: CoqAppTerm<String>,
        variant: String,
        ty: RustType,
        initializer: Box<Expr>,
    },
    DropE(Box<Expr>),
    /// a box expression for creating a box of a particular type
    BoxE(SynType),
    /// access the discriminant of an enum
    EnumDiscriminant {
        els: String,
        e: Box<Expr>,
    },
    /// access to the data of an enum
    EnumData {
        els: String,
        variant: String,
        e: Box<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(var) => write!(f, "\"{}\"", var),
            Self::MetaParam(param) => write!(f, "{}", param),
            Self::Literal(lit) => lit.fmt(f),
            Self::Use { ot, e } => {
                write!(f, "use{{ {} }} ({})", ot, e)
            },
            Self::Call { f: fe, lfts, args } => {
                write!(f, "CallE {} [", fe.as_ref())?;
                fmt_list(f, lfts, "; ", "\"")?;
                write!(f, "] [@{{expr}} ")?;
                fmt_list(f, args, "; ", "")?;
                write!(f, "]")
            },
            Self::Deref { ot, e } => {
                write!(f, "!{{ {} }} ( {} )", ot, e)
            },
            Self::Borrow { lft, bk, ty, e } => {
                let formatted_bk = bk.caesium_fmt();
                write!(f, "&ref{{ {}, ", formatted_bk)?;
                fmt_option(f, ty)?;
                write!(f, ", \"{}\" }} ({})", lft, e)
            },
            Self::AddressOf { mt, e } => {
                let formatted_mt = mt.caesium_fmt();
                write!(f, "&raw{{ {} }} ({})", formatted_mt, e)
            },
            Self::BinOp {
                o,
                ot1,
                ot2,
                e1,
                e2,
            } => {
                let formatted_o = o.caesium_fmt(ot1, ot2);
                write!(f, "({}) {} ({})", e1, formatted_o.as_str(), e2)
            },
            Self::UnOp { o, ot, e } => {
                write!(f, "UnOp ({o}) ({ot}) ({e})")
            },
            Self::FieldOf { e, sls, name } => {
                //let formatted_ly = ly.caesium_fmt();
                write!(f, "({}) at{{ {} }} \"{}\"", e, sls, name)
            },
            Self::Annot { a, e } => {
                write!(f, "AnnotExpr {} ({}) ({})", a.needs_laters(), a, e)
            },
            Self::BoxE(ly) => {
                write!(f, "box{{{}}}", ly)
            },
            Self::DropE(e) => {
                write!(f, "AnnotExpr 0 DropAnnot ({})", e)
            },
            Self::StructInitE { sls, components } => {
                write!(f, "StructInit {} [", sls)?;
                let mut needs_sep = false;
                for (name, e) in components.into_iter() {
                    if needs_sep {
                        write!(f, "; ")?;
                    }
                    needs_sep = true;
                    write!(f, "(\"{}\", {} : expr)", name, e)?;
                }
                write!(f, "]")
            },
            Self::EnumInitE {
                els,
                variant,
                ty,
                initializer,
            } => {
                write!(f, "EnumInit {} \"{}\" ({}) ({})", els, variant, ty, initializer)
            },
            Self::EnumDiscriminant { els, e } => {
                write!(f, "EnumDiscriminant ({els}) ({e})")
            },
            Self::EnumData { els, variant, e } => {
                write!(f, "EnumData ({els}) \"{variant}\" ({e})")
            },
            Self::If { ot, e1, e2, e3 } => {
                write!(f, "IfE ({ot}) ({e1}) ({e2}) ({e3})")
            },
        }
    }
}

/// for unique/shared pointers
#[derive(Debug, Clone, PartialEq)]
pub enum Mutability {
    Mut,
    Shared,
}
impl Mutability {
    fn caesium_fmt(&self) -> String {
        match self {
            Self::Mut => "Mut".to_string(),
            Self::Shared => "Shr".to_string(),
        }
    }
}

/**
 * Borrows allowed in Caesium
 */
#[derive(Debug, Clone, PartialEq)]
pub enum BorKind {
    Mutable,
    Shared,
}
impl BorKind {
    fn caesium_fmt(&self) -> String {
        match self {
            Self::Mutable => "Mut".to_string(),
            Self::Shared => "Shr".to_string(),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum LftNameTree {
    Leaf,
    Ref(Lft, Box<LftNameTree>),
    // TODO structs etc
}

impl fmt::Display for LftNameTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf => {
                write!(f, "LftNameTreeLeaf")
            },
            Self::Ref(lft, t) => {
                write!(f, "LftNameTreeRef \"{}\" (", lft)?;
                t.fmt(f)?;
                write!(f, ")")
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Annotation {
    /// Start a lifetime as a sublifetime of the intersection of a few other lifetimes
    StartLft(Lft, Vec<Lft>),
    /// End this lifetime
    EndLft(Lft),
    /// Extend this lifetime by making the directly owned part static
    ExtendLft(Lft),
    /// Dynamically include a lifetime in another lifetime
    DynIncludeLft(Lft, Lft),
    /// Shorten the lifetime of an object to the given lifetimes, according to the name map
    ShortenLft(LftNameTree),
    /// add naming for the lifetimes in the type of the expression to the name context,
    /// at the given names
    GetLftNames(LftNameTree),
    /// Copy a lft name map entry from lft1 to lft2
    CopyLftName(Lft, Lft),
    /// Create an alias for an intersection of lifetimes
    AliasLftIntersection(Lft, Vec<Lft>),
    /// The following Goto will enter a loop
    EnterLoop,
}
impl fmt::Display for Annotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StartLft(l, sup) => {
                write!(f, "StartLftAnnot \"{}\" [", l)?;
                fmt_list(f, sup, "; ", "\"")?;
                write!(f, "]")
            },
            Self::EndLft(l) => {
                write!(f, "EndLftAnnot \"{}\"", l)
            },
            Self::ExtendLft(l) => {
                write!(f, "ExtendLftAnnot \"{}\"", l)
            },
            Self::DynIncludeLft(l1, l2) => {
                write!(f, "DynIncludeLftAnnot \"{}\" \"{}\"", l1, l2)
            },
            Self::ShortenLft(name) => {
                write!(f, "ShortenLftAnnot ({})", name)
            },
            Self::GetLftNames(name) => {
                write!(f, "GetLftNamesAnnot ({})", name)
            },
            Self::CopyLftName(lft1, lft2) => {
                write!(f, "CopyLftNameAnnot \"{}\" \"{}\"", lft2, lft1)
            },
            Self::AliasLftIntersection(lft, lfts) => {
                write!(f, "AliasLftAnnot {} [", lft)?;
                fmt_list(f, lfts, "; ", "\"")?;
                write!(f, "]")
            },
            Self::EnterLoop => {
                write!(f, "EnterLoopAnnot")
            },
        }
    }
}

impl Annotation {
    pub(crate) fn needs_laters(&self) -> u32 {
        match self {
            Self::ShortenLft { .. } => 0,
            _ => 0,
        }
    }
}

type BlockLabel = usize;

pub enum Stmt {
    GotoBlock(BlockLabel),
    Return(Expr),
    If {
        ot: OpType,
        e: Expr,
        s1: Box<Stmt>,
        s2: Box<Stmt>,
    },
    Switch {
        // e needs to evaluate to an integer/variant index used as index to bs
        e: Expr,
        it: IntType,
        index_map: HashMap<u128, usize>,
        bs: Vec<Stmt>,
        def: Box<Stmt>,
    },
    Assign {
        ot: OpType,
        e1: Expr,
        e2: Expr,
        s: Box<Stmt>,
    },
    ExprS {
        e: Expr,
        s: Box<Stmt>,
    },
    AssertS {
        e: Expr,
        s: Box<Stmt>,
    },
    Annot {
        a: Annotation,
        s: Box<Stmt>,
    },
    Stuck,
}

impl Stmt {
    fn caesium_fmt(&self, indent: usize) -> String {
        let ind = make_indent(indent);
        let ind = ind.as_str();
        match self {
            Stmt::GotoBlock(block) => {
                format!("{ind}Goto \"_bb{}\"", block)
            },
            Stmt::Return(e) => {
                format!("{ind}return ({})", e)
            },
            Stmt::Assign { ot, e1, e2, s } => {
                let formatted_s = s.caesium_fmt(indent);

                format!("{ind}{} <-{{ {} }} {};\n{}", e1, ot, e2, formatted_s.as_str())
            },
            Stmt::ExprS { e, s } => {
                let formatted_s = s.caesium_fmt(indent);
                format!("{ind}expr: {};\n{}", e, formatted_s.as_str())
            },
            Stmt::Annot { a, s } => {
                let formatted_s = s.caesium_fmt(indent);
                format!("{ind}annot: {};\n{}", a, formatted_s.as_str())
            },
            Stmt::If { ot, e, s1, s2 } => {
                let formatted_s1 = s1.caesium_fmt(indent + 1);
                let formatted_s2 = s2.caesium_fmt(indent + 1);
                format!(
                    "{ind}if{{ {} }}: {} then\n{}\n{ind}else\n{}",
                    ot,
                    e,
                    formatted_s1.as_str(),
                    formatted_s2.as_str()
                )
            },
            Stmt::AssertS { e, s } => {
                let formatted_s = s.caesium_fmt(indent);
                format!("{ind}assert{{ {} }}: {};\n{}", OpType::BoolOp, e, formatted_s)
            },
            Stmt::Stuck => {
                format!("{ind}StuckS")
            },
            Stmt::Switch {
                e,
                it,
                index_map,
                bs,
                def,
            } => {
                let mut fmt_index_map = String::with_capacity(100);
                for (k, v) in index_map.iter() {
                    write!(fmt_index_map, "<[ {k}%Z := {v}%nat ]> $ ").unwrap();
                }
                write!(fmt_index_map, "∅").unwrap();

                let mut fmt_targets = String::with_capacity(100);
                write!(fmt_targets, "[").unwrap();
                let mut need_sep = false;
                for tgt in bs {
                    if need_sep {
                        write!(fmt_targets, "; ").unwrap();
                    }
                    need_sep = true;
                    write!(fmt_targets, "{}", tgt.caesium_fmt(0)).unwrap();
                }
                write!(fmt_targets, "]").unwrap();

                let fmt_default = def.caesium_fmt(0);

                format!(
                    "{ind}Switch ({it} : int_type) ({e}) ({fmt_index_map}) ({fmt_targets}) ({fmt_default})"
                )
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Unop {
    NegOp,
    NotBoolOp,
    NotIntOp,
}
impl Display for Unop {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::NegOp => write!(f, "NegOp"),
            Self::NotBoolOp => write!(f, "NotBoolOp"),
            Self::NotIntOp => write!(f, "NotIntOp"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binop {
    //arithmetic
    AddOp,
    SubOp,
    MulOp,
    DivOp,
    ModOp,
    // logical
    AndOp,
    OrOp,
    //bitwise
    BitAndOp,
    BitOrOp,
    BitXorOp,
    ShlOp,
    ShrOp,
    // comparison
    EqOp,
    NeOp,
    LtOp,
    GtOp,
    LeOp,
    GeOp,
    // pointer operations
    PtrOffsetOp(Layout),
    PtrNegOffsetOp(Layout),
    PtrDiffOp(Layout),
    // checked ops
    CheckedAddOp,
    CheckedSubOp,
    CheckedMulOp,
}
impl Binop {
    fn caesium_fmt(&self, ot1: &OpType, ot2: &OpType) -> String {
        let format_prim = |st: &str| format!("{} {} , {} }}", st, ot1, ot2);
        let format_bool = |st: &str| format!("{} {} , {} , {} }}", st, ot1, ot2, BOOL_REPR);

        match self {
            Self::AddOp => format_prim("+{"),
            Self::SubOp => format_prim("-{"),
            Self::MulOp => format_prim("×{"),
            Self::CheckedAddOp => format_prim("+c{"),
            Self::CheckedSubOp => format_prim("-c{"),
            Self::CheckedMulOp => format_prim("×c{"),
            Self::DivOp => format_prim("/{"),
            Self::ModOp => format_prim("%{"),
            Self::AndOp => format_bool("&&{"),
            Self::OrOp => format_bool("||{"),
            Self::BitAndOp => format_prim("&b{"),
            Self::BitOrOp => format_prim("|{"),
            Self::BitXorOp => format_prim("^{"),
            Self::ShlOp => format_prim("<<{"),
            Self::ShrOp => format_prim(">>{"),
            Self::EqOp => format_bool("= {"),
            Self::NeOp => format_bool("!= {"),
            Self::LtOp => format_bool("<{"),
            Self::GtOp => format_bool(">{"),
            Self::LeOp => format_bool("≤{"),
            Self::GeOp => format_bool("≥{"),
            Self::PtrOffsetOp(ly) => format!("at_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrNegOffsetOp(ly) => format!("at_neg_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrDiffOp(ly) => format!("sub_ptr{{ {} , {} , {} }}", ly, ot1, ot2),
        }
    }
}

/// Representation of a Caesium function's source code
pub struct FunctionCode {
    name: String,
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,

    /// Coq parameters that the function is parameterized over
    required_parameters: Vec<(CoqName, CoqType)>,
}

fn make_map_string(sep0: &str, sep: &str, els: Vec<(String, String)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els.iter() {
        out.push_str(sep);

        out.push_str(format!("<[{sep}\"{}\" :={}{}{}]>%E $", key, sep0, value, sep).as_str());
    }
    out.push_str(sep);
    out.push_str("∅");
    out
}

fn make_lft_map_string(els: Vec<(String, String)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els.iter() {
        out.push_str(format!("named_lft_update \"{}\" {} $ ", key, value).as_str());
    }
    out.push_str("∅");
    out
}

impl FunctionCode {
    const INITIAL_BB: usize = 0;

    pub fn caesium_fmt(&self) -> String {
        // format args
        let format_stack_layout = |layout: std::slice::Iter<'_, (String, SynType)>| {
            let mut formatted_args: String = String::with_capacity(100);
            formatted_args.push_str("[");
            let mut insert_sep = false;
            for (ref name, ref st) in layout {
                if insert_sep {
                    formatted_args.push_str(";");
                }
                let ly = st.layout_term(&[]); //should be closed already
                formatted_args.push_str("\n");
                formatted_args.push_str(make_indent(2).as_str());

                formatted_args.push_str(format!("(\"{}\", {} : layout)", name, ly).as_str());

                insert_sep = true;
            }
            formatted_args.push_str(format!("\n{}]", make_indent(1).as_str()).as_str());
            return formatted_args;
        };

        let mut formatted_args = String::with_capacity(100);
        formatted_args.push_str(
            format!(
                "{}f_args := {}",
                make_indent(1),
                format_stack_layout(self.stack_layout.iter_args()).as_str()
            )
            .as_str(),
        );

        let mut formatted_locals = String::with_capacity(100);
        formatted_locals.push_str(
            format!(
                "{}f_local_vars := {}",
                make_indent(1),
                format_stack_layout(self.stack_layout.iter_locals()).as_str()
            )
            .as_str(),
        );

        let formatted_bb = make_map_string(
            "\n",
            format!("\n{}", make_indent(2).as_str()).as_str(),
            self.basic_blocks
                .iter()
                .map(|(name, bb)| (format!("_bb{name}"), bb.caesium_fmt(3)))
                .collect(),
        );

        if self.basic_blocks.len() < 1 {
            panic!("Function has no basic block");
        }
        let formatted_init = format!("{}f_init := \"_bb{}\"", make_indent(1).as_str(), Self::INITIAL_BB);

        // format Coq parameters
        let mut formatted_params = String::with_capacity(20);
        let mut sorted_params = self.required_parameters.clone();
        sorted_params.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (ref name, ref ty) in sorted_params.iter() {
            formatted_params.push_str(format!(" ({} : {})", name, ty).as_str());
        }

        format!(
            "Definition {}_def{} : function := {{|\n{};\n{};\n{}f_code := {};\n{};\n|}}.",
            self.name.as_str(),
            formatted_params.as_str(),
            formatted_args.as_str(),
            formatted_locals.as_str(),
            make_indent(1).as_str(),
            formatted_bb.as_str(),
            formatted_init.as_str()
        )
    }

    /// Get the number of arguments of the function.
    pub fn get_argument_count(&self) -> usize {
        self.stack_layout.iter_args().len()
    }
}

/**
 * Maintain necessary info to map MIR places to Caesium stack variables.
 */
pub struct StackMap {
    arg_map: Vec<(String, SynType)>,
    local_map: Vec<(String, SynType)>,
    used_names: HashSet<String>,
}

impl StackMap {
    pub fn new() -> Self {
        let local_map = Vec::new();
        let arg_map = Vec::new();
        let names = HashSet::new();

        StackMap {
            arg_map,
            local_map,
            used_names: names,
        }
    }

    pub fn insert_local(&mut self, name: String, st: SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.to_string());
        self.local_map.push((name, st));
        true
    }

    pub fn insert_arg(&mut self, name: String, st: SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.to_string());
        self.arg_map.push((name, st));
        true
    }

    pub fn lookup_binding(&self, name: &str) -> Option<&SynType> {
        if !self.used_names.contains(name) {
            return None;
        }
        for (nm, st) in &self.local_map {
            if nm == name {
                return Some(st);
            }
        }
        for (nm, st) in &self.arg_map {
            if nm == name {
                return Some(st);
            }
        }
        panic!("StackMap: invariant violation");
    }

    pub fn iter_args(&self) -> std::slice::Iter<'_, (String, SynType)> {
        self.arg_map.iter()
    }

    pub fn iter_locals(&self) -> std::slice::Iter<'_, (String, SynType)> {
        self.local_map.iter()
    }
}

/// Builder for a FunctionCode.
pub struct FunctionCodeBuilder {
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,
}

impl FunctionCodeBuilder {
    pub fn new() -> FunctionCodeBuilder {
        FunctionCodeBuilder {
            stack_layout: StackMap::new(),
            basic_blocks: BTreeMap::new(),
        }
    }

    pub fn add_argument(&mut self, name: &str, st: SynType) {
        self.stack_layout.insert_arg(name.to_string(), st);
    }

    pub fn add_local(&mut self, name: &str, st: SynType) {
        self.stack_layout.insert_local(name.to_string(), st);
    }

    pub fn add_basic_block(&mut self, index: usize, bb: Stmt) {
        self.basic_blocks.insert(index, bb);
    }

    /// Initialize a local lifetime at the start of the function
    /// (i.e., prepend the initialization statementto the first block of the function)
    pub fn initialize_local_lifetime(&mut self, lft: Lft, outliving: Vec<Lft>) {
        let bb0 = self.basic_blocks.remove(&FunctionCode::INITIAL_BB).unwrap();
        let cont_stmt = Stmt::Annot {
            a: Annotation::StartLft(format!("{}", lft), outliving),
            s: Box::new(bb0),
        };
        self.basic_blocks.insert(FunctionCode::INITIAL_BB, cont_stmt);
    }
}

#[derive(Debug, Clone)]
struct InvariantMap(HashMap<usize, LoopSpec>);

impl Display for InvariantMap {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        // PolyCons (bb, wrap_inv inv) $ ... $ PolyNil
        write!(f, "(")?;
        for (bb, spec) in self.0.iter() {
            write!(f, "PolyCons  ({}, wrap_inv ({})) $ ", bb, spec.func_predicate)?;
        }
        write!(f, "PolyNil)")
    }
}

/// A Caesium function bundles up the Caesium code itself as well as the generated specification
/// for it.
pub struct Function<'def> {
    pub code: FunctionCode,
    pub spec: FunctionSpec<'def>,
    /// Generic types in scope for this function
    generic_types: Vec<LiteralTyParam>,

    /// Other functions that are used by this one.
    other_functions: Vec<(String, String, Vec<Type<'def>>, Vec<SynType>)>,
    /// Syntypes that we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<SynType>,
    /// Custom tactics for the generated proof
    manual_tactics: Vec<String>,

    /// invariants for loop head bbs
    loop_invariants: InvariantMap,
}

impl<'def> Function<'def> {
    /// Get the name of the function.
    pub fn name(&self) -> &str {
        &self.code.name
    }

    pub fn generate_lemma_statement<F>(&self, f: &mut F) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        // indent
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        let f = &mut writer;

        writeln!(f, "Definition {}_lemma (π : thread_id) : Prop :=", self.name())?;

        // write coq parameters
        if !self.spec.coq_params.is_empty() || !self.other_functions.is_empty() {
            write!(f, "∀ ")?;
            for param in self.spec.coq_params.iter() {
                // TODO use CoqParam::format instead
                if param.implicit {
                    write!(f, "`({})", param.ty)?;
                } else {
                    write!(f, "({} : {})", param.name, param.ty)?;
                }
                write!(f, " ")?;
            }

            // assume locations for other functions
            for (loc_name, _, _, _) in self.other_functions.iter() {
                write!(f, "({} : loc) ", loc_name)?;
            }
            writeln!(f, ", ")?;
        }

        // assume Coq assumptions
        for st in self.layoutable_syntys.iter() {
            write!(f, "syn_type_is_layoutable ({}) →\n", st)?;
        }

        // write iris assums
        if self.other_functions.len() == 0 {
            write!(f, "⊢ ")?;
        } else {
            for (loc_name, spec_name, param_insts, sts) in self.other_functions.iter() {
                info!("Using other function: {:?} with insts: {:?}", spec_name, param_insts);
                // generate an instantiation for the generic type arguments, by getting the refinement types
                // which need to be passed at the Coq level
                let mut gen_rfn_type_inst = Vec::new();
                for p in param_insts.iter() {
                    // use an empty env, these should be closed in the current environment
                    let rfn = p.get_rfn_type(&[]);
                    gen_rfn_type_inst.push(format!("({})", rfn.to_string()));
                    let st = p.get_syn_type();
                    gen_rfn_type_inst.push(format!("({})", st.to_string()));
                }
                let arg_syntys: Vec<String> = sts.iter().map(|st| st.to_string()).collect();

                write!(
                    f,
                    "{} ◁ᵥ{{π}} {} @ function_ptr [{}] ({} {}) -∗\n",
                    loc_name,
                    loc_name,
                    arg_syntys.join("; "),
                    spec_name,
                    gen_rfn_type_inst.join(" ")
                )?;
            }
        }

        write!(f, "typed_function π ({}_def ", self.name())?;

        // add arguments for the code definition
        let mut code_params: Vec<_> =
            self.other_functions.iter().map(|(loc_name, _, _, _)| loc_name.clone()).collect();
        for names in self.generic_types.iter() {
            code_params.push(names.syn_type.clone());
        }
        code_params.sort();
        for x in code_params.iter() {
            write!(f, "{}  ", x)?;
        }

        // write local syntypes
        write!(f, ") [")?;
        let mut needs_sep = false;
        for (_, st) in self.code.stack_layout.local_map.iter() {
            if needs_sep {
                write!(f, "; ")?;
            }
            needs_sep = true;
            write!(f, "{}", st)?;
        }

        write!(f, "] (type_of_{} ", self.name())?;

        // write type args (passed to the type definition)
        for param in self.spec.coq_params.iter() {
            if !param.implicit {
                write!(f, "{} ", param.name)?;
            }
        }

        write!(f, ").\n")
    }

    pub fn generate_proof_prelude<F>(&self, f: &mut F) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        // indent
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        let f = &mut writer;

        write!(f, "Ltac {}_prelude :=\n", self.name())?;

        write!(f, "unfold {}_lemma;\n", self.name())?;
        write!(f, "set (FN_NAME := FUNCTION_NAME \"{}\");\n", self.name())?;

        // intros spec params
        if !self.spec.coq_params.is_empty() {
            write!(f, "intros")?;
            for param in self.spec.coq_params.iter() {
                if !param.implicit {
                    write!(f, " {}", param.name)?;
                } else {
                    write!(f, " ?")?;
                }
            }
            writeln!(f, ";")?;
        }

        write!(f, "intros;\n")?;
        write!(f, "iStartProof;\n")?;

        // generate intro pattern for params
        let mut ip_params = String::with_capacity(100);
        let params = &self.spec.params;
        let ty_params = &self.spec.ty_params;
        if !params.is_empty() || !ty_params.is_empty() {
            // product is left-associative
            for _ in 0..(params.len() + ty_params.len() - 1) {
                ip_params.push_str("[ ");
            }

            let mut p_count = 0;
            for (n, _) in params.iter().chain(ty_params.iter()) {
                if p_count > 1 {
                    ip_params.push_str(" ]");
                }
                ip_params.push_str(" ");
                p_count += 1;
                ip_params.push_str(format!("{}", n).as_str());
            }
            for (n, _) in ty_params.iter() {
                write!(f, "let {} := fresh \"{}\" in\n", n, n)?;
            }

            if p_count > 1 {
                ip_params.push_str(" ]");
            }
        } else {
            // no params, but still need to provide something to catch the unit
            // (and no empty intropatterns are allowed)
            ip_params.push_str("?");
        }

        // generate intro pattern for lifetimes
        let mut lft_pattern = String::with_capacity(100);
        // pattern is left-associative
        for _ in 0..self.spec.lifetimes.len() {
            write!(lft_pattern, "[ ").unwrap();
        }
        write!(lft_pattern, "[]").unwrap();
        for lft in self.spec.lifetimes.iter() {
            write!(lft_pattern, " {}]", lft).unwrap();
            write!(f, "let {} := fresh \"{}\" in\n", lft, lft)?;
        }

        write!(
            f,
            "start_function \"{}\" ( {} ) ( {} );\n",
            self.name(),
            lft_pattern.as_str(),
            ip_params.as_str()
        )?;

        write!(f, "set (loop_map := BB_INV_MAP {});\n", self.loop_invariants)?;

        // intro stack locations
        write!(f, "intros")?;
        for (arg, _) in self.code.stack_layout.arg_map.iter() {
            write!(f, " arg_{}", arg)?;
        }
        for (local, _) in self.code.stack_layout.local_map.iter() {
            write!(f, " local_{}", local)?;
        }
        write!(f, ";\n")?;

        // destruct function parameters
        write!(f, "prepare_parameters (")?;
        for (n, _) in params {
            write!(f, " {}", n)?;
        }
        write!(f, " );\n")?;

        // initialize lifetimes
        let formatted_lifetimes =
            make_lft_map_string(self.spec.lifetimes.iter().map(|n| (n.to_string(), n.to_string())).collect());
        write!(f, "init_lfts ({} );\n", formatted_lifetimes.as_str())?;

        // initialize tyvars
        let formatted_tyvars = make_map_string(
            " ",
            " ",
            self.generic_types
                .iter()
                .map(|names| (names.rust_name.to_string(), format!("existT _ ({})", names.type_term)))
                .collect(),
        );

        write!(f, "init_tyvars ({} ).\n", formatted_tyvars.as_str())
    }

    pub fn generate_proof<F>(&self, f: &mut F) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        writeln!(f, "Lemma {}_proof (π : thread_id) :", self.name())?;

        {
            // indent
            let mut writer = IndentWriter::new(BASE_INDENT, &mut *f);
            let f = &mut writer;

            write!(f, "{}_lemma π.", self.name())?;
        }
        write!(f, "\n")?;
        write!(f, "Proof.\n")?;

        {
            let mut writer = IndentWriter::new(BASE_INDENT, &mut *f);
            let f = &mut writer;

            write!(f, "{}_prelude.\n\n", self.name())?;

            write!(f, "repeat liRStep; liShow.\n\n")?;
            write!(f, "all: print_remaining_goal.\n")?;
            write!(f, "Unshelve. all: sidecond_solver.\n")?;
            write!(f, "Unshelve. all: sidecond_hammer.\n")?;

            // add custom tactics specified in annotations
            for tac in self.manual_tactics.iter() {
                if tac.starts_with("all:") {
                    write!(f, "{}\n", tac)?;
                } else {
                    write!(f, "{{ {} all: shelve. }}\n", tac)?;
                }
            }

            write!(f, "Unshelve. all: print_remaining_sidecond.\n")?;
        }

        if rrconfig::admit_proofs() {
            write!(f, "Admitted. (* admitted due to admit_proofs config flag *)\n")?;
        } else {
            write!(f, "Qed.\n")?;
        }
        Ok(())
    }
}

/// A CaesiumFunctionBuilder allows to incrementally construct the functions's code and the spec
/// at the same time. It ensures that both definitions line up in the right way (for instance, by
/// ensuring that other functions are linked up in a consistent way).
pub struct FunctionBuilder<'def> {
    pub code: FunctionCodeBuilder,
    pub spec: FunctionSpecBuilder<'def>,
    spec_name: String,

    /// a sequence of other function names used by this function
    /// (code_loc_name, spec_name, type parameter instantiation)
    /// (Note that there may be multiple assumptions here with the same spec, if they are
    /// monomorphizations of the same function!)
    other_functions: Vec<(String, String, Vec<Type<'def>>, Vec<SynType>)>,
    /// name of this function
    function_name: String,
    /// available refinement types
    /// TODO: may not need this anymore.
    _rfn_types: Vec<CoqType>,
    /// generic types in scope for this function
    generic_types: Vec<LiteralTyParam>,
    /// generic lifetimes
    generic_lifetimes: Vec<(Option<String>, Lft)>,
    /// Syntypes we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<SynType>,

    /// manually specified tactics that will be emitted in the typing proof
    tactics: Vec<String>,

    /// maps loop head bbs to loop specifications
    loop_invariants: InvariantMap,
}

impl<'def> FunctionBuilder<'def> {
    pub fn new(name: &str, spec_name: &str) -> Self {
        let code_builder = FunctionCodeBuilder::new();
        let spec_builder = FunctionSpecBuilder::new();
        FunctionBuilder {
            function_name: name.to_string(),
            spec_name: spec_name.to_string(),
            other_functions: Vec::new(),
            _rfn_types: Vec::new(),
            generic_types: Vec::new(),
            generic_lifetimes: Vec::new(),
            code: code_builder,
            spec: spec_builder,
            layoutable_syntys: Vec::new(),
            loop_invariants: InvariantMap(HashMap::new()),
            tactics: Vec::new(),
        }
    }

    /// Require another function to be available.
    pub fn require_function(
        &mut self,
        loc_name: String,
        spec_name: String,
        params: Vec<Type<'def>>,
        syntypes: Vec<SynType>,
    ) {
        self.other_functions.push((loc_name, spec_name, params, syntypes));
    }

    /// Adds a lifetime parameter to the function.
    pub fn add_universal_lifetime(&mut self, name: Option<String>, lft: Lft) -> Result<(), String> {
        self.generic_lifetimes.push((name, lft.to_string()));
        self.spec.add_lifetime(lft)
    }

    /// Adds a universal lifetime constraint to the function.
    pub fn add_universal_lifetime_constraint(
        &mut self,
        lft1: UniversalLft,
        lft2: UniversalLft,
    ) -> Result<(), String> {
        self.spec.add_lifetime_constraint(lft1, lft2)
    }

    /// Add a manual tactic used for a sidecondition proof.
    pub fn add_manual_tactic(&mut self, tac: &str) {
        self.tactics.push(tac.to_string())
    }

    /// Add a generic type used by this function.
    pub fn add_generic_type(&mut self, t: LiteralTyParam) {
        self.generic_types.push(t);
    }

    /// Get the type parameters.
    pub fn get_ty_params(&self) -> &[LiteralTyParam] {
        &self.generic_types
    }

    /// Get the universal lifetimes.
    pub fn get_lfts(&self) -> Vec<(Option<String>, Lft)> {
        self.generic_lifetimes.clone()
    }

    /// Add the assumption that a particular syntype is layoutable to the typing proof.
    pub fn assume_synty_layoutable(&mut self, st: SynType) {
        assert!(st.is_closed());
        self.layoutable_syntys.push(st);
    }

    /// Register a loop invariant for the basic block [bb].
    /// Should only be called once per bb.
    pub fn register_loop_invariant(&mut self, bb: usize, spec: LoopSpec) {
        if self.loop_invariants.0.insert(bb, spec).is_some() {
            panic!("registered loop invariant multiple times");
        }
    }

    fn add_generics_to_spec(&mut self) {
        // push generic type parameters to the spec builder
        for names in self.generic_types.iter() {
            // TODO(cleanup): this currently regenerates the names for ty + rt, instead of using
            // the existing names
            self.spec
                .add_coq_param(CoqName::Named(names.refinement_type.to_string()), CoqType::Type, false)
                .unwrap();
            self.spec
                .add_coq_param(
                    CoqName::Unnamed,
                    CoqType::Literal(format!("Inhabited {}", names.refinement_type)),
                    true,
                )
                .unwrap();
            self.spec
                .add_coq_param(CoqName::Named(names.syn_type.to_string()), CoqType::SynType, false)
                .unwrap();
            self.spec
                .add_ty_param(
                    CoqName::Named(names.type_term.clone()),
                    CoqType::Ttype(Box::new(CoqType::Literal(names.refinement_type.clone()))),
                )
                .unwrap();

            // Add assumptions that the syntactic type of the semantic argument matches with the
            // assumed syntactic type.
            let st_precond = IProp::Pure(format!("ty_syn_type {} = {}", names.type_term, names.syn_type));
            // We prepend these conditions so that this information can already be used to simplify
            // the other assumptions.
            self.spec.prepend_precondition(st_precond).unwrap();

            // add assumptions that reads/writes to the generic are allowed
            let write_precond = IProp::Pure(format!("ty_allows_writes {}", names.type_term));
            let read_precond = IProp::Pure(format!("ty_allows_reads {}", names.type_term));
            let sc_precond = IProp::Atom(format!("ty_sidecond {}", names.type_term));
            self.spec.add_precondition(write_precond).unwrap();
            self.spec.add_precondition(read_precond).unwrap();
            self.spec.add_precondition(sc_precond).unwrap();
        }
    }
}

impl<'def> Into<Function<'def>> for FunctionBuilder<'def> {
    fn into(mut self) -> Function<'def> {
        // generate location parameters for other functions used by this one.
        let mut parameters: Vec<(CoqName, CoqType)> = self
            .other_functions
            .iter()
            .map(|f_inst| (CoqName::Named(f_inst.0.to_string()), CoqType::Loc))
            .collect();

        // add generic syntype parameters for generics that this function uses.
        let mut gen_st_parameters = self
            .generic_types
            .iter()
            .map(|names| (CoqName::Named(names.syn_type.to_string()), CoqType::SynType))
            .collect();
        parameters.append(&mut gen_st_parameters);

        self.add_generics_to_spec();
        let spec = self.spec.into_function_spec(&self.function_name, &self.spec_name);

        let code = FunctionCode {
            stack_layout: self.code.stack_layout,
            name: self.function_name.clone(),
            basic_blocks: self.code.basic_blocks,
            required_parameters: parameters,
        };

        Function {
            code,
            spec,
            generic_types: self.generic_types,
            other_functions: self.other_functions,
            layoutable_syntys: self.layoutable_syntys,
            loop_invariants: self.loop_invariants,
            manual_tactics: self.tactics,
        }
    }
}

impl<'def> Into<FunctionSpec<'def>> for FunctionBuilder<'def> {
    fn into(mut self) -> FunctionSpec<'def> {
        self.add_generics_to_spec();
        self.spec.into_function_spec(&self.function_name, &self.spec_name)
    }
}
