// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Provides the Coq AST for code and specifications as well as utilities for
/// constructing them.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as fmtWrite;
use std::io::Write as ioWrite;
use std::{fmt, io};

use derive_more::Display;
use indent_write::indentable::Indentable;
use indent_write::io::IndentWriter;
use indoc::{formatdoc, writedoc};
use log::info;

use crate::specs::*;
use crate::{coq, display_list, make_indent, push_str_list, write_list, BASE_INDENT};

fn fmt_comment(o: &Option<String>) -> String {
    match o {
        None => String::new(),
        Some(comment) => format!(" (* {} *)", comment),
    }
}

fn fmt_option<T: Display>(o: &Option<T>) -> String {
    match o {
        None => format!("None"),
        Some(x) => format!("Some ({})", x),
    }
}

/// A representation of syntactic Rust types that we can use in annotations for the `RefinedRust`
/// type system.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum RustType {
    #[display("RSTLitType [{}] [{}]", display_list!(_0, "; ", "\"{}\""), display_list!(_1, "; "))]
    Lit(Vec<String>, Vec<RustType>),

    #[display("RSTTyVar \"{}\"", _0)]
    TyVar(String),

    #[display("RSTInt {}", _0)]
    Int(IntType),

    #[display("RSTBool")]
    Bool,

    #[display("RSTChar")]
    Char,

    #[display("RSTUnit")]
    Unit,

    #[display("RSTRef Mut \"{}\" ({})", _1, &_0)]
    MutRef(Box<RustType>, Lft),

    #[display("RSTRef Shr \"{}\" ({})", _1, &_0)]
    ShrRef(Box<RustType>, Lft),

    #[display("RSTBox ({})", &_0)]
    PrimBox(Box<RustType>),

    #[display("RSTStruct ({}) [{}]", _0, display_list!(_1, "; "))]
    Struct(String, Vec<RustType>),

    #[display("RSTArray {} ({})", _0, &_1)]
    Array(usize, Box<RustType>),
}

impl RustType {
    #[must_use]
    pub fn of_type(ty: &Type<'_>, env: &[Option<LiteralTyParam>]) -> Self {
        info!("Translating rustType: {:?}", ty);
        match ty {
            Type::Var(var) => {
                // this must be a generic type variable
                let ty = env[*var].as_ref().unwrap();
                Self::TyVar(ty.rust_name.clone())
            },

            Type::Int(it) => Self::Int(*it),
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

                let Some(def) = as_use.def else {
                    return Self::Unit;
                };

                // translate type parameter instantiations
                let typarams: Vec<_> = as_use.ty_params.iter().map(|ty| Self::of_type(ty, env)).collect();
                let ty_name = if is_raw { def.plain_ty_name() } else { def.public_type_name() };

                Self::Lit(vec![ty_name.to_string()], typarams)
            },

            Type::Enum(ae_use) => {
                let typarams: Vec<_> = ae_use.ty_params.iter().map(|ty| Self::of_type(ty, env)).collect();

                Self::Lit(vec![ae_use.def.public_type_name().to_string()], typarams)
            },

            Type::LiteralParam(lit) => Self::TyVar(lit.rust_name.clone()),

            Type::Literal(lit) => {
                let typarams: Vec<_> = lit.params.iter().map(|ty| Self::of_type(ty, env)).collect();
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
// TODO: add chars
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Literal {
    #[display("I2v ({}) {}", _0, IntType::I8)]
    LitI8(i8),

    #[display("I2v ({}) {}", _0, IntType::I16)]
    LitI16(i16),

    #[display("I2v ({}) {}", _0, IntType::I32)]
    LitI32(i32),

    #[display("I2v ({}) {}", _0, IntType::I64)]
    LitI64(i64),

    #[display("I2v ({}) {}", _0, IntType::I128)]
    LitI128(i128),

    #[display("I2v ({}) {}", _0, IntType::U8)]
    LitU8(u8),

    #[display("I2v ({}) {}", _0, IntType::U16)]
    LitU16(u16),

    #[display("I2v ({}) {}", _0, IntType::U32)]
    LitU32(u32),

    #[display("I2v ({}) {}", _0, IntType::U64)]
    LitU64(u64),

    #[display("I2v ({}) {}", _0, IntType::U128)]
    LitU128(u128),

    #[display("val_of_bool {}", _0)]
    LitBool(bool),

    /// name of the loc
    #[display("{}", _0)]
    LitLoc(String),

    /// dummy literal for ZST values (e.g. ())
    #[display("zst_val")]
    LitZST,
}

/**
 * Caesium expressions
 */
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Expr {
    #[display("\"{}\"", _0)]
    Var(String),

    /// a Coq-level parameter with a given Coq name
    #[display("{}", _0)]
    MetaParam(String),

    #[display("{}", _0)]
    Literal(Literal),

    #[display("UnOp ({}) ({}) ({})", o, ot, &e)]
    UnOp { o: Unop, ot: OpType, e: Box<Expr> },

    #[display("({}) {} ({})", &e1, o.caesium_fmt(ot1, ot2), &e2)]
    BinOp {
        o: Binop,
        ot1: OpType,
        ot2: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
    },

    /// dereference an lvalue
    #[display("!{{ {} }} ( {} )", ot, &e)]
    Deref { ot: OpType, e: Box<Expr> },

    /// lvalue to rvalue conversion
    #[display("use{{ {} }} ({})", ot, &e)]
    Use { ot: OpType, e: Box<Expr> },

    /// the borrow-operator to get a reference
    #[display("&ref{{ {}, {}, \"{}\" }} ({})", bk, fmt_option(ty), lft, &e)]
    Borrow {
        lft: Lft,
        bk: BorKind,
        ty: Option<RustType>,
        e: Box<Expr>,
    },

    /// the address-of operator to get a raw pointer
    #[display("&raw{{ {} }} ({})", mt, &e)]
    AddressOf { mt: Mutability, e: Box<Expr> },

    #[display("CallE {} [{}] [@{{expr}} {}]", &f, display_list!(lfts, "; ", "\"{}\""), display_list!(args, "; "))]
    Call {
        f: Box<Expr>,
        lfts: Vec<Lft>,
        args: Vec<Expr>,
    },

    #[display("IfE ({}) ({}) ({}) ({})", ot, &e1, &e2, &e3)]
    If {
        ot: OpType,
        e1: Box<Expr>,
        e2: Box<Expr>,
        e3: Box<Expr>,
    },

    #[display("({}) at{{ {} }} \"{}\"", &e, sls, name)]
    FieldOf {
        e: Box<Expr>,
        sls: String,
        name: String,
    },

    /// an annotated expression
    #[display("AnnotExpr{} {} ({}) ({})", fmt_comment(why), a.needs_laters(), a, &e)]
    Annot {
        a: Annotation,
        why: Option<String>,
        e: Box<Expr>,
    },

    #[display("StructInit {} [{}]", sls, display_list!(components, "; ", |(name, e)| format!("(\"{name}\", {e} : expr)")))]
    StructInitE {
        sls: coq::AppTerm<String>,
        components: Vec<(String, Expr)>,
    },

    #[display("EnumInit {} \"{}\" ({}) ({})", els, variant, ty, &initializer)]
    EnumInitE {
        els: coq::AppTerm<String>,
        variant: String,
        ty: RustType,
        initializer: Box<Expr>,
    },

    #[display("AnnotExpr 0 DropAnnot ({})", &_0)]
    DropE(Box<Expr>),

    /// a box expression for creating a box of a particular type
    #[display("box{{{}}}", &_0)]
    BoxE(SynType),

    /// access the discriminant of an enum
    #[display("EnumDiscriminant ({}) ({})", els, &e)]
    EnumDiscriminant { els: String, e: Box<Expr> },

    /// access to the data of an enum
    #[display("EnumData ({}) \"{}\" ({})", els, variant, &e)]
    EnumData {
        els: String,
        variant: String,
        e: Box<Expr>,
    },
}

impl Expr {
    #[must_use]
    pub fn with_optional_annotation(e: Self, a: Option<Annotation>, why: Option<String>) -> Self {
        match a {
            Some(a) => Self::Annot {
                a,
                e: Box::new(e),
                why,
            },
            None => e,
        }
    }
}

/// for unique/shared pointers
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Mutability {
    #[display("Mut")]
    Mut,

    #[display("Shr")]
    Shared,
}

/**
 * Borrows allowed in Caesium
 */
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum BorKind {
    #[display("Mut")]
    Mutable,

    #[display("Shr")]
    Shared,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum LftNameTree {
    #[display("LftNameTreeLeaf")]
    Leaf,

    #[display("LftNameTreeRef \"{}\" ({})", _0, &_1)]
    Ref(Lft, Box<LftNameTree>),
    // TODO structs etc
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Annotation {
    /// Start a lifetime as a sublifetime of the intersection of a few other lifetimes
    #[display("StartLftAnnot \"{}\" [{}]", _0, display_list!(_1, "; ", "\"{}\""))]
    StartLft(Lft, Vec<Lft>),

    /// End this lifetime
    #[display("EndLftAnnot \"{}\"", _0)]
    EndLft(Lft),

    /// Extend this lifetime by making the directly owned part static
    #[display("ExtendLftAnnot \"{}\"", _0)]
    ExtendLft(Lft),

    /// Dynamically include a lifetime in another lifetime
    #[display("DynIncludeLftAnnot \"{}\" \"{}\"", _0, _1)]
    DynIncludeLft(Lft, Lft),

    /// Shorten the lifetime of an object to the given lifetimes, according to the name map
    #[display("ShortenLftAnnot ({})", _0)]
    ShortenLft(LftNameTree),

    /// add naming for the lifetimes in the type of the expression to the name context,
    /// at the given names
    #[display("GetLftNamesAnnot ({})", _0)]
    GetLftNames(LftNameTree),

    /// Copy a lft name map entry from lft1 to lft2
    #[display("CopyLftNameAnnot \"{}\" \"{}\"", _1, _0)]
    CopyLftName(Lft, Lft),

    /// Create an alias for an intersection of lifetimes
    #[display("AliasLftAnnot \"{}\" [{}]", _0, display_list!(_1, "; ", "\"{}\""))]
    AliasLftIntersection(Lft, Vec<Lft>),

    /// The following Goto will enter a loop
    #[display("EnterLoopAnnot")]
    EnterLoop,
}

impl Annotation {
    #[allow(clippy::unused_self)]
    pub(crate) const fn needs_laters(&self) -> u32 {
        0
    }
}

type BlockLabel = usize;

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Stmt {
    #[display("Goto \"_bb{}\"", _0)]
    GotoBlock(BlockLabel),

    #[display("return ({})", _0)]
    Return(Expr),

    #[display(
        "if{{ {} }}: {} then\n{}\nelse\n{}",
        ot,
        e,
        &s1.indented(&make_indent(1)),
        &s2.indented(&make_indent(1))
    )]
    If {
        ot: OpType,
        e: Expr,
        s1: Box<Stmt>,
        s2: Box<Stmt>,
    },

    #[display(
        "Switch ({}: int_type) ({}) ({}∅) ([{}]) ({})",
        it,
        e,
        display_list!(index_map, "", |(k, v)| format!("<[ {k}%Z := {v}%nat ]> $ ")),
        display_list!(bs, "; "),
        &def
    )]
    Switch {
        // e needs to evaluate to an integer/variant index used as index to bs
        e: Expr,
        it: IntType,
        index_map: HashMap<u128, usize>,
        bs: Vec<Stmt>,
        def: Box<Stmt>,
    },

    #[display("{} <-{{ {} }} {};\n{}", e1, ot, e2, &s)]
    Assign {
        ot: OpType,
        e1: Expr,
        e2: Expr,
        s: Box<Stmt>,
    },

    #[display("expr: {};\n{}", e, &s)]
    ExprS { e: Expr, s: Box<Stmt> },

    #[display("assert{{ {} }}: {};\n{}", OpType::BoolOp, e, &s)]
    AssertS { e: Expr, s: Box<Stmt> },

    #[display("annot: {};{}\n{}", a, fmt_comment(why), &s)]
    Annot {
        a: Annotation,
        s: Box<Stmt>,
        why: Option<String>,
    },

    #[display("StuckS")]
    Stuck,
}

impl Stmt {
    /// Annotate a statement with a list of annotations
    #[must_use]
    pub fn with_annotations(mut s: Self, a: Vec<Annotation>, why: &Option<String>) -> Self {
        for annot in a {
            s = Self::Annot {
                a: annot,
                s: Box::new(s),
                why: why.clone(),
            };
        }
        s
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Unop {
    #[display("NegOp")]
    NegOp,

    #[display("NotBoolOp")]
    NotBoolOp,

    #[display("NotIntOp")]
    NotIntOp,
}

#[derive(Clone, Eq, PartialEq, Debug)]
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
        let format_bool = |st: &str| format!("{} {} , {} , {} }}", st, ot1, ot2, crate::specs::BOOL_REPR);

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

/**
 * A variable in the Caesium code, composed of a name and a type.
 */
#[derive(Clone, Eq, PartialEq, Debug)]
struct Variable((String, SynType));

impl Variable {
    #[must_use]
    pub const fn new(name: String, st: SynType) -> Self {
        Self((name, st))
    }
}

/**
 * Maintain necessary info to map MIR places to Caesium stack variables.
 */
pub struct StackMap {
    args: Vec<Variable>,
    locals: Vec<Variable>,
    used_names: HashSet<String>,
}

impl StackMap {
    #[must_use]
    pub fn new() -> Self {
        Self {
            args: Vec::new(),
            locals: Vec::new(),
            used_names: HashSet::new(),
        }
    }

    pub fn insert_local(&mut self, name: String, st: SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.to_string());
        self.locals.push(Variable::new(name, st));
        true
    }

    pub fn insert_arg(&mut self, name: String, st: SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.to_string());
        self.args.push(Variable::new(name, st));
        true
    }

    #[must_use]
    pub fn lookup_binding(&self, name: &str) -> Option<&SynType> {
        if !self.used_names.contains(name) {
            return None;
        }

        for Variable((nm, st)) in &self.locals {
            if nm == name {
                return Some(st);
            }
        }

        for Variable((nm, st)) in &self.args {
            if nm == name {
                return Some(st);
            }
        }

        panic!("StackMap: invariant violation");
    }
}

/// Representation of a Caesium function's source code
pub struct FunctionCode {
    name: String,
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,

    /// Coq parameters that the function is parameterized over
    required_parameters: Vec<(coq::Name, coq::Type)>,
}

fn make_map_string(sep0: &str, sep: &str, els: &Vec<(String, String)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els {
        out.push_str(sep);

        out.push_str(format!("<[\n    \"{key}\" :=\n{value}\n    ]>%E $").as_str());
    }
    out.push_str(sep);
    out.push('∅');
    out
}

fn make_lft_map_string(els: &Vec<(String, String)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els {
        out.push_str(format!("named_lft_update \"{}\" {} $ ", key, value).as_str());
    }
    out.push('∅');
    out
}

impl Display for FunctionCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_params((name, ty): &(coq::Name, coq::Type)) -> String {
            format!("({} : {})", name, ty)
        }

        fn fmt_variable(Variable((name, ty)): &Variable) -> String {
            format!("(\"{}\", {} : layout)", name, ty.layout_term(&[]))
        }

        fn fmt_blocks((name, bb): (&usize, &Stmt)) -> String {
            formatdoc!(
                r#"<[
                   "_bb{}" :=
                    {}
                   ]>%E $"#,
                name,
                bb.indented_skip_initial(&make_indent(1))
            )
        }

        if self.basic_blocks.is_empty() {
            panic!("Function has no basic block");
        }

        let params = display_list!(&self.required_parameters, " ", fmt_params);
        let args = display_list!(&self.stack_layout.args, ";\n", fmt_variable);
        let locals = display_list!(&self.stack_layout.locals, ";\n", fmt_variable);
        let blocks = display_list!(&self.basic_blocks, "\n", fmt_blocks);

        writedoc!(
            f,
            r#"Definition {}_def {} : function := {{|
                f_args := [
                 {}
                ];
                f_local_vars := [
                 {}
                ];
                f_code :=
                 {}
                 ∅;
                f_init := "_bb0";
               |}}."#,
            self.name,
            params,
            args.indented_skip_initial(&make_indent(2)),
            locals.indented_skip_initial(&make_indent(2)),
            blocks.indented_skip_initial(&make_indent(2))
        )
    }
}

impl FunctionCode {
    /// Get the number of arguments of the function.
    #[must_use]
    pub fn get_argument_count(&self) -> usize {
        self.stack_layout.args.len()
    }
}

/// Builder for a `FunctionCode`.
pub struct FunctionCodeBuilder {
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,
}

impl FunctionCodeBuilder {
    #[must_use]
    pub fn new() -> Self {
        Self {
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
}

#[derive(Clone, Debug, Display)]
#[display("({}PolyNil)", display_list!(_0, "",
    |(bb, spec)| format!("PolyCons ({}, wrap_inv ({})) $ ", bb, spec.func_predicate))
)]
struct InvariantMap(HashMap<usize, LoopSpec>);

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
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,

    /// invariants for loop head bbs
    loop_invariants: InvariantMap,
}

impl<'def> Function<'def> {
    /// Get the name of the function.
    #[must_use]
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
        let has_params = !self.spec.coq_params.is_empty()
            || !self.other_functions.is_empty()
            || !self.used_statics.is_empty();
        if has_params {
            write!(f, "∀ ")?;
            for param in &self.spec.coq_params {
                write!(f, "{} ", param)?;
            }

            // assume locations for other functions
            for (loc_name, _, _, _) in &self.other_functions {
                write!(f, "({} : loc) ", loc_name)?;
            }

            // assume locations for statics
            for s in &self.used_statics {
                write!(f, "({} : loc) ", s.loc_name)?;
            }
            writeln!(f, ", ")?;
        }

        // assume link-time Coq assumptions
        // layoutable
        for st in &self.layoutable_syntys {
            write!(f, "syn_type_is_layoutable ({}) →\n", st)?;
        }
        // statics are registered
        for s in &self.used_statics {
            write!(f, "static_is_registered \"{}\" {} (existT _ {}) →\n", s.ident, s.loc_name, s.ty)?;
        }

        // write extra link-time assumptions
        if !self.spec.extra_link_assum.is_empty() {
            write!(f, "(* extra link-time assumptions *)\n")?;
            for s in &self.spec.extra_link_assum {
                write!(f, "{s} →\n")?;
            }
        }

        // write iris assums
        if self.other_functions.is_empty() {
            write!(f, "⊢ ")?;
        } else {
            for (loc_name, spec_name, param_insts, sts) in &self.other_functions {
                info!("Using other function: {:?} with insts: {:?}", spec_name, param_insts);
                // generate an instantiation for the generic type arguments, by getting the refinement types
                // which need to be passed at the Coq level
                let mut gen_rfn_type_inst = Vec::new();
                for p in param_insts {
                    // use an empty env, these should be closed in the current environment
                    let rfn = p.get_rfn_type(&[]);
                    gen_rfn_type_inst.push(format!("({})", rfn));

                    let st = p.get_syn_type();
                    gen_rfn_type_inst.push(format!("({})", st));
                }
                let arg_syntys: Vec<String> = sts.iter().map(ToString::to_string).collect();

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
        for names in &self.generic_types {
            code_params.push(names.syn_type.clone());
        }
        for s in &self.used_statics {
            code_params.push(s.loc_name.clone());
        }
        for x in &code_params {
            write!(f, "{}  ", x)?;
        }

        // write local syntypes
        write!(f, ") [")?;
        write_list!(f, &self.code.stack_layout.locals, "; ", |Variable((_, st))| st.to_string())?;
        write!(f, "] (type_of_{} ", self.name())?;

        // write type args (passed to the type definition)
        for param in &self.spec.coq_params {
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
            for param in &self.spec.coq_params {
                if param.implicit {
                    write!(f, " ?")?;
                } else {
                    write!(f, " {}", param.name)?;
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
                ip_params.push(' ');
                p_count += 1;
                ip_params.push_str(format!("{}", n).as_str());
            }
            for (n, _) in ty_params {
                write!(f, "let {} := fresh \"{}\" in\n", n, n)?;
            }

            if p_count > 1 {
                ip_params.push_str(" ]");
            }
        } else {
            // no params, but still need to provide something to catch the unit
            // (and no empty intropatterns are allowed)
            ip_params.push('?');
        }

        // generate intro pattern for lifetimes
        let mut lft_pattern = String::with_capacity(100);
        // pattern is left-associative
        for _ in 0..self.spec.lifetimes.len() {
            write!(lft_pattern, "[ ").unwrap();
        }
        write!(lft_pattern, "[]").unwrap();
        for lft in &self.spec.lifetimes {
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

        for Variable((arg, _)) in &self.code.stack_layout.args {
            write!(f, " arg_{}", arg)?;
        }

        for Variable((local, _)) in &self.code.stack_layout.locals {
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
        let formatted_lifetimes = make_lft_map_string(
            &self.spec.lifetimes.iter().map(|n| (n.to_string(), n.to_string())).collect(),
        );
        write!(f, "init_lfts ({} );\n", formatted_lifetimes.as_str())?;

        // initialize tyvars
        let formatted_tyvars = make_map_string(
            " ",
            " ",
            &self
                .generic_types
                .iter()
                .map(|names| (names.rust_name.to_string(), format!("existT _ ({})", names.type_term)))
                .collect(),
        );

        write!(f, "init_tyvars ({} ).\n", formatted_tyvars.as_str())
    }

    pub fn generate_proof<F>(&self, f: &mut F, admit_proofs: bool) -> Result<(), io::Error>
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
            for tac in &self.manual_tactics {
                if tac.starts_with("all:") {
                    write!(f, "{}\n", tac)?;
                } else {
                    write!(f, "{{ {} all: shelve. }}\n", tac)?;
                }
            }

            write!(f, "Unshelve. all: print_remaining_sidecond.\n")?;
        }

        if admit_proofs {
            write!(f, "Admitted. (* admitted due to admit_proofs config flag *)\n")?;
        } else {
            write!(f, "Qed.\n")?;
        }
        Ok(())
    }
}

/// Information on a used static variable
#[derive(Clone, Debug)]
pub struct StaticMeta<'def> {
    pub ident: String,
    pub loc_name: String,
    pub ty: Type<'def>,
}

/// A `CaesiumFunctionBuilder` allows to incrementally construct the functions's code and the spec
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
    /// generic types in scope for this function
    generic_types: Vec<LiteralTyParam>,
    /// generic lifetimes
    generic_lifetimes: Vec<(Option<String>, Lft)>,
    /// Syntypes we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<SynType>,
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,

    /// manually specified tactics that will be emitted in the typing proof
    tactics: Vec<String>,

    /// maps loop head bbs to loop specifications
    loop_invariants: InvariantMap,
}

impl<'def> FunctionBuilder<'def> {
    #[must_use]
    pub fn new(name: &str, spec_name: &str) -> Self {
        let code_builder = FunctionCodeBuilder::new();
        let spec_builder = FunctionSpecBuilder::new();
        FunctionBuilder {
            function_name: name.to_string(),
            spec_name: spec_name.to_string(),
            other_functions: Vec::new(),
            generic_types: Vec::new(),
            generic_lifetimes: Vec::new(),
            code: code_builder,
            spec: spec_builder,
            layoutable_syntys: Vec::new(),
            loop_invariants: InvariantMap(HashMap::new()),
            tactics: Vec::new(),
            used_statics: Vec::new(),
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

    /// Require a static variable to be in scope.
    pub fn require_static(&mut self, s: StaticMeta<'def>) {
        info!("Requiring static {:?}", s);
        self.used_statics.push(s);
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
        self.tactics.push(tac.to_string());
    }

    /// Add a generic type used by this function.
    pub fn add_generic_type(&mut self, t: LiteralTyParam) {
        self.generic_types.push(t);
    }

    /// Get the type parameters.
    #[must_use]
    pub fn get_ty_params(&self) -> &[LiteralTyParam] {
        &self.generic_types
    }

    /// Get the universal lifetimes.
    #[must_use]
    pub fn get_lfts(&self) -> Vec<(Option<String>, Lft)> {
        self.generic_lifetimes.clone()
    }

    /// Add the assumption that a particular syntype is layoutable to the typing proof.
    pub fn assume_synty_layoutable(&mut self, st: SynType) {
        assert!(st.is_closed());
        self.layoutable_syntys.push(st);
    }

    /// Register a loop invariant for the basic block `bb`.
    /// Should only be called once per bb.
    pub fn register_loop_invariant(&mut self, bb: usize, spec: LoopSpec) {
        if self.loop_invariants.0.insert(bb, spec).is_some() {
            panic!("registered loop invariant multiple times");
        }
    }

    fn add_generics_to_spec(&mut self) {
        // push generic type parameters to the spec builder
        for names in &self.generic_types {
            // TODO(cleanup): this currently regenerates the names for ty + rt, instead of using
            // the existing names
            self.spec
                .add_coq_param(coq::Name::Named(names.refinement_type.to_string()), coq::Type::Type, false)
                .unwrap();
            self.spec
                .add_coq_param(
                    coq::Name::Unnamed,
                    coq::Type::Literal(format!("Inhabited {}", names.refinement_type)),
                    true,
                )
                .unwrap();
            self.spec
                .add_coq_param(coq::Name::Named(names.syn_type.to_string()), coq::Type::SynType, false)
                .unwrap();
            self.spec
                .add_ty_param(
                    coq::Name::Named(names.type_term.clone()),
                    coq::Type::Ttype(Box::new(coq::Type::Literal(names.refinement_type.clone()))),
                )
                .unwrap();

            // Add assumptions that the syntactic type of the semantic argument matches with the
            // assumed syntactic type.
            let st_precond = IProp::Pure(format!("ty_syn_type {} = {}", names.type_term, names.syn_type));
            // We prepend these conditions so that this information can already be used to simplify
            // the other assumptions.
            self.spec.prepend_precondition(st_precond);

            // add assumptions that reads/writes to the generic are allowed
            let write_precond = IProp::Pure(format!("ty_allows_writes {}", names.type_term));
            let read_precond = IProp::Pure(format!("ty_allows_reads {}", names.type_term));
            let sc_precond = IProp::Atom(format!("ty_sidecond {}", names.type_term));
            self.spec.add_precondition(write_precond);
            self.spec.add_precondition(read_precond);
            self.spec.add_precondition(sc_precond);
        }
    }
}

impl<'def> From<FunctionBuilder<'def>> for Function<'def> {
    fn from(mut builder: FunctionBuilder<'def>) -> Self {
        // sort parameters for code
        builder.other_functions.sort_by(|a, b| a.0.cmp(&b.0));
        //builder.generic_types.sort_by(|a, b| a.rust_name.cmp(&b.rust_name));
        builder.used_statics.sort_by(|a, b| a.ident.cmp(&b.ident));

        // generate location parameters for other functions used by this one.
        let mut parameters: Vec<(coq::Name, coq::Type)> = builder
            .other_functions
            .iter()
            .map(|f_inst| (coq::Name::Named(f_inst.0.to_string()), coq::Type::Loc))
            .collect();

        // generate location parameters for statics used by this function
        let mut statics_parameters = builder
            .used_statics
            .iter()
            .map(|s| (coq::Name::Named(s.loc_name.to_string()), coq::Type::Loc))
            .collect();
        parameters.append(&mut statics_parameters);

        // add generic syntype parameters for generics that this function uses.
        let mut gen_st_parameters = builder
            .generic_types
            .iter()
            .map(|names| (coq::Name::Named(names.syn_type.to_string()), coq::Type::SynType))
            .collect();
        parameters.append(&mut gen_st_parameters);

        builder.add_generics_to_spec();
        let spec = builder.spec.into_function_spec(&builder.function_name, &builder.spec_name);

        let code = FunctionCode {
            stack_layout: builder.code.stack_layout,
            name: builder.function_name.clone(),
            basic_blocks: builder.code.basic_blocks,
            required_parameters: parameters,
        };

        Function {
            code,
            spec,
            generic_types: builder.generic_types,
            other_functions: builder.other_functions,
            layoutable_syntys: builder.layoutable_syntys,
            loop_invariants: builder.loop_invariants,
            manual_tactics: builder.tactics,
            used_statics: builder.used_statics,
        }
    }
}

impl<'def> From<FunctionBuilder<'def>> for FunctionSpec<'def> {
    fn from(mut builder: FunctionBuilder<'def>) -> Self {
        builder.add_generics_to_spec();
        builder.spec.into_function_spec(&builder.function_name, &builder.spec_name)
    }
}
