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

use derive_more::{Constructor, Display};
use indent_write::indentable::Indentable;
use indent_write::io::IndentWriter;
use indoc::{formatdoc, writedoc};
use log::info;
use typed_arena::Arena;

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
        None => "None".to_owned(),
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
    pub fn of_type(ty: &Type<'_>) -> Self {
        info!("Translating rustType: {:?}", ty);
        match ty {
            Type::Int(it) => Self::Int(*it),
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,

            Type::MutRef(ty, lft) => {
                let ty = Self::of_type(ty);
                Self::MutRef(Box::new(ty), lft.clone())
            },

            Type::ShrRef(ty, lft) => {
                let ty = Self::of_type(ty);
                Self::ShrRef(Box::new(ty), lft.clone())
            },

            Type::BoxType(ty) => {
                let ty = Self::of_type(ty);
                Self::PrimBox(Box::new(ty))
            },

            Type::Struct(as_use) => {
                let is_raw = as_use.is_raw();

                let Some(def) = as_use.def else {
                    return Self::Unit;
                };

                // translate type parameter instantiations
                let typarams: Vec<_> = as_use.ty_params.iter().map(|ty| Self::of_type(ty)).collect();
                let ty_name = if is_raw { def.plain_ty_name() } else { def.public_type_name() };

                Self::Lit(vec![ty_name.to_owned()], typarams)
            },

            Type::Enum(ae_use) => {
                let typarams: Vec<_> = ae_use.ty_params.iter().map(|ty| Self::of_type(ty)).collect();

                Self::Lit(vec![ae_use.def.public_type_name().to_owned()], typarams)
            },

            Type::LiteralParam(lit) => Self::TyVar(lit.rust_name.clone()),

            Type::Literal(lit) => {
                let typarams: Vec<_> = lit.params.iter().map(|ty| Self::of_type(ty)).collect();
                Self::Lit(vec![lit.def.type_term.clone()], typarams)
            },

            Type::Uninit(_) => {
                panic!("RustType::of_type: uninit is not a Rust type");
            },

            Type::Unit => Self::Unit,

            Type::Never => {
                panic!("RustType::of_type: cannot translate Never type");
            },

            Type::RawPtr => Self::Lit(vec!["alias_ptr_t".to_owned()], vec![]),
        }
    }
}

/**
 * Caesium literals.
 *
 * This is much more constrained than the Coq version of values, as we do not need to represent
 * runtime values.
 */
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Literal {
    #[display("I2v ({}) {}", _0, IntType::I8)]
    I8(i8),

    #[display("I2v ({}) {}", _0, IntType::I16)]
    I16(i16),

    #[display("I2v ({}) {}", _0, IntType::I32)]
    I32(i32),

    #[display("I2v ({}) {}", _0, IntType::I64)]
    I64(i64),

    #[display("I2v ({}) {}", _0, IntType::I128)]
    I128(i128),

    #[display("I2v ({}) {}", _0, IntType::U8)]
    U8(u8),

    #[display("I2v ({}) {}", _0, IntType::U16)]
    U16(u16),

    #[display("I2v ({}) {}", _0, IntType::U32)]
    U32(u32),

    #[display("I2v ({}) {}", _0, IntType::U64)]
    U64(u64),

    #[display("I2v ({}) {}", _0, IntType::U128)]
    U128(u128),

    #[display("val_of_bool {}", _0)]
    Bool(bool),

    #[display("I2v ({}) CharIt", *_0 as u32)]
    Char(char),

    /// name of the loc
    #[display("{}", _0)]
    Loc(String),

    /// dummy literal for ZST values (e.g. ())
    #[display("zst_val")]
    ZST,
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

    /// A call target, annotated with the type instantiation
    #[display("{}", _0)]
    CallTarget(String, Vec<RustType>, Vec<Lft>),

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

    #[display("CallE {} [{}] [{}] [@{{expr}} {}]", &f, display_list!(lfts, "; ", "\"{}\""), display_list!(tys, "; ", "{}"), display_list!(args, "; "))]
    Call {
        f: Box<Expr>,
        lfts: Vec<Lft>,
        tys: Vec<RustType>,
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
        sls: coq::term::App<String, String>,
        components: Vec<(String, Expr)>,
    },

    #[display("EnumInit {} \"{}\" ({}) ({})", els, variant, ty, &initializer)]
    EnumInitE {
        els: coq::term::App<String, String>,
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

    #[display("assert{{ {} }}: {};\n{}", OpType::Bool, e, &s)]
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
    Neg,

    #[display("NotBoolOp")]
    NotBool,

    #[display("NotIntOp")]
    NotInt,

    #[display("CastOp ({})", _0)]
    Cast(OpType),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Binop {
    //arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // logical
    And,
    Or,

    //bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,

    // comparison
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,

    // pointer operations
    PtrOffset(Layout),
    PtrNegOffset(Layout),
    PtrDiff(Layout),

    // checked ops
    CheckedAdd,
    CheckedSub,
    CheckedMul,
}

impl Binop {
    fn caesium_fmt(&self, ot1: &OpType, ot2: &OpType) -> String {
        let format_prim = |st: &str| format!("{} {} , {} }}", st, ot1, ot2);
        let format_bool = |st: &str| format!("{} {} , {} , {} }}", st, ot1, ot2, BOOL_REPR);

        match self {
            Self::Add => format_prim("+{"),
            Self::Sub => format_prim("-{"),
            Self::Mul => format_prim("×{"),
            Self::CheckedAdd => format_prim("+c{"),
            Self::CheckedSub => format_prim("-c{"),
            Self::CheckedMul => format_prim("×c{"),
            Self::Div => format_prim("/{"),
            Self::Mod => format_prim("%{"),
            Self::And => format_bool("&&{"),
            Self::Or => format_bool("||{"),
            Self::BitAnd => format_prim("&b{"),
            Self::BitOr => format_prim("|{"),
            Self::BitXor => format_prim("^{"),
            Self::Shl => format_prim("<<{"),
            Self::Shr => format_prim(">>{"),
            Self::Eq => format_bool("= {"),
            Self::Ne => format_bool("!= {"),
            Self::Lt => format_bool("<{"),
            Self::Gt => format_bool(">{"),
            Self::Le => format_bool("≤{"),
            Self::Ge => format_bool("≥{"),
            Self::PtrOffset(ly) => format!("at_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrNegOffset(ly) => format!("at_neg_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrDiff(ly) => format!("sub_ptr{{ {} , {} , {} }}", ly, ot1, ot2),
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
        self.used_names.insert(name.clone());
        self.locals.push(Variable::new(name, st));
        true
    }

    pub fn insert_arg(&mut self, name: String, st: SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.clone());
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
#[allow(clippy::module_name_repetitions)]
pub struct FunctionCode {
    name: String,
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,

    /// Coq parameters that the function is parameterized over
    required_parameters: Vec<coq::binder::Binder>,
}

fn make_map_string(sep: &str, els: &Vec<(String, String)>) -> String {
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
        fn fmt_variable(Variable((name, ty)): &Variable) -> String {
            format!("(\"{}\", {} : layout)", name, Layout::from(ty))
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

        let params = display_list!(&self.required_parameters, " ");
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
        )?;
        Ok(())
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
        self.stack_layout.insert_arg(name.to_owned(), st);
    }

    pub fn add_local(&mut self, name: &str, st: SynType) {
        self.stack_layout.insert_local(name.to_owned(), st);
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
#[allow(clippy::partial_pub_fields)]
pub struct Function<'def> {
    pub code: FunctionCode,
    pub spec: &'def FunctionSpec<InnerFunctionSpec<'def>>,

    /// Other functions that are used by this one.
    other_functions: Vec<UsedProcedure<'def>>,
    /// Syntypes that we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<SynType>,
    /// Custom tactics for the generated proof
    manual_tactics: Vec<String>,
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,

    /// invariants for loop head bbs
    loop_invariants: InvariantMap,

    /// Extra linktime assumptions
    pub extra_link_assum: Vec<String>,
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
        let params = self.spec.get_all_coq_params();
        let has_params =
            !params.0.is_empty() || !self.other_functions.is_empty() || !self.used_statics.is_empty();
        if has_params {
            write!(f, "∀ ")?;
            for param in &params.0 {
                write!(f, "{} ", param)?;
            }

            // assume locations for other functions
            for proc_use in &self.other_functions {
                write!(f, "({} : loc) ", proc_use.loc_name)?;
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
        if !self.extra_link_assum.is_empty() {
            write!(f, "(* extra link-time assumptions *)\n")?;
            for s in &self.extra_link_assum {
                write!(f, "{s} →\n")?;
            }
        }

        // write iris assums
        if self.other_functions.is_empty() {
            write!(f, "⊢ ")?;
        } else {
            for proc_use in &self.other_functions {
                info!(
                    "Using other function: {:?} with insts: {:?}",
                    proc_use.spec_name, proc_use.type_params
                );

                let arg_syntys: Vec<String> =
                    proc_use.syntype_of_all_args.iter().map(ToString::to_string).collect();

                write!(
                    f,
                    "{} ◁ᵥ{{π}} {} @ function_ptr [{}] {} -∗\n",
                    proc_use.loc_name,
                    proc_use.loc_name,
                    arg_syntys.join("; "),
                    proc_use,
                )?;
            }
        }

        write!(f, "typed_function π ")?;
        write!(f, "({}_def ", self.name())?;

        // add arguments for the code definition
        let mut code_params: Vec<_> =
            self.other_functions.iter().map(|proc_use| proc_use.loc_name.clone()).collect();

        for names in self.spec.generics.get_coq_ty_st_params().make_using_terms() {
            code_params.push(format!("{names}"));
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
        write!(f, "] (<tag_type> {} ", self.spec.get_spec_name())?;

        // write type args (passed to the type definition)
        for param in &params.0 {
            if !param.is_implicit() {
                write!(f, "{} ", param.get_name())?;
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
        let params = self.spec.get_all_coq_params();
        if !params.0.is_empty() {
            write!(f, "intros")?;
            for param in &params.0 {
                if param.is_implicit() {
                    write!(f, " ?")?;
                } else {
                    write!(f, " {}", param.get_name())?;
                }
            }
            writeln!(f, ";")?;
        }

        write!(f, "intros;\n")?;
        write!(f, "iStartProof;\n")?;

        // generate intro pattern for lifetimes
        let mut lft_pattern = String::with_capacity(100);
        // pattern is right-associative
        for lft in self.spec.generics.get_lfts() {
            write!(lft_pattern, "[{} ", lft).unwrap();
            write!(f, "let {} := fresh \"{}\" in\n", lft, lft)?;
        }
        write!(lft_pattern, "[]").unwrap();
        for _ in 0..self.spec.generics.get_num_lifetimes() {
            write!(lft_pattern, " ]").unwrap();
        }

        // generate intro pattern for typarams
        let mut typaram_pattern = String::with_capacity(100);
        // pattern is right-associative
        for param in self.spec.generics.get_ty_params() {
            write!(typaram_pattern, "[{} ", param.type_term).unwrap();
            write!(f, "let {} := fresh \"{}\" in\n", param.type_term, param.type_term)?;
        }
        write!(typaram_pattern, "[]").unwrap();
        for _ in 0..self.spec.generics.get_num_ty_params() {
            write!(typaram_pattern, " ]").unwrap();
        }

        // Prepare the intro pattern for specification-level parameters
        let mut ip_params = String::with_capacity(100);

        let params = self.spec.spec.get_params();
        /*
        for _ in 0..params.len() {
            write!(ip_params, "[ ").unwrap();
        }
        //write!(ip_params, "[]").unwrap();
        for p in params {
            write!(ip_params, " {}]", p.0).unwrap();
        }
        */
        if let Some(params) = params {
            if params.is_empty() {
                // no params, but still need to provide something to catch the unit
                // (and no empty intropatterns are allowed)
                ip_params.push('?');
            } else {
                // product is left-associative
                for _ in 0..(params.len() - 1) {
                    ip_params.push_str("[ ");
                }

                let mut p_count = 0;
                for param in params {
                    if p_count > 1 {
                        ip_params.push_str(" ]");
                    }
                    ip_params.push(' ');
                    p_count += 1;
                    ip_params.push_str(&param.get_name());
                }

                if p_count > 1 {
                    ip_params.push_str(" ]");
                }
            }
        } else {
            ip_params.push('?');
        }

        write!(
            f,
            "start_function \"{}\" ( {} ) ( {} ) ( {} );\n",
            self.name(),
            lft_pattern.as_str(),
            typaram_pattern.as_str(),
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

        // destruct specification-level parameters
        if let Some(params) = params {
            write!(f, "prepare_parameters (")?;
            for param in params {
                write!(f, " {}", param.get_name())?;
            }
            write!(f, " );\n")?;
        }

        // initialize lifetimes
        let formatted_lifetimes = make_lft_map_string(
            &self.spec.generics.get_lfts().iter().map(|n| (n.to_string(), n.to_string())).collect(),
        );
        write!(f, "init_lfts ({} );\n", formatted_lifetimes.as_str())?;

        // initialize tyvars
        let formatted_tyvars = make_map_string(
            " ",
            &self
                .spec
                .generics
                .get_ty_params()
                .iter()
                .map(|names| (names.rust_name.clone(), format!("existT _ ({})", names.type_term)))
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

/// Information on a used const place
#[derive(Clone, Debug)]
pub struct ConstPlaceMeta<'def> {
    pub ident: String,
    pub loc_name: String,
    pub ty: Type<'def>,
}

/// Information about another procedure this function uses
#[derive(Constructor, Clone, Debug)]
pub struct UsedProcedure<'def> {
    /// The name to use for the location parameter
    pub loc_name: String,
    /// The name of the specification definition
    pub spec_name: String,

    /// extra arguments to pass to the spec
    pub extra_spec_args: Vec<String>,

    /// Type parameters to quantify over
    /// This includes:
    /// - types this function spec needs to be generic over (in particular type variables of the calling
    ///   function)
    /// - additional lifetimes that the generic instantiation introduces, as well as all lifetime parameters
    ///   of this function
    pub quantified_scope: GenericScope,

    /// specialized specs for the trait assumptions
    pub trait_specs: Vec<SpecializedTraitSpec<'def>>,

    /// The type parameters to instantiate the spec with
    pub type_params: Vec<Type<'def>>,

    /// The lifetime paramters to instantiate the spec with
    /// (after the lifting of all parameters into the `quantified_scope`)
    pub lifetimes: Vec<Lft>,

    /// The syntactic types of all arguments
    pub syntype_of_all_args: Vec<SynType>,
}

impl<'def> Display for UsedProcedure<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // quantify
        write!(f, "(<tag_type> {} ", self.quantified_scope)?;

        // instantiate refinement types
        let mut gen_rfn_type_inst = Vec::new();
        for p in &self.type_params {
            // use an empty env, these should be closed in the current environment
            let rfn = p.get_rfn_type();
            gen_rfn_type_inst.push(format!("({})", rfn));
        }
        // instantiate syntypes
        for p in &self.type_params {
            let st = SynType::from(p);
            gen_rfn_type_inst.push(format!("({})", st));
        }

        write!(f, "{} {} {} ", self.spec_name, gen_rfn_type_inst.join(" "), self.extra_spec_args.join(" "))?;

        // apply to trait specs
        for x in &self.trait_specs {
            write!(f, "{} ", x.specialized_attr)?;
            write!(f, "{} ", x)?;
        }

        // instantiate lifetimes
        for lft in &self.lifetimes {
            write!(f, " <LFT> {lft}")?;
        }

        // instantiate type variables
        for ty in &self.type_params {
            write!(f, " <TY> {ty}")?;
        }

        write!(f, " <MERGE!>)")
    }
}

/// A `CaesiumFunctionBuilder` allows to incrementally construct the functions's code and the spec
/// at the same time. It ensures that both definitions line up in the right way (for instance, by
/// ensuring that other functions are linked up in a consistent way).
#[allow(clippy::partial_pub_fields)]
pub struct FunctionBuilder<'def> {
    pub code: FunctionCodeBuilder,

    /// optionally, a specification, if one has been created
    pub spec: FunctionSpec<Option<InnerFunctionSpec<'def>>>,

    /// a sequence of other functions used by this function
    /// (Note that there may be multiple assumptions here with the same spec, if they are
    /// monomorphizations of the same function!)
    other_functions: Vec<UsedProcedure<'def>>,

    /// required trait assumptions
    trait_requirements: Vec<LiteralTraitSpecUse<'def>>,

    /// Syntypes we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<SynType>,
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,

    /// manually specified tactics that will be emitted in the typing proof
    tactics: Vec<String>,

    /// maps loop head bbs to loop specifications
    loop_invariants: InvariantMap,

    /// Extra link-time assumptions
    extra_link_assum: Vec<String>,
}

impl<'def> FunctionBuilder<'def> {
    #[must_use]
    pub fn new(name: &str, spec_name: &str) -> Self {
        let code_builder = FunctionCodeBuilder::new();
        let spec = FunctionSpec::empty(spec_name.to_owned(), name.to_owned(), None);
        FunctionBuilder {
            other_functions: Vec::new(),
            code: code_builder,
            spec,
            layoutable_syntys: Vec::new(),
            loop_invariants: InvariantMap(HashMap::new()),
            tactics: Vec::new(),
            used_statics: Vec::new(),
            trait_requirements: Vec::new(),
            extra_link_assum: Vec::new(),
        }
    }

    /// Require another function to be available.
    pub fn require_function(&mut self, proc_use: UsedProcedure<'def>) {
        self.other_functions.push(proc_use);
    }

    /// Require a static variable to be in scope.
    pub fn require_static(&mut self, s: StaticMeta<'def>) {
        info!("Requiring static {:?}", s);
        self.used_statics.push(s);
    }

    /// Adds a lifetime parameter to the function.
    pub fn add_universal_lifetime(&mut self, lft: Lft) {
        self.spec.generics.add_lft_param(lft);
    }

    /// Add a manual tactic used for a sidecondition proof.
    pub fn add_manual_tactic(&mut self, tac: String) {
        self.tactics.push(tac);
    }

    /// Add a generic type used by this function.
    pub fn add_ty_param(&mut self, t: LiteralTyParam) {
        self.spec.generics.add_ty_param(t);
    }

    /// Get the type parameters.
    #[must_use]
    pub fn get_ty_params(&self) -> &[LiteralTyParam] {
        self.spec.generics.get_ty_params()
    }

    /// Get the universal lifetimes.
    #[must_use]
    pub fn get_lfts(&self) -> &[Lft] {
        self.spec.generics.get_lfts()
    }

    /// Add the assumption that a particular syntype is layoutable to the typing proof.
    pub fn assume_synty_layoutable(&mut self, st: SynType) {
        self.layoutable_syntys.push(st);
    }

    /// Register a loop invariant for the basic block `bb`.
    /// Should only be called once per bb.
    pub fn register_loop_invariant(&mut self, bb: usize, spec: LoopSpec) {
        if self.loop_invariants.0.insert(bb, spec).is_some() {
            panic!("registered loop invariant multiple times");
        }
    }

    /// Add a Coq-level param that comes before the type parameters.
    pub fn add_early_coq_param(&mut self, param: coq::binder::Binder) {
        self.spec.early_coq_params.0.push(param);
    }

    /// Add a Coq-level param that comes after the type parameters.
    pub fn add_late_coq_param(&mut self, param: coq::binder::Binder) {
        self.spec.late_coq_params.0.push(param);
    }

    /// Require that a particular trait is in scope.
    pub fn add_trait_requirement(&mut self, req: LiteralTraitSpecUse<'def>) {
        self.trait_requirements.push(req);
    }

    /// Add an extra link-time assumption.
    pub fn add_linktime_assumption(&mut self, assumption: String) {
        self.extra_link_assum.push(assumption);
    }

    /// Add a default function spec.
    pub fn add_trait_function_spec(&mut self, spec: InstantiatedTraitFunctionSpec<'def>) {
        assert!(self.spec.spec.is_none(), "Overriding specification of FunctionBuilder");
        self.spec.spec = Some(InnerFunctionSpec::TraitDefault(spec));
    }

    /// Add a functon specification from a specification builder.
    pub fn add_function_spec_from_builder(&mut self, mut spec_builder: LiteralFunctionSpecBuilder<'def>) {
        // add things for traits
        // TODO: is this the right place to do this?
        for trait_use in &self.trait_requirements {
            let spec_params_param_name = trait_use.make_spec_params_param_name();

            let spec_params_type_name = trait_use.trait_ref.spec_params_record.clone();

            let spec_param_name = trait_use.make_spec_param_name();
            let spec_attrs_param_name = trait_use.make_spec_attrs_param_name();
            let spec_type = format!("{} {spec_params_param_name}", trait_use.trait_ref.spec_record);

            // add the spec params
            self.spec.late_coq_params.0.push(coq::binder::Binder::new_generalized(
                coq::binder::Kind::MaxImplicit,
                Some(spec_params_param_name),
                coq::term::Type::Literal(spec_params_type_name),
            ));

            // add the attr params
            let all_args: Vec<_> = trait_use
                .params_inst
                .iter()
                .map(Type::get_rfn_type)
                .chain(trait_use.get_assoc_ty_inst().into_iter().map(|x| x.get_rfn_type()))
                .collect();
            let mut attr_param = format!("{} ", trait_use.trait_ref.spec_attrs_record);
            push_str_list!(attr_param, &all_args, " ");
            self.spec.late_coq_params.0.push(coq::binder::Binder::new(
                Some(spec_attrs_param_name),
                coq::term::Type::Literal(attr_param),
            ));

            // add the spec itself
            self.spec
                .late_coq_params
                .0
                .push(coq::binder::Binder::new(Some(spec_param_name), coq::term::Type::Literal(spec_type)));

            let spec_precond = trait_use.make_spec_param_precond();
            // this should be proved after typarams are instantiated
            spec_builder.add_late_precondition(spec_precond);
        }

        assert!(self.spec.spec.is_none(), "Overriding specification of FunctionBuilder");
        let lit_spec = spec_builder.into_function_spec();
        self.spec.spec = Some(InnerFunctionSpec::Lit(lit_spec));
    }

    pub fn into_function(
        mut self,
        arena: &'def Arena<FunctionSpec<InnerFunctionSpec<'def>>>,
    ) -> Function<'def> {
        assert!(self.spec.spec.is_some(), "No specification provided");

        // sort parameters for code
        self.other_functions.sort_by(|a, b| a.loc_name.cmp(&b.loc_name));
        self.used_statics.sort_by(|a, b| a.ident.cmp(&b.ident));

        // generate location parameters for other functions used by this one, as well as syntypes
        // These are parameters that the code gets
        let mut parameters: Vec<coq::binder::Binder> = self
            .other_functions
            .iter()
            .map(|f_inst| (coq::binder::Binder::new(Some(f_inst.loc_name.clone()), coq::term::Type::Loc)))
            .collect();

        // generate location parameters for statics used by this function
        let mut statics_parameters = self
            .used_statics
            .iter()
            .map(|s| coq::binder::Binder::new(Some(s.loc_name.clone()), coq::term::Type::Loc))
            .collect();

        parameters.append(&mut statics_parameters);

        // add generic syntype parameters for generics that this function uses.
        let mut gen_st_parameters = self
            .spec
            .generics
            .get_ty_params()
            .iter()
            .map(|names| coq::binder::Binder::new(Some(names.syn_type.clone()), coq::term::Type::SynType))
            .collect();

        parameters.append(&mut gen_st_parameters);

        let code = FunctionCode {
            stack_layout: self.code.stack_layout,
            name: self.spec.function_name.clone(),
            basic_blocks: self.code.basic_blocks,
            required_parameters: parameters,
        };

        // assemble the spec
        let lit_spec = self.spec.spec.take().unwrap();
        let spec = self.spec.replace_spec(lit_spec);
        let spec_ref = arena.alloc(spec);

        Function {
            code,
            spec: spec_ref,
            other_functions: self.other_functions,
            layoutable_syntys: self.layoutable_syntys,
            loop_invariants: self.loop_invariants,
            manual_tactics: self.tactics,
            used_statics: self.used_statics,
            extra_link_assum: self.extra_link_assum,
        }
    }
}

impl<'def> TryFrom<FunctionBuilder<'def>> for FunctionSpec<InnerFunctionSpec<'def>> {
    type Error = String;

    fn try_from(mut builder: FunctionBuilder<'def>) -> Result<Self, String> {
        let spec = builder.spec.spec.take().ok_or_else(|| "No specification was provided".to_owned())?;
        Ok(builder.spec.replace_spec(spec))
    }
}
