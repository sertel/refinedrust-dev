// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// A collection of types to represent and generate Rocq code.
///
/// These types are intended to be used for the purposes of this project.
use std::collections::HashSet;
use std::fmt;
use std::fmt::Write as fmtWrite;
use std::ops::Deref;

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;
use itertools::Itertools;

use crate::{display_list, make_indent, write_list, BASE_INDENT};

/// A Rocq path of the form `A.B.C`.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
#[display("{}", _0)]
pub struct Path(String);

impl Path {
    #[must_use]
    pub fn new(path: &str) -> Self {
        Self(path.to_owned())
    }

    #[must_use]
    pub fn new_from_segments(segments: &[&str]) -> Self {
        Self(segments.join("."))
    }
}

/// A Rocq module that contains a path `A.B.C` and a module name `D`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Module {
    path: Option<Path>,
    name: String,
}

impl Module {
    #[must_use]
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            path: None,
        }
    }

    #[must_use]
    pub fn new_with_path(name: &str, path: Path) -> Self {
        Self {
            name: name.to_owned(),
            path: Some(path),
        }
    }

    #[must_use]
    pub fn get_path(&self) -> Option<Path> {
        self.path.as_ref().cloned()
    }
}

/// A Rocq import of the form `From A.B.C Require Import D`.
///
/// If the `path` is empty, it is of the form `Require Import A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Import(Module);

impl Import {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

impl Deref for Import {
    type Target = Module;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A Rocq export of the form `From A.B.C Require Export D`.
///
/// If the `path` is empty, it is of the form `Require Export A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Export(Module);

impl Export {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

impl Deref for Export {
    type Target = Module;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn get_modules_path(modules: &[&Module]) -> Vec<Path> {
    let paths: Vec<_> = modules.iter().filter_map(|x| x.get_path()).collect();

    let mut result = vec![];
    for path in paths {
        if !result.contains(&path) {
            result.push(path);
        }
    }
    result
}

fn fmt_modules(f: &mut fmt::Formatter<'_>, modules: &[&Module], kind: &str) -> fmt::Result {
    fn is(module: &Module, path: Option<&Path>) -> Option<String> {
        (module.get_path() == path.cloned()).then(|| module.name.clone())
    }

    for path in get_modules_path(modules) {
        let modules: Vec<_> = modules.iter().filter_map(|x| is(x, Some(&path))).collect();

        if modules.is_empty() {
            unreachable!("get_modules_path() gave the path {path} but no modules matched it.");
        }

        writeln!(f, "From {} Require {} {}.", path, kind, modules.join(" "))?;
    }

    let modules_no_path: Vec<_> = modules.iter().filter_map(|x| is(x, None)).collect();

    if !modules_no_path.is_empty() {
        writeln!(f, "Require {} {}.", kind, modules_no_path.join(" "))?;
    }

    Ok(())
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct ImportList<'a>(pub &'a Vec<Import>);

impl Display for ImportList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modules: Vec<_> = self.0.iter().map(|x| &x.0).collect();

        fmt_modules(f, &modules, "Import")
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct ExportList<'a>(pub &'a Vec<Export>);

impl Display for ExportList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modules: Vec<_> = self.0.iter().map(|x| &x.0).collect();

        fmt_modules(f, &modules, "Export")
    }
}

/// Represents an application of a term to an rhs.
/// (commonly used for layouts and instantiating them with generics).
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct AppTerm<T, U> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<U>,
}

impl<T: Display, U: Display> Display for AppTerm<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write_list!(f, &self.rhs, " ", "({})")
    }
}

impl<T, U> AppTerm<T, U> {
    pub fn new(lhs: T, rhs: Vec<U>) -> Self {
        Self { lhs, rhs }
    }

    pub fn new_lhs(lhs: T) -> Self {
        Self {
            lhs,
            rhs: Vec::new(),
        }
    }

    pub(crate) const fn get_lhs(&self) -> &T {
        &self.lhs
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Display)]
pub enum Name {
    #[display("{}", _0)]
    Named(String),

    #[display("_")]
    Unnamed,
}

/// A Coq pattern, e.g., "x" or "'(x, y)".
pub type Pattern = String;

fn fmt_prod(v: &Vec<Type>) -> String {
    match v.as_slice() {
        [] => "unit".to_owned(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Type {
    /// literal types that are not contained in the grammar
    #[display("{}", _0)]
    Literal(String),

    /// function types; the argument vector should be non-empty
    #[display("{} → {}", display_list!(_0, " → ", "({})"), *_1)]
    Function(Vec<Type>, Box<Type>),

    /// Placeholder that should be inferred by Coq if possible
    #[display("_")]
    Infer,

    /// Coq type `lft`
    #[display("lft")]
    Lft,

    /// Coq type `loc`
    #[display("loc")]
    Loc,

    /// Coq type `layout`
    #[display("layout")]
    Layout,

    /// Coq type `syn_type`
    #[display("syn_type")]
    SynType,

    /// Coq type `struct_layout`
    #[display("struct_layout")]
    StructLayout,

    /// Coq type `Type`
    #[display("Type")]
    Type,

    /// Coq type `type rt`
    #[display("(type {})", &_0)]
    Ttype(Box<Type>),

    /// Coq type `rtype`
    #[display("rtype")]
    Rtype,

    /// the unit type
    #[display("unit")]
    Unit,

    /// the type of integers
    #[display("Z")]
    Z,

    /// the type of booleans
    #[display("bool")]
    Bool,

    /// product types
    #[display("{}", fmt_prod(_0))]
    Prod(Vec<Type>),

    /// place_rfn
    #[display("(place_rfn {})", &_0)]
    PlaceRfn(Box<Type>),

    /// gname
    #[display("gname")]
    Gname,

    /// a plist with a given type constructor over a list of types
    #[display("plist {} [{}]", _0, display_list!(_1, "; ", "{} : Type"))]
    PList(String, Vec<Type>),

    /// the semantic type of a function
    #[display("function_ty")]
    FunctionTy,

    /// the Coq type Prop of propositions
    #[display("Prop")]
    Prop,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", self.format(true))]
pub struct Param {
    /// the name
    name: Name,

    /// the type
    ty: Type,

    /// implicit or not?
    implicit: bool,

    /// does this depend on Σ?
    depends_on_sigma: bool,
}

impl Param {
    #[must_use]
    pub fn new(name: Name, ty: Type, implicit: bool) -> Self {
        let depends_on_sigma = if let Type::Literal(lit) = &ty { lit.contains('Σ') } else { false };

        Self {
            name,
            ty,
            implicit,
            depends_on_sigma,
        }
    }

    #[must_use]
    pub fn with_name(&self, name: String) -> Self {
        Self::new(Name::Named(name), self.ty.clone(), self.implicit)
    }

    #[must_use]
    pub fn get_name_ref(&self) -> Option<&str> {
        match &self.name {
            Name::Named(s) => Some(s),
            Name::Unnamed => None,
        }
    }

    #[allow(clippy::collapsible_else_if)]
    #[must_use]
    fn format(&self, make_implicits: bool) -> String {
        if !self.implicit {
            return format!("({} : {})", self.name, self.ty);
        }

        if make_implicits {
            if let Name::Named(name) = &self.name {
                format!("`{{{} : !{}}}", name, self.ty)
            } else {
                format!("`{{!{}}}", self.ty)
            }
        } else {
            if let Name::Named(name) = &self.name {
                format!("`({} : !{})", name, self.ty)
            } else {
                format!("`(!{})", self.ty)
            }
        }
    }

    pub(crate) const fn get_name(&self) -> &Name {
        &self.name
    }

    pub(crate) const fn is_implicit(&self) -> bool {
        self.implicit
    }

    pub(crate) const fn is_dependent_on_sigma(&self) -> bool {
        self.depends_on_sigma
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, " "))]
pub struct ParamList(pub Vec<Param>);

impl ParamList {
    #[must_use]
    pub const fn new(params: Vec<Param>) -> Self {
        Self(params)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn append(&mut self, params: Vec<Param>) {
        self.0.extend(params);
    }

    /// Make using terms for this list of binders
    #[must_use]
    pub fn make_using_terms(&self) -> Vec<GallinaTerm> {
        self.0.iter().map(|x| GallinaTerm::Literal(format!("{}", x.name))).collect()
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{} {}", name, params)]
pub struct Variant {
    name: String,
    params: ParamList,
}

impl Variant {
    #[must_use]
    pub fn new(name: &str, params: Vec<Param>) -> Self {
        Self {
            name: name.to_owned(),
            params: ParamList::new(params),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Inductive {} {} :=\n{}\n.", name, parameters,
    display_list!(variants, "\n| ").indented(&make_indent(1))
)]
pub struct Inductive {
    name: String,
    parameters: ParamList,
    variants: Vec<Variant>,
}

impl Inductive {
    #[must_use]
    pub fn new(name: &str, parameters: Vec<Param>, variants: Vec<Variant>) -> Self {
        Self {
            name: name.to_owned(),
            parameters: ParamList::new(parameters),
            variants,
        }
    }

    pub(crate) const fn get_name(&self) -> &String {
        &self.name
    }
}

/// A single tactic call.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ProofItem {
    #[display("{}.", _0)]
    Literal(String),
}

/// A Coq proof script.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}\n", display_list!(_0, "\n"))]
pub struct ProofScript(pub Vec<ProofItem>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordBodyItem {
    pub name: String,
    pub params: ParamList,
    pub term: GallinaTerm,
}

impl Display for RecordBodyItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        write!(writer, "{} {} :=\n{};", self.name, self.params, self.term)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordBodyTerm {
    pub items: Vec<RecordBodyItem>,
}

impl Display for RecordBodyTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{|\n")?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.items {
            write!(f2, "{}\n", it)?;
        }
        write!(f, "|}}\n")
    }
}

/// A Coq Gallina term.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum GallinaTerm {
    /// a literal
    Literal(String),
    /// Application
    App(Box<AppTerm<GallinaTerm, GallinaTerm>>),
    /// a record body
    RecordBody(RecordBodyTerm),
    /// Projection a.(b) from a record
    RecordProj(Box<GallinaTerm>, String),
    /// Universal quantifiers
    All(ParamList, Box<GallinaTerm>),
    /// Existential quantifiers
    Exists(ParamList, Box<GallinaTerm>),
    /// Infix operators
    Infix(String, Vec<GallinaTerm>),
}

impl Display for GallinaTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(lit) => {
                let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
                write!(f2, "{lit}")
            },
            Self::RecordBody(b) => {
                write!(f, "{b}")
            },
            Self::RecordProj(rec, component) => {
                write!(f, "{rec}.({component})")
            },
            Self::App(box a) => write!(f, "{a}"),
            Self::All(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∀ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Exists(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∃ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Infix(op, terms) => {
                if terms.is_empty() {
                    write!(f, "True")
                } else {
                    write!(f, "{}", terms.iter().format(&format!(" {op} ")))
                }
            },
        }
    }
}

/// A terminator for a proof script
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ProofScriptTerminator {
    #[display("Qed")]
    Qed,

    #[display("Defined")]
    Defined,

    #[display("Admitted")]
    Admitted,
}

/// A body of a Coq definition
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum DefBody {
    /// a proof script invoking Ltac tactics
    Script(ProofScript, ProofScriptTerminator),

    /// a proof term
    Term(GallinaTerm),
}

impl Display for DefBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Script(script, terminator) => {
                write!(f, ".\n")?;
                write!(f, "Proof.\n")?;
                let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
                write!(f2, "{}", script)?;
                write!(f, "{}.", terminator)?;
            },
            Self::Term(term) => {
                write!(f, " := {}.", term)?;
            },
        }
        Ok(())
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Attribute {
    #[display("global")]
    Global,

    #[display("local")]
    Local,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}",
    if attrs.is_empty() { String::new() } else {
        format!("#[ {} ]", display_list!(attrs, ", "))
    }
)]
pub struct Attributes {
    attrs: Vec<Attribute>,
}

impl Attributes {
    #[must_use]
    pub const fn empty() -> Self {
        Self { attrs: vec![] }
    }

    #[must_use]
    pub fn new(attrs: Vec<Attribute>) -> Self {
        Self { attrs }
    }

    #[must_use]
    pub fn singleton(attr: Attribute) -> Self {
        Self { attrs: vec![attr] }
    }
}

/// A Coq typeclass instance declaration
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("#[global] Instance : {}{}", ty, body)]
pub struct InstanceDecl {
    ty: Type,
    body: DefBody,
}

impl InstanceDecl {
    #[must_use]
    pub const fn new(ty: Type, body: DefBody) -> Self {
        Self { ty, body }
    }
}

#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: ParamList,
    pub ty: Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: ParamList,
    pub ty: Type,
    pub constructor: Option<String>,
    pub body: Vec<RecordDeclItem>,
}

impl Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let constructor = self.constructor.clone().unwrap_or_default();
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.body {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.")
    }
}

/// A Context declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContextDecl {
    pub items: ParamList,
}

impl ContextDecl {
    #[must_use]
    pub const fn new(items: ParamList) -> Self {
        Self { items }
    }

    #[must_use]
    pub fn refinedrust() -> Self {
        Self {
            items: ParamList::new(vec![Param::new(
                Name::Named("RRGS".to_owned()),
                Type::Literal("refinedrustGS Σ".to_owned()),
                true,
            )]),
        }
    }
}

impl Display for ContextDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.items.0.is_empty() { Ok(()) } else { write!(f, "Context {}.", self.items) }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum DefinitionKind {
    #[display("Definition")]
    Definition,
    #[display("Lemma")]
    Lemma,
}

/// A Coq definition
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub name: String,
    pub params: ParamList,
    pub ty: Option<Type>,
    pub body: DefBody,
    pub kind: DefinitionKind,
}

impl Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "{} {} {} : {ty}{}", self.kind, self.name, self.params, self.body)
        } else {
            write!(f, "{} {} {}{}", self.kind, self.name, self.params, self.body)
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum TopLevelAssertion<'a> {
    /// A declaration of a Coq Inductive
    #[display("{}", _0)]
    InductiveDecl(&'a Inductive),

    /// A declaration of a Coq instance
    #[display("{}", _0)]
    InstanceDecl(&'a InstanceDecl),

    /// A declaration of a Coq record
    #[display("{}", _0)]
    RecordDecl(Record),

    /// A declaration of Coq context items
    #[display("{}", _0)]
    ContextDecl(ContextDecl),

    /// A Coq Definition
    #[display("{}", _0)]
    Definition(Definition),

    /// A Coq comment
    #[display("(* {} *)", _0)]
    Comment(&'a str),

    /// A Coq section
    #[display("Section {}.\n{}End{}.", _0, Indented::new(_1), _0)]
    Section(String, TopLevelAssertions<'a>),

    /// A Coq section start
    #[display("Section {}.", _0)]
    SectionStart(String),

    /// A Coq section end
    #[display("End {}.", _0)]
    SectionEnd(String),
}

/// Type for writing contents indented via Display.
struct Indented<T> {
    x: T,
}
impl<T> Indented<T> {
    pub const fn new(x: T) -> Self {
        Self { x }
    }
}
impl<T: Display> Display for Indented<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut indent_writer = IndentWriter::new(BASE_INDENT, f);
        write!(indent_writer, "{}", self.x)
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, "\n"))]
pub struct TopLevelAssertions<'a>(pub Vec<TopLevelAssertion<'a>>);

impl<'a> TopLevelAssertions<'a> {
    #[must_use]
    pub(crate) const fn empty() -> Self {
        Self(vec![])
    }

    pub(crate) fn push(&mut self, a: TopLevelAssertion<'a>) {
        self.0.push(a);
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use indoc::indoc;

    use super::*;

    #[test]
    fn modules_paths_none() {
        let module_a = Module::new("A");
        let module_b = Module::new("B");
        let modules = vec![&module_a, &module_b];

        assert_eq!(get_modules_path(&modules), vec![]);
    }

    #[test]
    fn modules_paths_some_uniqueness() {
        let module_a = Module::new_with_path("A", Path::new("a.b.c"));
        let module_b = Module::new_with_path("B", Path::new("a.b.d"));
        let modules = vec![&module_a, &module_b];

        assert_eq!(get_modules_path(&modules), vec![Path::new("a.b.c"), Path::new("a.b.d")]);
    }

    #[test]
    fn modules_paths_some_duplicate() {
        let module_a = Module::new_with_path("A", Path::new("a.b.c"));
        let module_b = Module::new_with_path("B", Path::new("a.b.c"));
        let modules = vec![&module_a, &module_b];

        assert_eq!(get_modules_path(&modules), vec![Path::new("a.b.c")]);
    }

    #[test]
    fn modules_paths_all() {
        let module_a = Module::new("A");
        let module_b = Module::new_with_path("B", Path::new("a.b.c"));
        let module_c = Module::new_with_path("C", Path::new("a.b.d"));
        let module_d = Module::new_with_path("D", Path::new("a.b.d"));
        let modules = vec![&module_a, &module_b, &module_c, &module_d];

        assert_eq!(get_modules_path(&modules), vec![Path::new("a.b.c"), Path::new("a.b.d")]);
    }

    #[test]
    fn display_empty() {
        let modules = vec![];

        assert_eq!(ImportList(&modules).to_string(), "");
    }

    #[test]
    fn display_none() {
        let module_a = Import::new(Module::new("A"));
        let module_b = Import::new(Module::new("B"));
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            Require Import A B.
        "});
    }

    #[test]
    fn display_some_uniqueness() {
        let module_a = Import::new(Module::new_with_path("A", Path::new("a.b.c")));
        let module_b = Import::new(Module::new_with_path("B", Path::new("a.b.d")));
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import A.
            From a.b.d Require Import B.
        "});
    }

    #[test]
    fn display_some_duplicate() {
        let module_a = Import::new(Module::new_with_path("A", Path::new("a.b.c")));
        let module_b = Import::new(Module::new_with_path("B", Path::new("a.b.c")));
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import A B.
        "});
    }

    #[test]
    fn display_all() {
        let module_a = Import::new(Module::new("A"));
        let module_b = Import::new(Module::new_with_path("B", Path::new("a.b.c")));
        let module_c = Import::new(Module::new_with_path("C", Path::new("a.b.d")));
        let module_d = Import::new(Module::new_with_path("D", Path::new("a.b.d")));
        let modules = vec![module_a, module_b, module_c, module_d];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import B.
            From a.b.d Require Import C D.
            Require Import A.
        "});
    }
}
