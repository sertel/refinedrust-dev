// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [module] section.
//!
//! [module]: https://coq.inria.fr/doc/v8.20/refman/language/core/modules.html

use std::fmt;

use derive_more::{Deref, DerefMut, Display, From, Into};

use crate::{display_list, write_list};

/// A [dirpath].
///
/// [dirpath]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-dirpath
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display, Default, Deref, DerefMut)]
#[display("{}", display_list!(_0, "."))]
pub struct DirPath(pub Vec<String>);

impl From<Vec<&str>> for DirPath {
    fn from(v: Vec<&str>) -> Self {
        Self(v.into_iter().map(ToString::to_string).collect())
    }
}

impl From<Vec<String>> for DirPath {
    fn from(v: Vec<String>) -> Self {
        Self(v)
    }
}

/// Either an Import or an Export flag.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Kind {
    Import,
    Export,
}

/// The [`From ... Require`] command.
///
/// [`From ... Require`]: https://coq.inria.fr/doc/v8.20/refman/proof-engine/vernacular-commands.html#coq:cmd.From-%E2%80%A6-Require
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct FromRequire {
    pub from: Option<DirPath>,
    pub import: Vec<String>,
    pub kind: Kind,
}

impl FromRequire {
    #[must_use]
    pub fn new(import: Vec<impl Into<String>>, kind: Kind) -> Self {
        let from = None;
        let import = import.into_iter().map(Into::into).collect();

        Self { from, import, kind }
    }

    #[allow(clippy::same_name_method)]
    #[must_use]
    pub fn from(self, from: impl Into<DirPath>) -> Self {
        let from = Some(from.into());

        Self { from, ..self }
    }

    #[must_use]
    pub fn get_path(&self) -> Option<DirPath> {
        self.from.clone()
    }
}

impl Display for FromRequire {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(from) = &self.from {
            write!(f, "From {} ", from)?;
        }

        match self.kind {
            Kind::Import => write!(f, "Require Import ")?,
            Kind::Export => write!(f, "Require Export ")?,
        };

        write_list!(f, &self.import, " ")
    }
}

/// A wrapper over [`FromRequire`] to represent an import list.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Deref, DerefMut, Into)]
pub struct Import(pub FromRequire);

impl Import {
    #[must_use]
    pub fn new(import: Vec<impl Into<String>>) -> Self {
        Self(FromRequire::new(import, Kind::Import))
    }

    #[must_use]
    pub fn from(self, from: impl Into<DirPath>) -> Self {
        Self(self.0.from(from))
    }
}

/// A wrapper over [`FromRequire`] to represent an export list.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Deref, DerefMut, Into)]
pub struct Export(pub FromRequire);

impl Export {
    #[must_use]
    pub fn new(import: Vec<impl Into<String>>) -> Self {
        Self(FromRequire::new(import, Kind::Export))
    }

    #[must_use]
    pub fn from(self, from: impl Into<DirPath>) -> Self {
        Self(self.0.from(from))
    }
}

/// Get every unique path from a list of modules.
fn get_modules_path(modules: &[&FromRequire]) -> Vec<DirPath> {
    let paths: Vec<_> = modules.iter().filter_map(|x| x.get_path()).collect();

    let mut result = vec![];
    for path in paths {
        if !result.contains(&path) {
            result.push(path);
        }
    }
    result
}

/// Pretty printing a list of modules, by merging the ones with the same path.
fn fmt_modules(f: &mut fmt::Formatter<'_>, modules: &[&FromRequire], kind: &str) -> fmt::Result {
    fn is(module: &FromRequire, path: Option<&DirPath>) -> Option<Vec<String>> {
        (module.get_path() == path.cloned()).then(|| module.import.clone())
    }

    for path in get_modules_path(modules) {
        let modules: Vec<_> = modules.iter().filter_map(|x| is(x, Some(&path))).flatten().collect();

        if modules.is_empty() {
            unreachable!("get_modules_path() gave the path {path} but no modules matched it.");
        }

        writeln!(f, "From {} Require {} {}.", path, kind, modules.join(" "))?;
    }

    let modules_no_path: Vec<_> = modules.iter().filter_map(|x| is(x, None)).flatten().collect();

    if !modules_no_path.is_empty() {
        writeln!(f, "Require {} {}.", kind, modules_no_path.join(" "))?;
    }

    Ok(())
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ImportList<'a>(pub &'a Vec<Import>);

impl Display for ImportList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modules: Vec<_> = self.0.iter().map(|x| &x.0).collect();

        fmt_modules(f, &modules, "Import")
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExportList<'a>(pub &'a Vec<Export>);

impl Display for ExportList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modules: Vec<_> = self.0.iter().map(|x| &x.0).collect();

        fmt_modules(f, &modules, "Export")
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::*;

    #[test]
    fn dirpath_empty() {
        let path = DirPath::default();

        assert_eq!(path.to_string(), "");
    }

    #[test]
    fn dirpath_some_separated() {
        let path = DirPath::from(vec!["a", "b", "c"]);

        assert_eq!(path.to_string(), "a.b.c");
    }

    #[test]
    fn dirpath_some_concatenated() {
        let path = DirPath::from(vec!["a.b.c"]);

        assert_eq!(path.to_string(), "a.b.c");
    }

    #[test]
    fn dirpath_some_all() {
        let path = DirPath::from(vec!["a", "b.c", "d"]);

        assert_eq!(path.to_string(), "a.b.c.d");
    }

    #[test]
    fn dirpath_strings() {
        let dirpath = DirPath::from(vec!["a.b.c".to_owned()]);

        assert_eq!(dirpath.to_string(), "a.b.c");
    }

    #[test]
    fn modules_paths_none() {
        let module_a = Import::new(vec!["A"]);
        let module_b = Import::new(vec!["B"]);
        let modules = vec![&*module_a, &*module_b];

        assert_eq!(get_modules_path(&modules), vec![]);
    }

    #[test]
    fn modules_paths_some_uniqueness() {
        let module_a = Import::new(vec!["A"]).from(vec!["a", "b", "c"]);
        let module_b = Import::new(vec!["B"]).from(vec!["a", "b", "d"]);
        let modules = vec![&*module_a, &*module_b];

        assert_eq!(get_modules_path(&modules), vec![
            DirPath::from(vec!["a", "b", "c"]),
            DirPath::from(vec!["a", "b", "d"])
        ]);
    }

    #[test]
    fn modules_paths_some_duplicate() {
        let module_a = Import::new(vec!["A"]).from(vec!["a", "b", "c"]);
        let module_b = Import::new(vec!["B"]).from(vec!["a", "b", "c"]);
        let modules = vec![&*module_a, &*module_b];

        assert_eq!(get_modules_path(&modules), vec![DirPath::from(vec!["a", "b", "c"])]);
    }

    #[test]
    fn modules_paths_all() {
        let module_a = Import::new(vec!["A"]);
        let module_b = Import::new(vec!["B"]).from(vec!["a", "b", "c"]);
        let module_c = Import::new(vec!["C"]).from(vec!["a", "b", "d"]);
        let module_d = Import::new(vec!["D"]).from(vec!["a", "b", "d"]);
        let modules = vec![&*module_a, &*module_b, &*module_c, &*module_d];

        assert_eq!(get_modules_path(&modules), vec![
            DirPath::from(vec!["a", "b", "c"]),
            DirPath::from(vec!["a", "b", "d"])
        ]);
    }

    #[test]
    fn display_empty() {
        let modules = vec![];

        assert_eq!(ImportList(&modules).to_string(), "");
    }

    #[test]
    fn display_none() {
        let module_a = Import::new(vec!["A"]);
        let module_b = Import::new(vec!["B", "C"]);
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            Require Import A B C.
        "});
    }

    #[test]
    fn display_some_uniqueness() {
        let module_a = Import::new(vec!["A"]).from(vec!["a", "b", "c"]);
        let module_b = Import::new(vec!["B", "C"]).from(vec!["a", "b", "d"]);
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import A.
            From a.b.d Require Import B C.
        "});
    }

    #[test]
    fn display_some_duplicate() {
        let module_a = Import::new(vec!["A"]).from(vec!["a", "b", "c"]);
        let module_b = Import::new(vec!["B", "C"]).from(vec!["a", "b", "c"]);
        let modules = vec![module_a, module_b];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import A B C.
        "});
    }

    #[test]
    fn display_all() {
        let module_a = Import::new(vec!["A"]);
        let module_b = Import::new(vec!["B", "C"]).from(vec!["a", "b", "c"]);
        let module_c = Import::new(vec!["D"]).from(vec!["a", "b", "d"]);
        let module_d = Import::new(vec!["E", "F"]).from(vec!["a", "b", "d"]);
        let modules = vec![module_a, module_b, module_c, module_d];

        assert_eq!(ImportList(&modules).to_string(), indoc! {"
            From a.b.c Require Import B C.
            From a.b.d Require Import D E F.
            Require Import A.
        "});
    }
}
