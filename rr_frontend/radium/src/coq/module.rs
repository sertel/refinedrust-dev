// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// The [module system].
///
/// [module system]: https://coq.inria.fr/doc/master/refman/language/core/modules.html
use std::fmt;

use derive_more::{Deref, Display};

/// A path of the form `A.B.C`.
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

/// A module that contains a path `A.B.C` and a module name `D`.
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

/// An import of the form `From A.B.C Require Import D`.
///
/// If the `path` is empty, it is of the form `Require Import A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Deref)]
pub struct Import(Module);

impl Import {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

/// An export of the form `From A.B.C Require Export D`.
///
/// If the `path` is empty, it is of the form `Require Export A`.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Deref)]
pub struct Export(Module);

impl Export {
    #[must_use]
    pub const fn new(module: Module) -> Self {
        Self(module)
    }
}

/// Get every unique path from a list of modules.
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

/// Pretty printing a list of modules, by merging the ones with the same path.
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

#[cfg(test)]
mod tests {
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
