// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Registry of shims for Rust functions that get mapped to custom RefinedRust
/// implementations.
/// Provides deserialization from a JSON file defining this registry.
extern crate serde_json;

use serde::{Deserialize, Serialize};
use typed_arena::Arena;

use std::fs::File;
use std::io::BufReader;

type Path<'a> = Vec<&'a str>;

/// A file entry.
#[derive(Serialize, Deserialize)]
struct ShimFileEntry {
    /// The rustc path for this symbol.
    path: Vec<String>,
    /// a kind: either "method" or "function"
    kind: String,
    /// the Coq name of the code
    name: String,
    /// the Coq name of the spec
    spec: String,
}

pub enum ShimKind {
    Method,
    Function,
}

/// Registry of function shims loaded by the user. Substitutes path to the function/method with a
/// code definition name and a spec name.
pub struct ShimRegistry<'a> {
    /// path to the Rust def, code name, and spec name
    shims: Vec<(Path<'a>, ShimKind, String, String)>,
}

impl<'a> ShimRegistry<'a> {
    pub fn new(arena: &'a Arena<String>) -> std::result::Result<ShimRegistry<'a>, String> {
        let mut shims = Vec::new();

        match rrconfig::shim_file() {
            None => (),
            Some(file) => {
                let f = File::open(file).map_err(|a| a.to_string())?;
                let reader = BufReader::new(f);
                let deser: serde_json::Value = serde_json::from_reader(reader).unwrap();

                let v: Vec<serde_json::Value> = match deser {
                    serde_json::Value::Array(v) => {
                        v
                    },
                    _ => {
                        return Err("not a vector".to_string())
                    }
                };

                for i in v.into_iter() {
                    let b: ShimFileEntry = serde_json::value::from_value(i).map_err(|e| e.to_string())?;

                    let mut path = Vec::new();
                    for pc in b.path.into_iter() {
                        let pc = arena.alloc(pc);
                        path.push(pc.as_str());
                    }
                    let kind;
                    match b.kind.as_str() {
                        "function" => kind = ShimKind::Function,
                        "method" => kind = ShimKind::Method,
                        _ => return Err("unknown kind".to_string()),
                    }
                    shims.push((path, kind, b.name, b.spec));
                }
            },
        }

        let reg = ShimRegistry { shims };
        Ok(reg)
    }

    pub fn get_shims(&self) -> &[(Path<'a>, ShimKind, String, String)] {
        &self.shims
    }
}
