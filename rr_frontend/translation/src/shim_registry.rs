// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Registry of shims for Rust functions that get mapped to custom RefinedRust
/// implementations.
/// Provides deserialization from a JSON file defining this registry.
extern crate serde_json;

use std::fs::File;
use std::io::{BufReader, BufWriter};

use log::info;
use serde::{Deserialize, Serialize};
use typed_arena::Arena;

type Path<'a> = Vec<&'a str>;

/// A file entry for a function/method shim.
#[derive(Serialize, Deserialize)]
struct ShimFunctionEntry {
    /// The rustc path for this symbol.
    path: Vec<String>,
    /// a kind: either "method" or "function"
    kind: String,
    /// the basis name to use for generated Coq names
    name: String,
    /// the Coq name of the spec
    spec: String,
}

/// A file entry for an adt shim.
#[derive(Serialize, Deserialize)]
struct ShimAdtEntry {
    /// The rustc path for this symbol.
    path: Vec<String>,
    /// always "adt"
    kind: String,
    /// the Coq name of the syntactic type
    syntype: String,
    /// the Coq name of the refinement type
    rtype: String,
    /// the Coq name of the semantic type
    semtype: String,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ShimKind {
    Method,
    Function,
    Adt,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct FunctionShim<'a> {
    pub path: Path<'a>,
    pub is_method: bool,
    pub name: String,
    pub spec_name: String,
}

impl<'a> Into<ShimFunctionEntry> for FunctionShim<'a> {
    fn into(self) -> ShimFunctionEntry {
        ShimFunctionEntry {
            path: self.path.iter().map(|x| x.to_string()).collect(),
            kind: if self.is_method { "method".to_string() } else { "function".to_string() },
            name: self.name,
            spec: self.spec_name,
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct AdtShim<'a> {
    pub path: Path<'a>,
    pub refinement_type: String,
    pub syn_type: String,
    pub sem_type: String,
}

impl<'a> Into<ShimAdtEntry> for AdtShim<'a> {
    fn into(self) -> ShimAdtEntry {
        ShimAdtEntry {
            path: self.path.iter().map(|x| x.to_string()).collect(),
            kind: "adt".to_string(),
            syntype: self.syn_type,
            semtype: self.sem_type,
            rtype: self.refinement_type,
        }
    }
}

pub struct ModuleSummary<'a> {
    /// function/method shims
    function_shims: Vec<FunctionShim<'a>>,
    /// adt shims
    adt_shims: Vec<AdtShim<'a>>,
}

/// Registry of function shims loaded by the user. Substitutes path to the function/method with a
/// code definition name and a spec name.
pub struct ShimRegistry<'a> {
    arena: &'a Arena<String>,
    /// function/method shims
    function_shims: Vec<FunctionShim<'a>>,
    /// adt shims
    adt_shims: Vec<AdtShim<'a>>,
    /// extra imports
    imports: Vec<radium::specs::CoqPath>,
}

impl<'a> ShimRegistry<'a> {
    fn get_shim_kind(v: &serde_json::Value) -> Result<ShimKind, String> {
        let obj = v.as_object().ok_or(format!("element is not an object"))?;
        let vk = obj.get("kind").ok_or(format!("object does not have \"kind\" attribute"))?;
        let kind_str = vk.as_str().ok_or(format!("\"kind\" attribute is not a string"))?;
        match kind_str {
            "function" => Ok(ShimKind::Function),
            "method" => Ok(ShimKind::Method),
            "adt" => Ok(ShimKind::Adt),
            k => Err(format!("unknown kind {:?}", k)),
        }
    }

    pub fn intern_path(&self, p: Vec<String>) -> Path<'a> {
        let mut path = Vec::new();
        for pc in p.into_iter() {
            let pc = self.arena.alloc(pc);
            path.push(pc.as_str());
        }
        path
    }

    pub fn empty(arena: &'a Arena<String>) -> Self {
        Self {
            arena,
            function_shims: Vec::new(),
            adt_shims: Vec::new(),
            imports: Vec::new(),
        }
    }

    pub fn new(arena: &'a Arena<String>) -> std::result::Result<ShimRegistry<'a>, String> {
        let mut reg = Self::empty(arena);

        match rrconfig::shim_file() {
            None => (),
            Some(file) => {
                let f = File::open(file).map_err(|a| a.to_string())?;
                reg.add_source(f)?;
            },
        }

        Ok(reg)
    }

    pub fn add_source(&mut self, f: File) -> Result<(), String> {
        let reader = BufReader::new(f);
        let deser: serde_json::Value = serde_json::from_reader(reader).unwrap();

        // We support both directly giving the items array, or also specifying a path to import
        let v: Vec<serde_json::Value>;
        match deser {
            serde_json::Value::Object(obj) => {
                let path =
                    obj.get("refinedrust_path").ok_or(format!("Missing attribute \"refinedrust_path\""))?;
                let path =
                    path.as_str().ok_or(format!("Expected string for \"refinedrust_path\" attribute"))?;

                let module = obj
                    .get("refinedrust_module")
                    .ok_or(format!("Missing attribute \"refinedrust_module\""))?;
                let module =
                    module.as_str().ok_or(format!("Expected string for \"refinedrust_module\" attribute"))?;

                let name =
                    obj.get("refinedrust_name").ok_or(format!("Missing attribute \"refinedrust_name\""))?;
                let _name =
                    name.as_str().ok_or(format!("Expected string for \"refinedrust_name\" attribute"))?;

                let coq_path = radium::specs::CoqPath {
                    path: Some(path.to_string()),
                    module: module.to_string(),
                };
                self.imports.push(coq_path);

                let arr = obj.get("items").ok_or(format!("Missing attribute \"items\""))?;
                let arr = arr.as_array().ok_or(format!("Expected array for \"items\" attribute"))?;
                v = arr.clone();
            },
            serde_json::Value::Array(arr) => {
                v = arr;
            },
            _ => return Err("invalid Json format".to_string()),
        }

        for i in v.into_iter() {
            let kind = Self::get_shim_kind(&i)?;
            if kind == ShimKind::Adt {
                let b: ShimAdtEntry = serde_json::value::from_value(i).map_err(|e| e.to_string())?;
                let path = self.intern_path(b.path);
                let entry = AdtShim {
                    path,
                    syn_type: b.syntype,
                    sem_type: b.semtype,
                    refinement_type: b.rtype,
                };

                self.adt_shims.push(entry);
            } else {
                let b: ShimFunctionEntry = serde_json::value::from_value(i).map_err(|e| e.to_string())?;
                let path = self.intern_path(b.path);
                let entry = FunctionShim {
                    path,
                    is_method: kind == ShimKind::Method,
                    name: b.name,
                    spec_name: b.spec,
                };

                self.function_shims.push(entry);
            }
        }

        Ok(())
    }

    pub fn get_function_shims(&self) -> &[FunctionShim] {
        &self.function_shims
    }

    pub fn get_adt_shims(&self) -> &[AdtShim] {
        &self.adt_shims
    }

    pub fn get_extra_imports(&self) -> &[radium::specs::CoqPath] {
        &self.imports
    }
}

/// Write serialized representation of shims to a file.
pub fn write_shims<'a>(
    f: File,
    load_path: &str,
    load_module: &str,
    name: &str,
    adt_shims: Vec<AdtShim<'a>>,
    function_shims: Vec<FunctionShim<'a>>,
) {
    let writer = BufWriter::new(f);

    let mut values = Vec::new();
    for x in adt_shims.into_iter() {
        let x: ShimAdtEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in function_shims.into_iter() {
        let x: ShimFunctionEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }

    let array_val = serde_json::Value::Array(values);

    info!("write_shims: writing entries {:?}", array_val);

    let object = serde_json::json!({
        "refinedrust_path": load_path,
        "refinedrust_module": load_module,
        "refinedrust_name": name,
        "items": array_val
    });

    serde_json::to_writer_pretty(writer, &object).unwrap();
}

/// Check if this file declares a RefinedRust module.
pub fn is_valid_refinedrust_module(f: File) -> Option<String> {
    let reader = BufReader::new(f);
    let deser: serde_json::Value = serde_json::from_reader(reader).unwrap();

    // We support both directly giving the items array, or also specifying a path to import
    let _v: Vec<serde_json::Value>;
    match deser {
        serde_json::Value::Object(obj) => {
            let path = obj.get("refinedrust_path")?;
            let _path = path.as_str()?;

            let module = obj.get("refinedrust_module")?;
            let _module = module.as_str()?;

            let name = obj.get("refinedrust_name")?;
            let name = name.as_str()?;

            Some(name.to_string())
        },
        _ => None,
    }
}
