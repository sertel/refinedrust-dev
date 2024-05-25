// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Registry of shims for Rust functions that get mapped to custom `RefinedRust`
/// implementations.
/// Provides deserialization from a JSON file defining this registry.
extern crate serde_json;

use std::fs::File;
use std::io::{BufReader, BufWriter};

use log::info;
use radium::coq;
use serde::{Deserialize, Serialize};
use typed_arena::Arena;

use crate::utils::*;

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

#[derive(Serialize, Deserialize)]
struct ShimTraitMethodImplEntry {
    /// The rustc path for the trait
    trait_path: PathWithArgs,
    /// for which type is this implementation?
    for_type: FlatType,
    /// The method identifier
    method_ident: String,
    /// a kind: always "trait_method"
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

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ShimKind {
    Method,
    Function,
    TraitMethod,
    Adt,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FunctionShim<'a> {
    pub path: Path<'a>,
    pub is_method: bool,
    pub name: String,
    pub spec_name: String,
}

impl<'a> From<FunctionShim<'a>> for ShimFunctionEntry {
    fn from(shim: FunctionShim<'a>) -> Self {
        Self {
            path: shim.path.iter().map(|x| (*x).to_owned()).collect(),
            kind: if shim.is_method { "method".to_owned() } else { "function".to_owned() },
            name: shim.name,
            spec: shim.spec_name,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TraitMethodImplShim {
    pub trait_path: PathWithArgs,
    pub method_ident: String,
    pub for_type: FlatType,
    pub name: String,
    pub spec_name: String,
}

impl From<TraitMethodImplShim> for ShimTraitMethodImplEntry {
    fn from(shim: TraitMethodImplShim) -> Self {
        Self {
            trait_path: shim.trait_path,
            method_ident: shim.method_ident,
            for_type: shim.for_type,
            kind: "trait_method".to_owned(),
            name: shim.name,
            spec: shim.spec_name,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AdtShim<'a> {
    pub path: Path<'a>,
    pub refinement_type: String,
    pub syn_type: String,
    pub sem_type: String,
}

impl<'a> From<AdtShim<'a>> for ShimAdtEntry {
    fn from(shim: AdtShim<'a>) -> Self {
        Self {
            path: shim.path.iter().map(|x| (*x).to_owned()).collect(),
            kind: "adt".to_owned(),
            syntype: shim.syn_type,
            semtype: shim.sem_type,
            rtype: shim.refinement_type,
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

    /// trait method implementation shims
    trait_method_shims: Vec<TraitMethodImplShim>,

    /// adt shims
    adt_shims: Vec<AdtShim<'a>>,

    /// extra exports
    exports: Vec<coq::Export>,

    /// extra module dependencies
    dependencies: Vec<coq::Path>,
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
            "trait_method" => Ok(ShimKind::TraitMethod),
            k => Err(format!("unknown kind {:?}", k)),
        }
    }

    pub fn intern_path(&self, p: Vec<String>) -> Path<'a> {
        let mut path = Vec::new();
        for pc in p {
            let pc = self.arena.alloc(pc);
            path.push(pc.as_str());
        }
        path
    }

    pub fn empty(arena: &'a Arena<String>) -> Self {
        Self {
            arena,
            function_shims: Vec::new(),
            trait_method_shims: Vec::new(),
            adt_shims: Vec::new(),
            exports: Vec::new(),
            dependencies: Vec::new(),
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
        let v = match deser {
            serde_json::Value::Object(obj) => {
                let path = obj
                    .get("refinedrust_path")
                    .ok_or(format!("Missing attribute \"refinedrust_path\""))?
                    .as_str()
                    .ok_or(format!("Expected string for \"refinedrust_path\" attribute"))?;

                let module = obj
                    .get("refinedrust_module")
                    .ok_or(format!("Missing attribute \"refinedrust_module\""))?
                    .as_str()
                    .ok_or(format!("Expected string for \"refinedrust_module\" attribute"))?;

                let _ = obj
                    .get("refinedrust_name")
                    .ok_or(format!("Missing attribute \"refinedrust_name\""))?
                    .as_str()
                    .ok_or(format!("Expected string for \"refinedrust_name\" attribute"))?;

                let module = coq::Module::new_with_path(module, coq::Path::new(path));
                self.exports.push(coq::Export::new(module));

                let dependencies = obj
                    .get("module_dependencies")
                    .ok_or(format!("Missing attribute \"module_dependencies\""))?
                    .as_array()
                    .ok_or(format!("Expected array for \"module_dependencies\" attribute"))?;

                for dependency in dependencies {
                    let path = dependency
                        .as_str()
                        .ok_or(format!("Expected string for element of \"module_dependencies\" array"))?;

                    self.dependencies.push(coq::Path::new(path));
                }

                obj.get("items")
                    .ok_or(format!("Missing attribute \"items\""))?
                    .as_array()
                    .ok_or(format!("Expected array for \"items\" attribute"))?
                    .clone()
            },

            serde_json::Value::Array(arr) => arr,

            _ => return Err("invalid Json format".to_owned()),
        };

        for i in v {
            let kind = Self::get_shim_kind(&i)?;

            match kind {
                ShimKind::Adt => {
                    let b: ShimAdtEntry = serde_json::value::from_value(i).map_err(|e| e.to_string())?;
                    let path = self.intern_path(b.path);
                    let entry = AdtShim {
                        path,
                        syn_type: b.syntype,
                        sem_type: b.semtype,
                        refinement_type: b.rtype,
                    };

                    self.adt_shims.push(entry);
                },
                ShimKind::Function | ShimKind::Method => {
                    let b: ShimFunctionEntry = serde_json::value::from_value(i).map_err(|e| e.to_string())?;
                    let path = self.intern_path(b.path);
                    let entry = FunctionShim {
                        path,
                        is_method: kind == ShimKind::Method,
                        name: b.name,
                        spec_name: b.spec,
                    };

                    self.function_shims.push(entry);
                },
                ShimKind::TraitMethod => {
                    let b: ShimTraitMethodImplEntry =
                        serde_json::value::from_value(i).map_err(|e| e.to_string())?;
                    let entry = TraitMethodImplShim {
                        trait_path: b.trait_path,
                        method_ident: b.method_ident,
                        for_type: b.for_type,
                        name: b.name,
                        spec_name: b.spec,
                    };

                    self.trait_method_shims.push(entry);
                },
            }
        }

        Ok(())
    }

    pub fn get_function_shims(&self) -> &[FunctionShim] {
        &self.function_shims
    }

    pub fn get_trait_method_shims(&self) -> &[TraitMethodImplShim] {
        &self.trait_method_shims
    }

    pub fn get_adt_shims(&self) -> &[AdtShim] {
        &self.adt_shims
    }

    pub fn get_extra_exports(&self) -> &[coq::Export] {
        &self.exports
    }

    pub fn get_extra_dependencies(&self) -> &[coq::Path] {
        &self.dependencies
    }
}

/// Write serialized representation of shims to a file.
pub fn write_shims<'a>(
    f: File,
    load_path: &str,
    load_module: &str,
    name: &str,
    module_dependencies: &[coq::Path],
    adt_shims: Vec<AdtShim<'a>>,
    function_shims: Vec<FunctionShim<'a>>,
    trait_method_shims: Vec<TraitMethodImplShim>,
) {
    let writer = BufWriter::new(f);

    let mut values = Vec::new();
    for x in adt_shims {
        let x: ShimAdtEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in function_shims {
        let x: ShimFunctionEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }
    for x in trait_method_shims {
        let x: ShimTraitMethodImplEntry = x.into();
        values.push(serde_json::to_value(x).unwrap());
    }

    let array_val = serde_json::Value::Array(values);

    info!("write_shims: writing entries {:?}", array_val);

    let module_dependencies: Vec<_> = module_dependencies.iter().map(ToString::to_string).collect();

    let object = serde_json::json!({
        "refinedrust_path": load_path,
        "refinedrust_module": load_module,
        "refinedrust_name": name,
        "module_dependencies": module_dependencies,
        "items": array_val
    });

    serde_json::to_writer_pretty(writer, &object).unwrap();
}

/// Check if this file declares a `RefinedRust` module.
pub fn is_valid_refinedrust_module(f: File) -> Option<String> {
    let reader = BufReader::new(f);
    let deser: serde_json::Value = serde_json::from_reader(reader).unwrap();

    // We support both directly giving the items array, or also specifying a path to import
    match deser {
        serde_json::Value::Object(obj) => {
            let path = obj.get("refinedrust_path")?;
            let _path = path.as_str()?;

            let module = obj.get("refinedrust_module")?;
            let _module = module.as_str()?;

            let name = obj.get("refinedrust_name")?;
            let name = name.as_str()?;

            Some(name.to_owned())
        },
        _ => None,
    }
}
