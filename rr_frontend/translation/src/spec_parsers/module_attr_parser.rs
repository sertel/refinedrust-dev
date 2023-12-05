// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rustc_ast::ast::AttrItem;
use rustc_hir::{def_id::DefId, def_id::LocalDefId};
use radium::specs as specs;
use crate::spec_parsers::parse_utils;

use attribute_parse as parse;



/// Parse attributes on a module.
/// Permitted attributes:
/// - rr::import("A.B.C", "D"), which will import the Coq path "A.B.C.D"
pub trait ModuleAttrParser {
    fn parse_module_attrs<'a>(&'a mut self, did: LocalDefId, attrs: &'a[&'a AttrItem]) -> Result<ModuleAttrs, String>;
}

#[derive(Debug, Clone)]
pub struct ModuleAttrs {
    pub imports: Vec<specs::CoqPath>,
}

pub struct VerboseModuleAttrParser {
}

impl VerboseModuleAttrParser {
    pub fn new() -> Self {
        VerboseModuleAttrParser {}
    }
}

impl ModuleAttrParser for VerboseModuleAttrParser {
    fn parse_module_attrs<'a>(&'a mut self, _did: LocalDefId, attrs: &'a[&'a AttrItem]) -> Result<ModuleAttrs, String> {
        fn str_err(e : parse::ParseError) -> String {
            format!("{:?}", e)
        }

        let meta = ();
        let mut imports: Vec<specs::CoqPath> = Vec::new();

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                match &*seg.ident.name.as_str() {
                    "import" => {
                        let path: parse_utils::CoqPath = buffer.parse(&meta).map_err(str_err)?;
                        imports.push(path.into());
                    },
                    _ => {
                        return Err(format!("unknown attribute for module specification: {:?}", args));
                    },
                }
            }
        }
        Ok(ModuleAttrs { imports })
    }
}