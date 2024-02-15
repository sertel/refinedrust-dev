// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse as parse;
use radium::specs;
use rustc_ast::ast::AttrItem;

use crate::spec_parsers::parse_utils;

/// Parse attributes on a crate.
/// Permitted attributes:
/// - rr::import("A.B.C", "D"), which will import the Coq path "A.B.C.D"
pub trait CrateAttrParser {
    fn parse_crate_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<CrateAttrs, String>;
}

#[derive(Debug, Clone)]
pub struct CrateAttrs {
    pub imports: Vec<specs::CoqPath>,
    pub prefix: Option<String>,
    pub includes: Vec<String>,
}

pub struct VerboseCrateAttrParser {}

impl VerboseCrateAttrParser {
    pub fn new() -> Self {
        VerboseCrateAttrParser {}
    }
}

impl CrateAttrParser for VerboseCrateAttrParser {
    fn parse_crate_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<CrateAttrs, String> {
        fn str_err(e: parse::ParseError) -> String {
            format!("{:?}", e)
        }

        let meta = ();
        let mut imports: Vec<specs::CoqPath> = Vec::new();
        let mut includes: Vec<String> = Vec::new();
        let mut prefix: Option<String> = None;

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
                    "include" => {
                        let name: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        includes.push(name.value());
                    },
                    "coq_prefix" => {
                        let path: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        if let Some(_) = prefix {
                            return Err(format!("multiple rr::coq_prefix attributes have been provided"));
                        }
                        prefix = Some(path.value().to_string());
                    },
                    _ => {
                        return Err(format!("unknown attribute for crate specification: {:?}", args));
                    },
                }
            }
        }
        Ok(CrateAttrs {
            imports,
            prefix,
            includes,
        })
    }
}
