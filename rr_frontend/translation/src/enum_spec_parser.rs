// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use rustc_ast::ast::AttrItem;
use crate::caesium::specs as specs;

use crate::parse as parse;
use crate::parse_utils::*;

/// An attribute spec parser handles the parsing of the attributes of the whole enum and relevant
/// attributes on the variants at once.
///
/// Supported attributes for the whole enum:
/// - rr::refined_by: specifies the refinement type
///
/// Supported attributes for the enum variants:
/// - rr::pattern: specifies the Coq pattern of the refinement type that matches this variant
/// - rr::refinement: specifies the refinement of the struct for this variant in the scope
///     introduced by the pattern. Can be omitted if the variant does not have any fields.
pub trait EnumSpecParser {
    fn parse_enum_spec<'a>(&'a mut self, ty_name: &str, attrs: &'a[&'a AttrItem], variant_attrs: &[Vec<&'a AttrItem>], params: &'a [specs::TyParamNames], lfts: &'a [(Option<String>, specs::Lft)]) -> Result<specs::EnumSpec, String>;
}

pub struct VerboseEnumSpecParser {
}

impl VerboseEnumSpecParser {
    pub fn new() -> Self {
        VerboseEnumSpecParser {}
    }
}

impl EnumSpecParser for VerboseEnumSpecParser {
    fn parse_enum_spec<'a>(&'a mut self, ty_name: &str, attrs: &'a[&'a AttrItem],
                           variant_attrs: &[Vec<&'a AttrItem>],
                           params: &'a [specs::TyParamNames],
                           lfts: &'a [(Option<String>, specs::Lft)]) -> Result<specs::EnumSpec, String> {
        fn str_err(e : parse::ParseError) -> String {
            format!("{:?}", e)
        }
        let meta = (params, lfts);

        let mut variant_patterns: Vec<(String, String)> = Vec::new();
        let mut rfn_type = None;

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                match &*seg.ident.name.as_str() {
                    "refined_by" => {
                        let ty: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                        let (ty, _) = process_coq_literal(ty.value().as_str(), meta);
                        rfn_type = Some(specs::CoqType::Literal(ty));
                    },
                    _ => {
                        return Err(format!("unknown attribute for enum specification: {:?}", args));
                    },
                }
            }
        }

        // parse the variant patterns
        for attrs in variant_attrs.iter() {
            let mut pattern = None;
            let mut refinement = None;
            for &it in attrs.iter() {
                let ref path_segs = it.path.segments;

                if let Some(seg) = path_segs.get(1) {
                    let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                    match &*seg.ident.name.as_str() {
                        "pattern" => {
                            let pat: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                            let (pat, _) = process_coq_literal(pat.value().as_str(), meta);
                            pattern = Some(pat);
                        },
                        "refinement" => {
                            let rfn: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                            let (rfn, _) = process_coq_literal(rfn.value().as_str(), meta);
                            refinement = Some(rfn);
                        },
                        _ => {
                            // skip and ignore other attributes
                            ()
                        },
                    }
                }
            }
            if let Some(pattern) = pattern {
                let refinement = refinement.unwrap_or("-[]".to_string());
                variant_patterns.push((pattern, refinement));
            }

        }

        if let Some(rfn_type) = rfn_type {
            let enum_spec = specs::EnumSpec {
                rfn_type,
                variant_patterns,
            };
            Ok(enum_spec)
        }
        else {
            Err(format!("No refined_by clause provided for enum {:?}", ty_name))
        }
    }
}

