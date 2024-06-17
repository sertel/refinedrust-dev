// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use attribute_parse::{parse, MToken};
use parse::Peek;
use radium::{coq, specs};
use rr_rustc_interface::ast::ast::{AttrArgs, AttrItem};

use crate::spec_parsers::parse_utils::*;

/// An attribute spec parser handles the parsing of the attributes of the whole enum and relevant
/// attributes on the variants at once.
///
/// Supported attributes for the whole enum:
/// - `rr::refined_by`: specifies the refinement type
///
/// Supported attributes for the enum variants:
/// - `rr::pattern`: specifies the Coq pattern of the refinement type that matches this variant
/// - `rr::refinement`: specifies the refinement of the struct for this variant in the scope introduced by the
///   pattern. Can be omitted if the variant does not have any fields.
pub trait EnumSpecParser {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a AttrItem],
        variant_attrs: &[Vec<&'a AttrItem>],
    ) -> Result<specs::EnumSpec, String>;
}

#[derive(Debug)]
pub struct EnumPattern {
    pub pat: String,
    pub args: Vec<String>,
}

impl<T: ParamLookup> parse::Parse<T> for EnumPattern {
    fn parse(input: parse::Stream, meta: &T) -> parse::Result<Self> {
        // parse the pattern
        let pat: parse::LitStr = input.parse(meta)?;
        let (pat, _) = process_coq_literal(&pat.value(), meta);

        let args: Vec<String> = if parse::Dollar::peek(input) {
            // optionally parse args
            input.parse::<_, MToken![$]>(meta)?;

            // parse a sequence of args
            let parsed_args: parse::Punctuated<parse::LitStr, MToken![,]> =
                parse::Punctuated::<_, _>::parse_terminated(input, meta)?;

            parsed_args
                .into_iter()
                .map(|s| {
                    let (arg, _) = process_coq_literal(&s.value(), meta);
                    arg
                })
                .collect()
        } else {
            Vec::new()
        };

        Ok(Self { pat, args })
    }
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseEnumSpecParser<'a, T> {
    scope: &'a T,
}

impl<'a, T: ParamLookup> VerboseEnumSpecParser<'a, T> {
    pub const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'b, T: ParamLookup> EnumSpecParser for VerboseEnumSpecParser<'b, T> {
    fn parse_enum_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a AttrItem],
        variant_attrs: &[Vec<&'a AttrItem>],
    ) -> Result<specs::EnumSpec, String> {
        let mut variant_patterns: Vec<(String, Vec<String>, String)> = Vec::new();
        let mut rfn_type = None;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());
            match seg.ident.name.as_str() {
                "refined_by" => {
                    let ty: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                    let (ty, _) = process_coq_literal(ty.value().as_str(), self.scope);
                    rfn_type = Some(coq::term::Type::Literal(ty));
                },
                "export_as" => {},
                _ => {
                    return Err(format!("unknown attribute for enum specification: {:?}", args));
                },
            }
        }

        // parse the variant patterns
        for attrs in variant_attrs {
            let mut pattern = None;
            let mut refinement = None;
            for &it in attrs {
                let path_segs = &it.path.segments;

                let Some(seg) = path_segs.get(1) else {
                    continue;
                };

                let buffer = parse::Buffer::new(&it.args.inner_tokens());
                match seg.ident.name.as_str() {
                    "pattern" => {
                        let pat: EnumPattern = buffer.parse(self.scope).map_err(str_err)?;
                        pattern = Some(pat);
                    },
                    "refinement" => {
                        let rfn: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                        let (rfn, _) = process_coq_literal(rfn.value().as_str(), self.scope);
                        refinement = Some(rfn);
                    },
                    _ => {
                        // skip and ignore other attributes
                    },
                }
            }

            if let Some(pattern) = pattern {
                let refinement = refinement.unwrap_or_else(|| "-[]".to_owned());
                variant_patterns.push((pattern.pat, pattern.args, refinement));
            }
        }

        let Some(rfn_type) = rfn_type else {
            return Err(format!("No refined_by clause provided for enum {:?}", ty_name));
        };

        Ok(specs::EnumSpec {
            rfn_type,
            variant_patterns,
        })
    }
}

/// Parse the arguments of a `rr::refine_as` annotation.
/// Returns the optional specified name.
pub fn parse_enum_refine_as(attrs: &AttrArgs) -> Result<Option<String>, String> {
    let buffer = parse::Buffer::new(&attrs.inner_tokens());

    if matches!(attrs, AttrArgs::Empty) {
        Ok(None)
    } else {
        let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
        Ok(Some(name.value()))
    }
}
