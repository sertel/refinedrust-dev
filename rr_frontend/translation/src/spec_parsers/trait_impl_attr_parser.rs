// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use attribute_parse::{parse, MToken};
use rr_rustc_interface::ast::ast::AttrItem;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::*;

/// Parse attributes on a trait.
/// Permitted attributes:
/// - `rr::instantiate("x" := "True")`, which will instantiate a specification attribute "x" to a given term
///   "True"
pub trait TraitImplAttrParser {
    fn parse_trait_impl_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<TraitImplAttrs, String>;
}

#[derive(Clone, Debug)]
pub struct TraitImplAttrs {
    pub attrs: radium::TraitSpecAttrsInst,
}

#[allow(clippy::module_name_repetitions)]
pub struct VerboseTraitImplAttrParser<'a, T> {
    scope: &'a T,
}

impl<'a, T> VerboseTraitImplAttrParser<'a, T> {
    pub const fn new(scope: &'a T) -> Self {
        Self { scope }
    }
}

impl<'b, T: ParamLookup> TraitImplAttrParser for VerboseTraitImplAttrParser<'b, T> {
    fn parse_trait_impl_attrs<'a>(&'a mut self, attrs: &'a [&'a AttrItem]) -> Result<TraitImplAttrs, String> {
        let mut trait_attrs = HashMap::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&it.args.inner_tokens());

            match seg.ident.name.as_str() {
                "instantiate" => {
                    let parsed_name: IdentOrTerm = buffer.parse(&()).map_err(str_err)?;
                    buffer.parse::<_, MToken![:]>(&()).map_err(str_err)?;
                    buffer.parse::<_, MToken![=]>(&()).map_err(str_err)?;
                    let parsed_term: parse::LitStr = buffer.parse(self.scope).map_err(str_err)?;
                    let (parsed_term, _) = process_coq_literal(&parsed_term.value(), self.scope);
                    if trait_attrs
                        .insert(parsed_name.to_string(), radium::coq::term::Gallina::Literal(parsed_term))
                        .is_some()
                    {
                        return Err(format!(
                            "attribute {} has been instantiated multiple times",
                            parsed_name.to_string()
                        ));
                    }
                },
                "export_as" | "only_spec" | "trust_me" => (),
                _ => {
                    return Err(format!("unknown attribute for trait impl specification: {:?}", args));
                },
            }
        }

        Ok(TraitImplAttrs {
            attrs: radium::TraitSpecAttrsInst::new(trait_attrs),
        })
    }
}
