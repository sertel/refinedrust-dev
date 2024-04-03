// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use attribute_parse as parse;
/// Parsing of RefinedRust struct specifications.
use log::info;
use parse::{Parse, Peek};
use radium::specs;
use rustc_ast::ast::AttrItem;

use crate::spec_parsers::parse_utils::*;

pub trait InvariantSpecParser {
    /// Parse attributes as an invariant type specification.
    /// `ty_name` is the name of the type to generate.
    /// `params` are the type parameters of the surrounded type.
    ///
    /// Supported attributes on the invariant definition (outer):
    /// - rr::refined_by
    /// - rr::exists
    /// - rr::invariant
    /// - rr::refines for the inner refinement
    /// - rr::context for context items that are required to be available in the definition
    ///
    /// Returns whether a Boolean stating whether a rr::refines attribute was included.
    fn parse_invariant_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a AttrItem],
        params: &'a [specs::LiteralTyParam],
        lfts: &'a [(Option<String>, specs::Lft)],
    ) -> Result<(specs::InvariantSpec, bool), String>;
}

/// Parse a binder pattern with an optional Coq type annotation, e.g.
/// `"(x, y)" : "(Z * Z)%type"`
struct RfnPattern {
    rfn_pat: specs::CoqPattern,
    rfn_type: Option<specs::CoqType>,
}

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for RfnPattern {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        let pat = parse::LitStr::parse(input, meta)?;
        let (pat, _) = process_coq_literal(pat.value().as_str(), *meta);

        // optionally, parse a type annotation (otherwise, let Coq inference do its thing)
        if parse::Colon::peek(input) {
            input.parse::<_, parse::MToken![:]>(meta)?;
            let ty: parse::LitStr = input.parse(meta)?;
            let (ty, _) = process_coq_literal(ty.value().as_str(), *meta);
            Ok(RfnPattern {
                rfn_pat: pat,
                rfn_type: Some(specs::CoqType::Literal(ty)),
            })
        } else {
            Ok(RfnPattern {
                rfn_pat: pat,
                rfn_type: None,
            })
        }
    }
}

/// Representation of the IProps that can appear in an invariant clause.
enum MetaIProp {
    /// #[rr::invariant("..")] or #[rr::invariant("H" : "..")]
    Pure(String, Option<String>),
    /// #[rr::invariant(#iris "..")]
    Iris(specs::IProp),
    /// #[rr::invariant(#type "l" : "rfn" @ "ty")]
    Type(specs::TyOwnSpec),
    /// #[rr::invariant(#own "...")] (only for the Owned predicate)
    Own(specs::IProp),
    /// #[rr::invariant(#shr "...")] (only for the Shared predicate)
    Shared(specs::IProp),
}

impl<'tcx, 'a> parse::Parse<ParseMeta<'a>> for MetaIProp {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        if parse::Pound::peek(input) {
            input.parse::<_, parse::MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "iris" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(MetaIProp::Iris(prop.into()))
                },
                "own" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(MetaIProp::Own(prop.into()))
                },
                "shr" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(MetaIProp::Shared(prop.into()))
                },
                "type" => {
                    let loc_str: parse::LitStr = input.parse(meta)?;
                    let (loc_str, mut annot_meta) = process_coq_literal(&loc_str.value(), *meta);

                    input.parse::<_, parse::MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = input.parse(meta)?;
                    let (rfn_str, annot_meta2) = process_coq_literal(&rfn_str.value(), *meta);

                    annot_meta.join(&annot_meta2);

                    input.parse::<_, parse::MToken![@]>(meta)?;

                    let type_str: parse::LitStr = input.parse(meta)?;
                    let (type_str, annot_meta3) = process_coq_literal(&type_str.value(), *meta);

                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, true, annot_meta);
                    Ok(MetaIProp::Type(spec))
                },
                _ => {
                    panic!("invalid macro command: {:?}", macro_cmd.value());
                },
            }
        } else {
            let name_or_prop_str: parse::LitStr = input.parse(meta)?;
            if parse::Colon::peek(input) {
                // this is a name
                let name_str = name_or_prop_str.value();

                input.parse::<_, parse::MToken![:]>(meta)?;

                let pure_prop: parse::LitStr = input.parse(meta)?;
                let (pure_str, _annot_meta) = process_coq_literal(&pure_prop.value(), *meta);
                // TODO: should we use annot_meta?

                Ok(MetaIProp::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let (lit, _) = process_coq_literal(&name_or_prop_str.value(), *meta);
                Ok(MetaIProp::Pure(lit, None))
            }
        }
    }
}

pub struct InvariantSpecFlags(specs::InvariantSpecFlags);
impl Into<specs::InvariantSpecFlags> for InvariantSpecFlags {
    fn into(self) -> specs::InvariantSpecFlags {
        self.0
    }
}

impl<'tcx, U> parse::Parse<U> for InvariantSpecFlags {
    fn parse(input: parse::ParseStream, meta: &U) -> parse::ParseResult<Self> {
        let mode: parse::Ident = input.parse(meta)?;
        match mode.value().as_str() {
            "persistent" => Ok(InvariantSpecFlags(specs::InvariantSpecFlags::Persistent)),
            "plain" => Ok(InvariantSpecFlags(specs::InvariantSpecFlags::Plain)),
            "na" => Ok(InvariantSpecFlags(specs::InvariantSpecFlags::NonAtomic)),
            "atomic" => Ok(InvariantSpecFlags(specs::InvariantSpecFlags::Atomic)),
            _ => {
                panic!("invalid ADT mode: {:?}", mode.value())
            },
        }
    }
}

pub struct VerboseInvariantSpecParser {}

impl VerboseInvariantSpecParser {
    pub fn new() -> Self {
        VerboseInvariantSpecParser {}
    }
}

impl InvariantSpecParser for VerboseInvariantSpecParser {
    fn parse_invariant_spec<'a>(
        &'a mut self,
        ty_name: &str,
        attrs: &'a [&'a AttrItem],
        params: &'a [specs::LiteralTyParam],
        lfts: &'a [(Option<String>, specs::Lft)],
    ) -> Result<(specs::InvariantSpec, bool), String> {
        fn str_err(e: parse::ParseError) -> String {
            format!("{:?}", e)
        }

        if attrs.len() == 0 {
            return Err(format!("no invariant specifications given"));
        }

        let meta: ParseMeta<'_> = (params, lfts);

        let mut invariants: Vec<(specs::IProp, specs::InvariantMode)> = Vec::new();
        let mut type_invariants: Vec<specs::TyOwnSpec> = Vec::new();
        let mut abstracted_refinement = None;

        let mut rfn_pat = "placeholder_pat".to_string();
        let mut rfn_type = specs::CoqType::Infer;

        let mut existentials: Vec<RRParam> = Vec::new();

        // use Plain as the default
        let mut inv_flags = specs::InvariantSpecFlags::Plain;

        let mut params: Vec<specs::CoqParam> = Vec::new();

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&args.inner_tokens());
                match &*seg.ident.name.as_str() {
                    "refined_by" => {
                        let pat = RfnPattern::parse(&buffer, &meta).map_err(str_err)?;
                        rfn_pat = pat.rfn_pat;
                        match pat.rfn_type {
                            Some(ty) => rfn_type = ty,
                            None => (),
                        }
                    },
                    "invariant" => {
                        let prop = MetaIProp::parse(&buffer, &meta).map_err(str_err)?;
                        match prop {
                            MetaIProp::Own(iprop) => {
                                invariants.push((iprop, specs::InvariantMode::OnlyOwned));
                            },
                            MetaIProp::Shared(iprop) => {
                                invariants.push((iprop, specs::InvariantMode::OnlyShared));
                            },
                            MetaIProp::Iris(iprop) => {
                                invariants.push((iprop, specs::InvariantMode::All));
                            },
                            MetaIProp::Type(ty) => {
                                type_invariants.push(ty);
                            },
                            MetaIProp::Pure(p, name) => match name {
                                None => invariants.push((specs::IProp::Pure(p), specs::InvariantMode::All)),
                                Some(n) => invariants
                                    .push((specs::IProp::PureWithName(p, n), specs::InvariantMode::All)),
                            },
                        }
                    },
                    "exists" => {
                        let mut params = RRParams::parse(&buffer, &meta).map_err(str_err)?;
                        existentials.append(&mut params.params);
                    },
                    "mode" => {
                        let mode = InvariantSpecFlags::parse(&buffer, &meta).map_err(str_err)?;
                        inv_flags = mode.into();
                    },
                    "refines" => {
                        let term = IdentOrTerm::parse(&buffer, &meta).map_err(str_err)?;
                        if let Some(_) = abstracted_refinement {
                            return Err("multiple refines specifications given".to_string());
                        } else {
                            abstracted_refinement = Some(term.to_string());
                        }
                    },
                    "context" => {
                        let param = RRCoqContextItem::parse(&buffer, &meta).map_err(str_err)?;
                        params.push(specs::CoqParam::new(
                            specs::CoqName::Unnamed,
                            specs::CoqType::Literal(param.item),
                            true,
                        ));
                    },
                    _ => {
                        //skip, this may be part of an enum spec
                        ()
                    },
                }
            }
        }

        let refinement_included = abstracted_refinement.is_some();

        let spec = specs::InvariantSpec::new(
            ty_name.to_string(),
            inv_flags,
            "κ".to_string(),
            rfn_type,
            rfn_pat,
            existentials.into_iter().map(|a| (a.name, a.ty)).collect(),
            invariants,
            type_invariants,
            abstracted_refinement,
            params,
        );

        Ok((spec, refinement_included))
    }
}

/// A parsed specification for a field.
pub struct StructFieldSpec<'def> {
    /// the (default or annotated) type of the field
    pub ty: specs::Type<'def>,
    /// optional refinement specified here
    pub rfn: Option<String>,
}

pub trait StructFieldSpecParser<'def> {
    /// Parse attributes on a struct field as a type specification.
    /// Supported attributes:
    /// - rr::field([r @ ] type)
    fn parse_field_spec<'a>(
        &'a mut self,
        field_name: &str,
        attrs: &'a [&'a AttrItem],
    ) -> Result<StructFieldSpec<'def>, String>;
}

/// Parses attributes on a field to a `StructFieldSpec`, using a given default type for the field
/// in case none is annotated.
pub struct VerboseStructFieldSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// The translated Rust field type that is used as a default.
    field_type: &'a specs::Type<'def>,

    /// the type parameters of this struct
    params: &'a [specs::LiteralTyParam],

    lfts: &'a [(Option<String>, specs::Lft)],

    /// whether to expect a refinement to be specified or not
    expect_rfn: bool,

    make_literal: F,
    //ty_scope: &'a [Option<specs::Type<'def>>],
    //rfnty_scope: &'a [Option<specs::CoqType>],
}

impl<'a, 'def, F> VerboseStructFieldSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    pub fn new(
        field_type: &'a specs::Type<'def>,
        params: &'a [specs::LiteralTyParam],
        lfts: &'a [(Option<String>, specs::Lft)],
        expect_rfn: bool,
        make_literal: F,
    ) -> Self {
        Self {
            field_type,
            params,
            lfts,
            expect_rfn,
            make_literal,
        }
    }

    fn make_type(&self, lit: LiteralType, ty: &specs::Type<'def>) -> specs::Type<'def> {
        // literal type given, we use this literal type as the RR semantic type
        // just use the syntype from the Rust type
        let st = ty.get_syn_type();

        // TODO: get CoqType for refinement.
        // maybe have it as an annotation? the Infer is currently a placeholder.
        // we need this in order to be able to specify the invariant spec separately.

        info!("making type: {:?}, {:?}", lit, ty);
        let lit_ty = specs::LiteralType {
            rust_name: None,
            type_term: lit.ty.to_string(),
            refinement_type: specs::CoqType::Infer,
            syn_type: st,
        };
        let lit_ref = (&self.make_literal)(lit_ty);
        let lit_use = specs::LiteralTypeUse::new_with_annot(lit_ref, vec![], lit.meta);

        specs::Type::Literal(lit_use)
    }
}

impl<'a, 'def, F> StructFieldSpecParser<'def> for VerboseStructFieldSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    fn parse_field_spec(
        &mut self,
        field_name: &str,
        attrs: &[&AttrItem],
    ) -> Result<StructFieldSpec<'def>, String> {
        fn str_err(e: parse::ParseError) -> String {
            format!("{:?}", e)
        }

        info!("parsing attributes of field {:?}: {:?}", field_name, attrs);

        let meta = (self.params, self.lfts);

        let mut field_type = None;
        let mut parsed_rfn = None;

        for &it in attrs.iter() {
            let ref path_segs = it.path.segments;
            let ref args = it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&args.inner_tokens());
                match &*seg.ident.name.as_str() {
                    "field" => {
                        let mut expect_ty = false;
                        if self.expect_rfn {
                            let rfn: parse::LitStr = buffer.parse(&meta).map_err(str_err)?;
                            let (rfn, _) = process_coq_literal(rfn.value().as_str(), meta);
                            parsed_rfn = Some(rfn);

                            if parse::At::peek(&buffer) {
                                info!("expecting type");
                                buffer.parse::<_, parse::MToken![@]>(&meta).map_err(str_err)?;
                                expect_ty = true;
                            }
                        } else {
                            expect_ty = true;
                        }

                        if expect_ty {
                            let ty = LiteralType::parse(&buffer, &meta).map_err(str_err)?;
                            if let None = field_type {
                                field_type = Some(self.make_type(ty, self.field_type));
                            } else {
                                return Err(format!(
                                    "field attribute specified twice for field {:?}",
                                    field_name
                                ));
                            }
                        }
                    },
                    _ => {
                        return Err(format!("unknown attribute for struct field specification: {:?}", args));
                    },
                }
            }
        }

        let spec;
        if let Some(ty) = field_type {
            spec = StructFieldSpec {
                ty,
                rfn: parsed_rfn,
            };
        } else {
            spec = StructFieldSpec {
                ty: self.field_type.clone(),
                rfn: parsed_rfn,
            };
        }
        Ok(spec)
    }
}
