// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use attribute_parse::{parse, MToken};
use log::{info, warn};
use parse::{Parse, Peek};
use radium::{coq, push_str_list, specs};
use rustc_ast::ast::AttrItem;
use rustc_middle::ty;

use crate::spec_parsers::parse_utils::{ParseMeta, *};

pub struct ClosureMetaInfo<'a, 'tcx, 'def> {
    /// the closure kind
    pub kind: ty::ClosureKind,
    /// capture information
    pub captures: &'tcx [&'tcx ty::CapturedPlace<'tcx>],
    /// the translated types of the captures, including the surrounding reference if captured by-ref.
    /// Needs to be in same order as `captures`
    pub capture_tys: &'a [specs::Type<'def>],
    /// the lifetime of the closure, if kind is `Fn` or `FnMut`
    pub closure_lifetime: Option<specs::Lft>,
}

pub trait FunctionSpecParser<'def> {
    /// Parse a set of attributes into a function spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_function_spec<'a>(
        &'a mut self,
        attrs: &'a [&'a AttrItem],
        spec: &'a mut radium::FunctionBuilder<'def>,
    ) -> Result<(), String>;

    /// Parse a set of attributes into a closure spec.
    /// The implementation can assume the `attrs` to be prefixed by the tool prefix (e.g. `rr`) and
    /// that it does not need to deal with any other attributes.
    fn parse_closure_spec<'tcx, 'a, 'c, F>(
        &'a mut self,
        attrs: &'a [&'a AttrItem],
        spec: &'a mut radium::FunctionBuilder<'def>,
        meta: ClosureMetaInfo<'c, 'tcx, 'def>,
        make_tuple: F,
    ) -> Result<(), String>
    where
        F: Fn(Vec<specs::Type<'def>>) -> specs::Type<'def>;
}

/// A sequence of refinements with optional types, e.g.
/// `"42" @ "int i32", "1337", "(a, b)"`
#[derive(Debug)]
struct RRArgs {
    args: Vec<LiteralTypeWithRef>,
}
impl<'a> parse::Parse<ParseMeta<'a>> for RRArgs {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        let args: parse::Punctuated<LiteralTypeWithRef, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(input, meta)?;
        Ok(Self {
            args: args.into_iter().collect(),
        })
    }
}

/// Representation of the spec for a single closure capture.
/// e.g. `"x" : "#42"` (for by shr-ref capture)
/// or `"y" : "(#42, γ)" -> "(#43, γ)"` (for by mut-ref capture)
struct ClosureCaptureSpec {
    variable: String,
    pre: LiteralTypeWithRef,
    post: Option<LiteralTypeWithRef>,
}

impl<'a> parse::Parse<ParseMeta<'a>> for ClosureCaptureSpec {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        let name_str: parse::LitStr = input.parse(meta)?;
        let name = name_str.value();
        input.parse::<_, MToken![:]>(meta)?;

        let pre_spec: LiteralTypeWithRef = input.parse(meta)?;

        if parse::RArrow::peek(input) {
            input.parse::<_, MToken![->]>(meta)?;
            let current_pos = input.pos().unwrap();

            let post_spec: LiteralTypeWithRef = input.parse(meta)?;
            if post_spec.ty.is_some() {
                Err(parse::ParseError::OtherErr(
                    current_pos,
                    format!("Did not expect type specification for capture postcondition"),
                ))
            } else {
                Ok(Self {
                    variable: name,
                    pre: pre_spec,
                    post: Some(post_spec),
                })
            }
        } else {
            Ok(Self {
                variable: name,
                pre: pre_spec,
                post: None,
            })
        }
    }
}

/// Representation of the `IProps` that can appear in a requires or ensures clause.
enum MetaIProp {
    /// #[rr::requires("..")] or #[rr::requires("Ha" : "..")]
    Pure(String, Option<String>),
    /// #[rr::requires(#iris "..")]
    Iris(specs::IProp),
    /// #[rr::requires(#type "l" : "rfn" @ "ty")]
    Type(specs::TyOwnSpec),
    /// #[rr::ensures(#observe "γ" : "2 * x")]
    Observe(String, String),
    /// #[rr::requires(#linktime "st_size {st_of T} < MaxInt isize")]
    Linktime(String),
}

impl<'a> parse::Parse<ParseMeta<'a>> for MetaIProp {
    fn parse(input: parse::ParseStream, meta: &ParseMeta) -> parse::ParseResult<Self> {
        if parse::Pound::peek(input) {
            input.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = input.parse(meta)?;
            match macro_cmd.value().as_str() {
                "type" => {
                    let loc_str: parse::LitStr = input.parse(meta)?;
                    let (loc_str, mut annot_meta) = process_coq_literal(&loc_str.value(), *meta);

                    input.parse::<_, MToken![:]>(meta)?;

                    let rfn_str: parse::LitStr = input.parse(meta)?;
                    let (rfn_str, annot_meta2) = process_coq_literal(&rfn_str.value(), *meta);

                    annot_meta.join(&annot_meta2);

                    input.parse::<_, MToken![@]>(meta)?;

                    let type_str: parse::LitStr = input.parse(meta)?;
                    let (type_str, annot_meta3) = process_coq_literal(&type_str.value(), *meta);
                    annot_meta.join(&annot_meta3);

                    let spec = specs::TyOwnSpec::new(loc_str, rfn_str, type_str, false, annot_meta);
                    Ok(Self::Type(spec))
                },
                "iris" => {
                    let prop: IProp = input.parse(meta)?;
                    Ok(Self::Iris(prop.into()))
                },
                "observe" => {
                    let gname: parse::LitStr = input.parse(meta)?;
                    input.parse::<_, MToken![:]>(meta)?;

                    let term: parse::LitStr = input.parse(meta)?;
                    let (term, _meta) = process_coq_literal(&term.value(), *meta);

                    Ok(Self::Observe(gname.value(), term))
                },
                "linktime" => {
                    let term: parse::LitStr = input.parse(meta)?;
                    let (term, _meta) = process_coq_literal(&term.value(), *meta);
                    Ok(Self::Linktime(term))
                },
                _ => Err(parse::ParseError::OtherErr(
                    input.pos().unwrap(),
                    format!("invalid macro command: {:?}", macro_cmd.value()),
                )),
            }
        } else {
            let name_or_prop_str: parse::LitStr = input.parse(meta)?;
            if parse::Colon::peek(input) {
                // this is a name
                let name_str = name_or_prop_str.value();

                input.parse::<_, MToken![:]>(meta)?;

                let pure_prop: parse::LitStr = input.parse(meta)?;
                let (pure_str, _annot_meta) = process_coq_literal(&pure_prop.value(), *meta);
                // TODO: should we use annot_meta?

                Ok(Self::Pure(pure_str, Some(name_str)))
            } else {
                // this is a
                let (lit, _) = process_coq_literal(&name_or_prop_str.value(), *meta);
                Ok(Self::Pure(lit, None))
            }
        }
    }
}

impl From<MetaIProp> for specs::IProp {
    fn from(meta: MetaIProp) -> Self {
        match meta {
            MetaIProp::Pure(p, name) => match name {
                None => Self::Pure(p),
                Some(n) => Self::PureWithName(p, n),
            },
            MetaIProp::Iris(p) => p,
            MetaIProp::Type(spec) => {
                let lit = spec.fmt_owned("π");
                Self::Atom(lit)
            },
            MetaIProp::Observe(name, term) => Self::Atom(format!("gvar_pobs {name} ({term})")),
            MetaIProp::Linktime(p) => Self::Linktime(p),
        }
    }
}

/// The main parser.
pub struct VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// argument types with substituted type parameters
    arg_types: &'a [specs::Type<'def>],
    /// return types with substituted type parameters
    ret_type: &'a specs::Type<'def>,
    make_literal: F,
}

impl<'a, 'def, F> VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// Type parameters must already have been substituted in the given types.
    pub const fn new(
        arg_types: &'a [specs::Type<'def>],
        ret_type: &'a specs::Type<'def>,
        make_literal: F,
    ) -> Self {
        VerboseFunctionSpecParser {
            arg_types,
            ret_type,
            make_literal,
        }
    }

    /// Given a type annotation (either `r` or `r @ ty0`) and a translated Rust type `ty`, get the
    /// full type with refinement and, optionally, a Coq refinement type hint that will be used
    /// for the refinement `r`.
    fn make_type_with_ref(
        &self,
        lit: &LiteralTypeWithRef,
        ty: &specs::Type<'def>,
    ) -> (specs::TypeWithRef<'def>, Option<coq::Type>) {
        if let Some(lit_ty) = &lit.ty {
            // literal type given, we use this literal type as the RR semantic type
            // just use the syntype from the Rust type
            let st = ty.get_syn_type();

            // TODO: get CoqType for refinement. maybe have it as an annotation? the Infer is currently a
            // placeholder.

            let lit_ty = specs::LiteralType {
                rust_name: None,
                type_term: lit_ty.to_string(),
                refinement_type: coq::Type::Infer,
                syn_type: st,
            };
            let lit_ref = (self.make_literal)(lit_ty);
            let lit_ty_use = specs::LiteralTypeUse::new_with_annot(lit_ref, vec![], lit.meta.clone());

            (specs::TypeWithRef::new(specs::Type::Literal(lit_ty_use), lit.rfn.to_string()), None)
        } else {
            // no literal type given, just a refinement
            // we use the translated Rust type with the given refinement
            let mut ty = ty.clone();
            let rt = ty.get_rfn_type(&[]);
            if lit.raw == specs::TypeIsRaw::Yes {
                ty.make_raw();
            }
            (specs::TypeWithRef::new(ty, lit.rfn.to_string()), Some(rt))
        }
    }
}

impl<'a, 'def, F> VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    /// Handles attributes common among functions/methods and closures.
    fn handle_common_attributes(
        &mut self,
        name: &str,
        buffer: &parse::ParseBuffer,
        builder: &mut radium::FunctionBuilder<'def>,
        lfts: &[(Option<String>, String)],
    ) -> Result<bool, String> {
        let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
        let meta: ParseMeta = (&meta, lfts);

        match name {
            "params" => {
                let params = RRParams::parse(buffer, &meta).map_err(str_err)?;
                for p in params.params {
                    builder.spec.add_param(p.name, p.ty)?;
                }
            },
            "param" => {
                let param = RRParam::parse(buffer, &meta).map_err(str_err)?;
                builder.spec.add_param(param.name, param.ty)?;
            },
            "args" => {
                let args = RRArgs::parse(buffer, &meta).map_err(str_err)?;
                if self.arg_types.len() != args.args.len() {
                    return Err(format!(
                        "wrong number of function arguments given: expected {} args",
                        self.arg_types.len()
                    ));
                }
                for (arg, ty) in args.args.into_iter().zip(self.arg_types) {
                    let (ty, hint) = self.make_type_with_ref(&arg, ty);
                    builder.spec.add_arg(ty);
                    if let Some(cty) = hint {
                        // potentially add a typing hint to the refinement
                        if let IdentOrTerm::Ident(i) = arg.rfn {
                            info!("Trying to add a typing hint for {}", i);
                            builder.spec.add_param_type_annot(&coq::Name::Named(i.clone()), cty)?;
                        }
                    }
                }
            },
            "requires" => {
                let iprop = MetaIProp::parse(buffer, &meta).map_err(str_err)?;
                builder.spec.add_precondition(iprop.into());
            },
            "ensures" => {
                let iprop = MetaIProp::parse(buffer, &meta).map_err(str_err)?;
                builder.spec.add_postcondition(iprop.into());
            },
            "observe" => {
                let m = || {
                    let gname: parse::LitStr = buffer.parse(&meta)?;
                    buffer.parse::<_, MToken![:]>(&meta)?;

                    let term: parse::LitStr = buffer.parse(&meta)?;
                    let (term, _) = process_coq_literal(&term.value(), meta);
                    Ok(MetaIProp::Observe(gname.value(), term))
                };
                let m = m().map_err(str_err)?;
                builder.spec.add_postcondition(m.into());
            },
            "returns" => {
                let tr = LiteralTypeWithRef::parse(buffer, &meta).map_err(str_err)?;
                // convert to type
                let (ty, _) = self.make_type_with_ref(&tr, self.ret_type);
                builder.spec.set_ret_type(ty)?;
            },
            "exists" => {
                let params = RRParams::parse(buffer, &meta).map_err(str_err)?;
                for param in params.params {
                    builder.spec.add_existential(param.name, param.ty)?;
                }
            },
            "tactics" => {
                let tacs = parse::LitStr::parse(buffer, &meta).map_err(str_err)?;
                let tacs = tacs.value();
                builder.add_manual_tactic(&tacs);
            },
            "context" => {
                let context_item = RRCoqContextItem::parse(buffer, &meta).map_err(str_err)?;
                if context_item.at_end {
                    builder.spec.add_late_coq_param(
                        coq::Name::Unnamed,
                        coq::Type::Literal(context_item.item),
                        true,
                    )?;
                } else {
                    builder.spec.add_coq_param(
                        coq::Name::Unnamed,
                        coq::Type::Literal(context_item.item),
                        true,
                    )?;
                }
            },
            _ => {
                return Ok(false);
            },
        }
        Ok(true)
    }

    /// Merges information on captured variables with specifications on captures.
    /// `capture_specs`: the parsed capture specification

    /// `make_tuple`: closure to make a new Radium tuple type
    /// `builder`: the function builder to push new specification components to
    fn merge_capture_information<'b, 'c, 'tcx, H>(
        &mut self,
        capture_specs: Vec<ClosureCaptureSpec>,
        meta: ClosureMetaInfo<'c, 'tcx, 'def>,
        make_tuple: H,
        builder: &mut radium::FunctionBuilder<'def>,
    ) -> Result<(), String>
    where
        H: Fn(Vec<specs::Type<'def>>) -> specs::Type<'def>,
    {
        enum CapturePostRfn {
            // mutable capture: (pattern, ghost_var)
            Mut(String, String),
            // immutable or once capture: pattern
            ImmutOrConsume(String),
        }

        // new ghost vars created for mut-captures
        let mut new_ghost_vars: Vec<String> = Vec::new();
        let mut pre_types: Vec<specs::TypeWithRef> = Vec::new();
        // post patterns and optional ghost variable, if this is a by-mut-ref capture
        let mut post_patterns: Vec<CapturePostRfn> = Vec::new();

        let mut capture_spec_map = HashMap::new();
        for x in capture_specs {
            capture_spec_map.insert(x.variable, (x.pre, x.post));
        }

        // assemble the pre types
        for (capture, ty) in meta.captures.iter().zip(meta.capture_tys.iter()) {
            if !capture.place.projections.is_empty() {
                info!("processing capture {:?}", capture);
                warn!("ignoring place projection in translation of capture: {:?}", capture);
                // TODO: could handle this by parsing capture strings in specs
                //unimplemented!("only support specifying closure captures without projections");
            }
            let base = capture.var_ident.name.as_str();
            if let Some((_, (pre, post))) = capture_spec_map.remove_entry(base) {
                // we kinda want to specify the thing independently of how it is captured
                match capture.info.capture_kind {
                    ty::UpvarCapture::ByValue => {
                        // full ownership
                        let (processed_ty, _) = self.make_type_with_ref(&pre, ty);
                        pre_types.push(processed_ty);

                        if let Some(post) = post {
                            // this should not contain any post
                            return Err(format!(
                                "Did not expect postcondition {:?} for by-value capture",
                                post
                            ));
                            //let (processed_post, _) = self.make_type_with_ref(&post, ty);
                            //post_patterns.push(processed_post.1);
                        }
                    },
                    ty::UpvarCapture::ByRef(ty::BorrowKind::ImmBorrow) => {
                        // shared borrow
                        // if there's a manually specified type, we need to wrap it in the reference
                        if let specs::Type::ShrRef(box auto_type, lft) = ty {
                            let (processed_ty, _) = self.make_type_with_ref(&pre, auto_type);
                            // now wrap it in a shared reference again
                            let altered_ty = specs::Type::ShrRef(Box::new(processed_ty.0), lft.clone());
                            let altered_rfn = format!("#({})", processed_ty.1);
                            pre_types.push(specs::TypeWithRef::new(altered_ty, altered_rfn.clone()));

                            // push the same pattern for the post, no ghost variable
                            post_patterns.push(CapturePostRfn::ImmutOrConsume(altered_rfn));
                        }
                    },
                    ty::UpvarCapture::ByRef(_) => {
                        // mutable borrow
                        // we handle ty::BorrowKind::MutBorrow and ty::BorrowKind::UniqImmBorrow
                        // the same way, as they are not really different for RefinedRust's type
                        // system
                        if let specs::Type::MutRef(box auto_type, lft) = ty {
                            let (processed_ty, _) = self.make_type_with_ref(&pre, auto_type);
                            // now wrap it in a mutable reference again
                            // we create a ghost variable
                            let ghost_var = format!("_γ{base}");
                            new_ghost_vars.push(ghost_var.clone());
                            let altered_ty = specs::Type::MutRef(Box::new(processed_ty.0), lft.clone());
                            let altered_rfn = format!("(#({}), {ghost_var})", processed_ty.1);
                            pre_types.push(specs::TypeWithRef::new(altered_ty, altered_rfn));

                            if let Some(post) = post {
                                post_patterns.push(CapturePostRfn::Mut(post.rfn.to_string(), ghost_var));
                            } else {
                                // push the same pattern for the post
                                post_patterns.push(CapturePostRfn::Mut(processed_ty.1, ghost_var));
                            }
                        }
                    },
                }
            } else {
                return Err(format!("ambiguous specification of capture {:?}", capture));
            }
        }

        // push everything to the builder
        for x in new_ghost_vars {
            builder.spec.add_param(coq::Name::Named(x), coq::Type::Gname).unwrap();
        }

        // assemble a string for the closure arg
        let mut pre_rfn = String::new();
        let mut pre_tys = Vec::new();

        if pre_types.is_empty() {
            pre_rfn.push_str("()");
        } else {
            pre_rfn.push_str("-[");
            push_str_list!(pre_rfn, pre_types.clone(), "; ", |x| format!("#({})", x.1));
            pre_rfn.push(']');

            pre_tys = pre_types.iter().map(|x| x.0.clone()).collect();
        }
        let tuple = make_tuple(pre_tys);

        match meta.kind {
            ty::ClosureKind::FnOnce => {
                builder.spec.add_arg(specs::TypeWithRef::new(tuple, pre_rfn));

                // generate observations on all the mut-ref captures
                for p in post_patterns {
                    match p {
                        CapturePostRfn::ImmutOrConsume(_) => {
                            // nothing mutated
                        },
                        CapturePostRfn::Mut(pat, gvar) => {
                            // add an observation on `gvar`
                            builder.spec.add_postcondition(MetaIProp::Observe(gvar, pat).into());
                        },
                    }
                }
            },
            ty::ClosureKind::Fn => {
                // wrap the argument in a shared reference
                // all the captures are by shared ref

                let lft = meta.closure_lifetime.unwrap();
                let ref_ty = specs::Type::ShrRef(Box::new(tuple), lft);
                let ref_rfn = format!("#{}", pre_rfn);

                builder.spec.add_arg(specs::TypeWithRef::new(ref_ty, ref_rfn));
            },
            ty::ClosureKind::FnMut => {
                // wrap the argument in a mutable reference
                let post_name = "__γclos";
                builder.spec.add_param(coq::Name::Named(post_name.to_owned()), coq::Type::Gname).unwrap();

                let lft = meta.closure_lifetime.unwrap();
                let ref_ty = specs::Type::MutRef(Box::new(tuple), lft);
                let ref_rfn = format!("(#({}), {})", pre_rfn, post_name);

                builder.spec.add_arg(specs::TypeWithRef::new(ref_ty, ref_rfn));

                // assemble a postcondition on the closure
                // we observe on the outer mutable reference for the capture, not on the individual
                // references
                let mut post_term = String::new();

                post_term.push_str("-[");
                push_str_list!(post_term, post_patterns, "; ", |p| match p {
                    CapturePostRfn::ImmutOrConsume(pat) => format!("#({pat})"),
                    CapturePostRfn::Mut(pat, gvar) => format!("#(#({pat}), {gvar})"),
                });
                post_term.push(']');

                builder.spec.add_postcondition(MetaIProp::Observe(post_name.to_owned(), post_term).into());
            },
        }
        Ok(())
    }
}

impl<'a, 'def, F> FunctionSpecParser<'def> for VerboseFunctionSpecParser<'a, 'def, F>
where
    F: Fn(specs::LiteralType) -> specs::LiteralTypeRef<'def>,
{
    fn parse_closure_spec<'tcx, 'b, 'c, H>(
        &'b mut self,
        attrs: &'b [&'b AttrItem],
        spec: &'b mut radium::FunctionBuilder<'def>,
        closure_meta: ClosureMetaInfo<'c, 'tcx, 'def>,
        make_tuple: H,
    ) -> Result<(), String>
    where
        H: Fn(Vec<specs::Type<'def>>) -> specs::Type<'def>,
    {
        if !attrs.is_empty() {
            spec.spec.have_spec();
        }

        // clone to be able to mutably borrow later
        let builder = spec;
        let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
        let lfts: Vec<(Option<String>, specs::Lft)> = builder.get_lfts();
        let meta: ParseMeta = (&meta, &lfts);
        info!("ty params: {:?}", meta);

        // TODO: handle args in the common function differently
        let mut capture_specs = Vec::new();

        // parse captures -- we need to handle it before the other annotations because we will have
        // to add the first arg for the capture
        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
            let meta: ParseMeta = (&meta, &lfts);

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&args.inner_tokens());

                if seg.ident.name.as_str() == "capture" {
                    let spec: ClosureCaptureSpec = buffer.parse(&meta).map_err(str_err)?;
                    capture_specs.push(spec);
                }
            }
        }

        self.merge_capture_information(capture_specs, closure_meta, make_tuple, &mut *builder)?;

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());
                let name = seg.ident.name.as_str();

                match self.handle_common_attributes(name, &buffer, builder, &lfts) {
                    Ok(b) => {
                        if !b && name != "capture" {
                            info!("ignoring function attribute: {:?}", args);
                        }
                    },

                    Err(e) => return Err(e),
                }
            }
        }

        Ok(())
    }

    fn parse_function_spec(
        &mut self,
        attrs: &[&AttrItem],
        spec: &mut radium::FunctionBuilder<'def>,
    ) -> Result<(), String> {
        if !attrs.is_empty() {
            spec.spec.have_spec();
        }

        // clone to be able to mutably borrow later
        let builder = spec;
        let lfts: Vec<(Option<String>, specs::Lft)> = builder.get_lfts();

        let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
        let meta: ParseMeta = (&meta, &lfts);
        info!("ty params: {:?}", meta);

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            if let Some(seg) = path_segs.get(1) {
                let buffer = parse::ParseBuffer::new(&it.args.inner_tokens());

                match self.handle_common_attributes(seg.ident.name.as_str(), &buffer, builder, &lfts) {
                    Ok(b) => {
                        if !b {
                            let meta: &[specs::LiteralTyParam] = builder.get_ty_params();
                            let _meta: ParseMeta = (&meta, &lfts);

                            info!("ignoring function attribute: {:?}", args);
                        }
                    },
                    Err(e) => {
                        return Err(e);
                    },
                }
            }
        }
        Ok(())
    }
}
