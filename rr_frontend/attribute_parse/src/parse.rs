// Based on the syn crate: https://github.com/dtolnay/syn
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.
#![allow(dead_code)]
/// This provides parsing facilities for rustc attribute token streams.
// TODO: refactor/ make into own crate?
use std::cell::Cell;
use std::fmt::Display;
use std::str::{self, FromStr};

use rustc_ast::token::{BinOpToken, Lit, LitKind, TokenKind};
use rustc_ast::tokenstream::TokenTree;
use rustc_span::{Span, Symbol};
use unicode_xid::UnicodeXID;

pub trait IntoSpans<S> {
    fn into_spans(self) -> S;
}

impl IntoSpans<[Span; 1]> for Span {
    fn into_spans(self) -> [Span; 1] {
        [self]
    }
}

impl IntoSpans<[Span; 2]> for Span {
    fn into_spans(self) -> [Span; 2] {
        [self, self]
    }
}

impl IntoSpans<[Span; 3]> for Span {
    fn into_spans(self) -> [Span; 3] {
        [self, self, self]
    }
}

impl IntoSpans<[Span; 1]> for [Span; 1] {
    fn into_spans(self) -> [Span; 1] {
        self
    }
}

impl IntoSpans<[Span; 2]> for [Span; 2] {
    fn into_spans(self) -> [Span; 2] {
        self
    }
}

impl IntoSpans<[Span; 3]> for [Span; 3] {
    fn into_spans(self) -> [Span; 3] {
        self
    }
}

pub trait FromSpans: Sized {
    fn from_spans(spans: &[Span]) -> Self;
}

impl FromSpans for [Span; 1] {
    fn from_spans(spans: &[Span]) -> Self {
        [spans[0]]
    }
}

impl FromSpans for [Span; 2] {
    fn from_spans(spans: &[Span]) -> Self {
        [spans[0], spans[1]]
    }
}

impl FromSpans for [Span; 3] {
    fn from_spans(spans: &[Span]) -> Self {
        [spans[0], spans[1], spans[2]]
    }
}

#[derive(Debug)]
pub enum ParseError {
    EOF,
    WrongTokenKind(TokenKind, TokenKind, Span),
    UnexpectedDelim(rustc_ast::tokenstream::DelimSpan),
    ExpectedIdent(TokenKind, Span),
    ExpectedLiteral(TokenKind, Span),
    UnexpectedLitKind(LitKind, LitKind),
    OtherErr(Span, String),
}

pub type ParseResult<T> = Result<T, ParseError>;

// TODO: maybe change to just have a shared reference to the vector? (or a RefCell)?
// we anyways only ever read from it, and making ParseBuffer Copy might be nice for
// having multiple different cursors at once into the same vector.
#[derive(Debug, Clone)]
pub struct ParseBuffer {
    trees: Vec<rustc_ast::tokenstream::TokenTree>,
    index: Cell<usize>,
}

impl ParseBuffer {
    pub fn new(stream: &rustc_ast::tokenstream::TokenStream) -> Self {
        // TODO; maybe avoid the cloning
        let trees: Vec<TokenTree> = stream.trees().map(|c| c.clone()).collect();
        ParseBuffer {
            trees,
            index: Cell::new(0),
        }
    }

    pub fn parse<U, T: Parse<U>>(&self, meta: &U) -> ParseResult<T>
    where
        U: ?Sized,
    {
        T::parse(self, meta)
    }

    pub fn call<T>(&self, function: fn(ParseStream) -> ParseResult<T>) -> ParseResult<T> {
        function(self)
    }

    pub fn pos(&self) -> Option<Span> {
        self.trees.get(self.index.get()).map(|r| r.span())
    }

    pub fn peek(&self, n: usize) -> ParseResult<&TokenTree> {
        self.trees.get(self.index.get() + n).ok_or(ParseError::EOF)
    }

    pub fn advance(&self, n: usize) {
        self.index.set(self.index.get() + n)
    }

    pub fn advance_get(&self) -> ParseResult<&TokenTree> {
        let i = self.index.get();
        let r = self.trees.get(i).ok_or(ParseError::EOF)?;
        self.index.set(i + 1);
        Ok(r)
    }

    pub fn is_empty(&self) -> bool {
        self.index.get() >= self.trees.len()
    }

    /// Check if the next symbol is a token matching the given kind.
    pub fn peek_token(&self, token: TokenKind) -> bool {
        let tok = self.peek(0);
        match tok {
            Ok(TokenTree::Token(tok, _)) => tok.kind == token,
            _ => false,
        }
    }

    /// Consume a token of the given kind.
    pub fn expect_token(&self, token: TokenKind) -> ParseResult<Span> {
        let tok = self.peek(0)?;
        match tok {
            TokenTree::Token(tok, _) => {
                if tok.kind == token {
                    self.advance(1);
                    Ok(tok.span)
                } else {
                    Err(ParseError::WrongTokenKind(token, tok.kind.clone(), tok.span))
                }
            },
            TokenTree::Delimited(span, _, _) => Err(ParseError::UnexpectedDelim(*span)),
        }
    }

    /// Consume an identifier.
    pub fn expect_ident(&self) -> ParseResult<(Symbol, Span)> {
        let tok = self.peek(0)?;
        match tok {
            TokenTree::Token(tok, _) => match tok.kind {
                TokenKind::Ident(sym, _) => {
                    self.advance(1);
                    Ok((sym, tok.span))
                },
                _ => Err(ParseError::ExpectedIdent(tok.kind.clone(), tok.span)),
            },
            TokenTree::Delimited(span, _, _) => Err(ParseError::UnexpectedDelim(*span)),
        }
    }

    /// Consume a literal.
    pub fn expect_literal(&self) -> ParseResult<(Lit, Span)> {
        let tok = self.peek(0)?;
        match tok {
            TokenTree::Token(tok, _) => match tok.kind {
                TokenKind::Literal(lit) => {
                    self.advance(1);
                    Ok((lit, tok.span))
                },
                _ => Err(ParseError::ExpectedLiteral(tok.kind.clone(), tok.span)),
            },
            TokenTree::Delimited(span, _, _) => Err(ParseError::UnexpectedDelim(*span)),
        }
    }
}

pub type ParseStream<'a> = &'a ParseBuffer;

pub trait Parse<U>: Sized
where
    U: ?Sized,
{
    fn parse(stream: ParseStream, meta: &U) -> ParseResult<Self>;
}

impl<U, T: Parse<U>> Parse<U> for Box<T>
where
    U: ?Sized,
{
    fn parse(input: ParseStream, meta: &U) -> ParseResult<Self> {
        input.parse(meta).map(Box::new)
    }
}

pub trait Peek {
    fn peek(stream: ParseStream) -> bool;
}

pub trait PToken: Peek {}

macro_rules! define_punctuation_structs {
    ($($token:tt pub struct $name:ident/$len:tt #[$doc:meta])*) => {
        $(
            #[repr(C)]
            #[$doc]
            ///
            /// Don't try to remember the name of this type &mdash; use the
            /// [`Token!`] macro instead.
            ///
            /// [`Token!`]: crate::token
            pub struct $name {
                pub span: Span,
            }

            //#[doc(hidden)]
            //#[allow(non_snake_case)]
            //pub fn $name<S: IntoSpans<[Span; $len]>>(spans: S) -> $name {
                //$name {
                    //span: spans.into_spans(),
                //}
            //}

            //impl std::default::Default for $name {
                //fn default() -> Self {
                    //$name {
                        //spans: [Span::call_site(); $len],
                    //}
                //}
            //}

            impl Copy for $name {}

            impl Clone for $name {
                fn clone(&self) -> Self {
                    *self
                }
            }

            //impl Debug for $name {
                //fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    //f.write_str(stringify!($name))
                //}
            //}

            //impl cmp::Eq for $name {}

            //impl PartialEq for $name {
                //fn eq(&self, _other: &$name) -> bool {
                    //true
                //}
            //}

            //impl Hash for $name {
                //fn hash<H: Hasher>(&self, _state: &mut H) {}
            //}
        )*
    };
}

macro_rules! define_punctuation {
    ($($token:tt pub struct $name:ident/$len:tt $tk:expr , #[$doc:meta])*) => {
        $(
            define_punctuation_structs! {
                $token pub struct $name/$len #[$doc]
            }

            //#[cfg(feature = "printing")]
            //#[cfg_attr(doc_cfg, doc(cfg(feature = "printing")))]
            //impl ToTokens for $name {
                //fn to_tokens(&self, tokens: &mut TokenStream) {
                    //printing::punct($token, &self.spans, tokens);
                //}
            //}

            impl<U> Parse<U> for $name where U: ?Sized {
                fn parse(input: ParseStream, _: &U) -> ParseResult<Self> {
                    Ok($name {
                        span: input.expect_token($tk)?,
                    })
                }
            }

            impl Peek for $name {
                fn peek(input: ParseStream) -> bool {
                    input.peek_token($tk)
                }

                //fn display() -> &'static str {
                    //concat!("`", $token, "`")
                //}
            }

            impl PToken for $name {

            }
        )*
    };
}

define_punctuation! {
    "+"           pub struct Add/1              TokenKind::BinOp(BinOpToken::Plus),         /// `+`
    "+="          pub struct AddEq/2            TokenKind::BinOpEq(BinOpToken::Plus),       /// `+=`
    "&"           pub struct And/1              TokenKind::BinOp(BinOpToken::And),          /// `&`
    "&&"          pub struct AndAnd/2           TokenKind::AndAnd,                          /// `&&`
    "&="          pub struct AndEq/2            TokenKind::BinOpEq(BinOpToken::And),        /// `&=`
    "@"           pub struct At/1               TokenKind::At,                              /// `@`
    "!"           pub struct Bang/1             TokenKind::Not,                             /// `!`
    "^"           pub struct Caret/1            TokenKind::BinOp(BinOpToken::Caret),        /// `^`
    "^="          pub struct CaretEq/2          TokenKind::BinOpEq(BinOpToken::Caret),      /// `^=`
    ":"           pub struct Colon/1            TokenKind::Colon,                           /// `:`
    "::"          pub struct Colon2/2           TokenKind::ModSep,                          /// `::`
    ","           pub struct Comma/1            TokenKind::Comma,                           /// `,`
    "/"           pub struct Div/1              TokenKind::BinOp(BinOpToken::Slash),        /// `/`
    "/="          pub struct DivEq/2            TokenKind::BinOpEq(BinOpToken::Slash),      /// `/=`
    "$"           pub struct Dollar/1           TokenKind::Dollar,                          /// `$`
    "."           pub struct Dot/1              TokenKind::Dot,                             /// `.`
    ".."          pub struct Dot2/2             TokenKind::DotDot,                          /// `..`
    "..."         pub struct Dot3/3             TokenKind::DotDotDot,                       /// `...`
    "..="         pub struct DotDotEq/3         TokenKind::DotDotEq,                        /// `..=`
    "="           pub struct Eq/1               TokenKind::Eq,                              /// `=`
    "=="          pub struct EqEq/2             TokenKind::EqEq,                            /// `==`
    ">="          pub struct Ge/2               TokenKind::Ge,                              /// `>=`
    ">"           pub struct Gt/1               TokenKind::Gt,                              /// `>`
    "<="          pub struct Le/2               TokenKind::Le,                              /// `<=`
    "<"           pub struct Lt/1               TokenKind::Lt,                              /// `<`
    "*="          pub struct MulEq/2            TokenKind::BinOpEq(BinOpToken::Star),       /// `*=`
    "!="          pub struct Ne/2               TokenKind::Ne,                              /// `!=`
    "|"           pub struct Or/1               TokenKind::BinOp(BinOpToken::Or),           /// `|`
    "|="          pub struct OrEq/2             TokenKind::BinOpEq(BinOpToken::Or),         /// `|=`
    "||"          pub struct OrOr/2             TokenKind::OrOr,                            /// `||`
    "#"           pub struct Pound/1            TokenKind::Pound,                           /// `#`
    "?"           pub struct Question/1         TokenKind::Question,                        /// `?`
    "->"          pub struct RArrow/2           TokenKind::RArrow,                          /// `->`
    "<-"          pub struct LArrow/2           TokenKind::LArrow,                          /// `<-`
    "%"           pub struct Rem/1              TokenKind::BinOp(BinOpToken::Percent),      /// `%`
    "%="          pub struct RemEq/2            TokenKind::BinOpEq(BinOpToken::Percent),    /// `%=`
    "=>"          pub struct FatArrow/2         TokenKind::FatArrow,                        /// `=>`
    ";"           pub struct Semi/1             TokenKind::Semi,                            /// `;`
    "<<"          pub struct Shl/2              TokenKind::BinOp(BinOpToken::Shl),          /// `<<`
    "<<="         pub struct ShlEq/3            TokenKind::BinOpEq(BinOpToken::Shl),        /// `<<=`
    ">>"          pub struct Shr/2              TokenKind::BinOp(BinOpToken::Shr),          /// `>>`
    ">>="         pub struct ShrEq/3            TokenKind::BinOpEq(BinOpToken::Shr),        /// `>>=`
    "*"           pub struct Star/1             TokenKind::BinOp(BinOpToken::Star),         /// `*`
    "-"           pub struct Sub/1              TokenKind::BinOp(BinOpToken::Minus),        /// `-`
    "-="          pub struct SubEq/2            TokenKind::BinOpEq(BinOpToken::Minus),      /// `-=`
    "~"           pub struct Tilde/1            TokenKind::Tilde,                           /// `~`
}

#[macro_export]
macro_rules! MToken {
    [+]           => { $crate::parse::Add };
    [+=]          => { $crate::parse::AddEq };
    [&]           => { $crate::parse::And };
    [&&]          => { $crate::parse::AndAnd };
    [&=]          => { $crate::parse::AndEq };
    [@]           => { $crate::parse::At };
    [!]           => { $crate::parse::Bang };
    [^]           => { $crate::parse::Caret };
    [^=]          => { $crate::parse::CaretEq };
    [:]           => { $crate::parse::Colon };
    [::]          => { $crate::parse::Colon2 };
    [,]           => { $crate::parse::Comma };
    [/]           => { $crate::parse::Div };
    [/=]          => { $crate::parse::DivEq };
    [$]           => { $crate::parse::Dollar };
    [.]           => { $crate::parse::Dot };
    [..]          => { $crate::parse::Dot2 };
    [...]         => { $crate::parse::Dot3 };
    [..=]         => { $crate::parse::DotDotEq };
    [=]           => { $crate::parse::Eq };
    [==]          => { $crate::parse::EqEq };
    [>=]          => { $crate::parse::Ge };
    [>]           => { $crate::parse::Gt };
    [<=]          => { $crate::parse::Le };
    [<]           => { $crate::parse::Lt };
    [*=]          => { $crate::parse::MulEq };
    [!=]          => { $crate::parse::Ne };
    [|]           => { $crate::parse::Or };
    [|=]          => { $crate::parse::OrEq };
    [||]          => { $crate::parse::OrOr };
    [#]           => { $crate::parse::Pound };
    [?]           => { $crate::parse::Question };
    [->]          => { $crate::parse::RArrow };
    [<-]          => { $crate::parse::LArrow };
    [%]           => { $crate::parse::Rem };
    [%=]          => { $crate::parse::RemEq };
    [=>]          => { $crate::parse::FatArrow };
    [;]           => { $crate::parse::Semi };
    [<<]          => { $crate::parse::Shl };
    [<<=]         => { $crate::parse::ShlEq };
    [>>]          => { $crate::parse::Shr };
    [>>=]         => { $crate::parse::ShrEq };
    [*]           => { $crate::parse::Star };
    [-]           => { $crate::parse::Sub };
    [-=]          => { $crate::parse::SubEq };
    [~]           => { $crate::parse::Tilde };
    [_]           => { $crate::parse::Underscore };
}

pub struct LitStr {
    span: Span,
    sym: Symbol,
}

impl LitStr {
    pub fn value(&self) -> String {
        self.sym.to_string()
    }
}

impl<U> Parse<U> for LitStr
where
    U: ?Sized,
{
    fn parse(input: ParseStream, _: &U) -> ParseResult<Self> {
        let lit = input.expect_literal()?;
        match lit.0.kind {
            LitKind::Str => Ok(LitStr {
                span: lit.1,
                sym: lit.0.symbol,
            }),
            _ => Err(ParseError::UnexpectedLitKind(LitKind::Str, lit.0.kind)),
        }
    }
}

pub struct Ident {
    span: Span,
    sym: Symbol,
}

impl<U> Parse<U> for Ident
where
    U: ?Sized,
{
    fn parse(input: ParseStream, _: &U) -> ParseResult<Self> {
        let (sym, span) = input.expect_ident()?;
        Ok(Ident { span, sym })
    }
}

impl Ident {
    pub fn value(&self) -> String {
        self.sym.to_string()
    }
}

pub struct LitInt {
    span: Span,
    sym: Symbol,
    digits: Box<str>,
    suffix: Box<str>,
}

impl LitInt {
    //pub fn value(&self) -> String {
    //self.sym.to_string()
    //}
    pub fn base10_parse<N>(&self) -> ParseResult<N>
    where
        N: FromStr,
        N::Err: Display,
    {
        self.digits.parse().map_err(|err| ParseError::OtherErr(self.span, format!("{}", err)))
    }
}

impl<U> Parse<U> for LitInt
where
    U: ?Sized,
{
    fn parse(input: ParseStream, _: &U) -> ParseResult<Self> {
        let lit = input.expect_literal()?;
        match lit.0.kind {
            LitKind::Integer => {
                let sym = lit.0.symbol;
                if let Some((digits, suffix)) = value::parse_lit_int(&sym.to_string()) {
                    Ok(LitInt {
                        span: lit.1,
                        sym: lit.0.symbol,
                        digits: digits,
                        suffix: suffix,
                    })
                } else {
                    panic!("Not an integer literal: {}", sym.to_string());
                }
            },
            _ => Err(ParseError::UnexpectedLitKind(LitKind::Integer, lit.0.kind)),
        }
    }
}

mod value {
    use crate::parse::BigInt;

    // Returns base 10 digits and suffix.
    pub fn parse_lit_int(mut s: &str) -> Option<(Box<str>, Box<str>)> {
        let negative = byte(s, 0) == b'-';
        if negative {
            s = &s[1..];
        }

        let base = match (byte(s, 0), byte(s, 1)) {
            (b'0', b'x') => {
                s = &s[2..];
                16
            },
            (b'0', b'o') => {
                s = &s[2..];
                8
            },
            (b'0', b'b') => {
                s = &s[2..];
                2
            },
            (b'0'..=b'9', _) => 10,
            _ => return None,
        };

        let mut value = BigInt::new();
        'outer: loop {
            let b = byte(s, 0);
            let digit = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' if base > 10 => b - b'a' + 10,
                b'A'..=b'F' if base > 10 => b - b'A' + 10,
                b'_' => {
                    s = &s[1..];
                    continue;
                },
                // If looking at a floating point literal, we don't want to
                // consider it an integer.
                b'.' if base == 10 => return None,
                b'e' | b'E' if base == 10 => {
                    let mut has_exp = false;
                    for (i, b) in s[1..].bytes().enumerate() {
                        match b {
                            b'_' => {},
                            b'-' | b'+' => return None,
                            b'0'..=b'9' => has_exp = true,
                            _ => {
                                let suffix = &s[1 + i..];
                                if has_exp && crate::parse::xid_ok(suffix) {
                                    return None;
                                } else {
                                    break 'outer;
                                }
                            },
                        }
                    }
                    if has_exp {
                        return None;
                    } else {
                        break;
                    }
                },
                _ => break,
            };

            if digit >= base {
                return None;
            }

            value *= base;
            value += digit;
            s = &s[1..];
        }

        let suffix = s;
        if suffix.is_empty() || crate::parse::xid_ok(suffix) {
            let mut repr = value.to_string();
            if negative {
                repr.insert(0, '-');
            }
            Some((repr.into_boxed_str(), suffix.to_owned().into_boxed_str()))
        } else {
            None
        }
    }

    /// Get the byte at offset idx, or a default of `b'\0'` if we're looking
    /// past the end of the input buffer.
    pub fn byte<S: AsRef<[u8]> + ?Sized>(s: &S, idx: usize) -> u8 {
        let s = s.as_ref();
        if idx < s.len() { s[idx] } else { 0 }
    }
}

pub fn xid_ok(symbol: &str) -> bool {
    let mut chars = symbol.chars();
    let first = chars.next().unwrap();
    if !(UnicodeXID::is_xid_start(first) || first == '_') {
        return false;
    }
    for ch in chars {
        if !UnicodeXID::is_xid_continue(ch) {
            return false;
        }
    }
    true
}

use std::ops::{AddAssign, MulAssign};

// For implementing base10_digits() accessor on LitInt.
pub struct BigInt {
    digits: Vec<u8>,
}

impl BigInt {
    pub fn new() -> Self {
        BigInt { digits: Vec::new() }
    }

    pub fn to_string(&self) -> String {
        let mut repr = String::with_capacity(self.digits.len());

        let mut has_nonzero = false;
        for digit in self.digits.iter().rev() {
            has_nonzero |= *digit != 0;
            if has_nonzero {
                repr.push((*digit + b'0') as char);
            }
        }

        if repr.is_empty() {
            repr.push('0');
        }

        repr
    }

    fn reserve_two_digits(&mut self) {
        let len = self.digits.len();
        let desired = len + !self.digits.ends_with(&[0, 0]) as usize + !self.digits.ends_with(&[0]) as usize;
        self.digits.resize(desired, 0);
    }
}

impl AddAssign<u8> for BigInt {
    // Assumes increment <16.
    fn add_assign(&mut self, mut increment: u8) {
        self.reserve_two_digits();

        let mut i = 0;
        while increment > 0 {
            let sum = self.digits[i] + increment;
            self.digits[i] = sum % 10;
            increment = sum / 10;
            i += 1;
        }
    }
}

impl MulAssign<u8> for BigInt {
    // Assumes base <=16.
    fn mul_assign(&mut self, base: u8) {
        self.reserve_two_digits();

        let mut carry = 0;
        for digit in &mut self.digits {
            let prod = *digit * base + carry;
            *digit = prod % 10;
            carry = prod / 10;
        }
    }
}

pub struct Punctuated<T, P> {
    inner: Vec<(T, P)>,
    last: Option<Box<T>>,
}

impl<T, P> Punctuated<T, P> {
    /// Creates an empty punctuated sequence.
    pub fn new() -> Self {
        Punctuated {
            inner: Vec::new(),
            last: None,
        }
    }

    /// Determines whether this punctuated sequence is empty, meaning it
    /// contains no syntax tree nodes or punctuation.
    pub fn is_empty(&self) -> bool {
        self.inner.len() == 0 && self.last.is_none()
    }

    /// Returns the number of syntax tree nodes in this punctuated sequence.
    ///
    /// This is the number of nodes of type `T`, not counting the punctuation of
    /// type `P`.
    pub fn len(&self) -> usize {
        self.inner.len() + if self.last.is_some() { 1 } else { 0 }
    }

    /// Borrows the first element in this sequence.
    pub fn first(&self) -> Option<&T> {
        self.iter().next()
    }

    /// Mutably borrows the first element in this sequence.
    //pub fn first_mut(&mut self) -> Option<&mut T> {
    //self.iter_mut().next()
    //}

    /// Borrows the last element in this sequence.
    pub fn last(&self) -> Option<&T> {
        self.iter().next_back()
    }

    /// Mutably borrows the last element in this sequence.
    //pub fn last_mut(&mut self) -> Option<&mut T> {
    //self.iter_mut().next_back()
    //}

    /// Returns an iterator over borrowed syntax tree nodes of type `&T`.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            inner: Box::new(PrivateIter {
                inner: self.inner.iter(),
                last: self.last.as_ref().map(Box::as_ref).into_iter(),
            }),
        }
    }

    /// Returns an iterator over mutably borrowed syntax tree nodes of type
    /// `&mut T`.
    //pub fn iter_mut(&mut self) -> IterMut<T> {
    //IterMut {
    //inner: Box::new(PrivateIterMut {
    //inner: self.inner.iter_mut(),
    //last: self.last.as_mut().map(Box::as_mut).into_iter(),
    //}),
    //}

    /// Returns an iterator over the contents of this sequence as borrowed
    /// punctuated pairs.
    //pub fn pairs(&self) -> Pairs<T, P> {
    //Pairs {
    //inner: self.inner.iter(),
    //last: self.last.as_ref().map(Box::as_ref).into_iter(),
    //}

    /// Returns an iterator over the contents of this sequence as mutably
    /// borrowed punctuated pairs.
    //pub fn pairs_mut(&mut self) -> PairsMut<T, P> {
    //PairsMut {
    //inner: self.inner.iter_mut(),
    //last: self.last.as_mut().map(Box::as_mut).into_iter(),
    //}

    /// Returns an iterator over the contents of this sequence as owned
    /// punctuated pairs.
    //pub fn into_pairs(self) -> IntoPairs<T, P> {
    //IntoPairs {
    //inner: self.inner.into_iter(),
    //last: self.last.map(|t| *t).into_iter(),
    //}

    /// Appends a syntax tree node onto the end of this punctuated sequence. The
    /// sequence must previously have a trailing punctuation.
    ///
    /// Use [`push`] instead if the punctuated sequence may or may not already
    /// have trailing punctuation.
    ///
    /// [`push`]: Punctuated::push
    ///
    /// # Panics
    ///
    /// Panics if the sequence does not already have a trailing punctuation when
    /// this method is called.
    pub fn push_value(&mut self, value: T) {
        assert!(
            self.empty_or_trailing(),
            "Punctuated::push_value: cannot push value if Punctuated is missing trailing punctuation",
        );

        self.last = Some(Box::new(value));
    }

    /// Appends a trailing punctuation onto the end of this punctuated sequence.
    /// The sequence must be non-empty and must not already have trailing
    /// punctuation.
    ///
    /// # Panics
    ///
    /// Panics if the sequence is empty or already has a trailing punctuation.
    pub fn push_punct(&mut self, punctuation: P) {
        assert!(
            self.last.is_some(),
            "Punctuated::push_punct: cannot push punctuation if Punctuated is empty or already has trailing punctuation",
        );

        let last = self.last.take().unwrap();
        self.inner.push((*last, punctuation));
    }

    /// Removes the last punctuated pair from this sequence, or `None` if the
    /// sequence is empty.
    //pub fn pop(&mut self) -> Option<Pair<T, P>> {
    //if self.last.is_some() {
    //self.last.take().map(|t| Pair::End(*t))
    //} else {
    //self.inner.pop().map(|(t, p)| Pair::Punctuated(t, p))
    //}

    /// Determines whether this punctuated sequence ends with a trailing
    /// punctuation.
    pub fn trailing_punct(&self) -> bool {
        self.last.is_none() && !self.is_empty()
    }

    /// Returns true if either this `Punctuated` is empty, or it has a trailing
    /// punctuation.
    ///
    /// Equivalent to `punctuated.is_empty() || punctuated.trailing_punct()`.
    pub fn empty_or_trailing(&self) -> bool {
        self.last.is_none()
    }

    /// Appends a syntax tree node onto the end of this punctuated sequence.
    ///
    /// If there is not a trailing punctuation in this sequence when this method
    /// is called, the default value of punctuation type `P` is inserted before
    /// the given value of type `T`.
    pub fn push(&mut self, value: T)
    where
        P: Default,
    {
        if !self.empty_or_trailing() {
            self.push_punct(Default::default());
        }
        self.push_value(value);
    }

    /// Inserts an element at position `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than the number of elements previously in
    /// this punctuated sequence.
    pub fn insert(&mut self, index: usize, value: T)
    where
        P: Default,
    {
        assert!(index <= self.len(), "Punctuated::insert: index out of range",);

        if index == self.len() {
            self.push(value);
        } else {
            self.inner.insert(index, (value, Default::default()));
        }
    }

    /// Clears the sequence of all values and punctuation, making it empty.
    pub fn clear(&mut self) {
        self.inner.clear();
        self.last = None;
    }

    /// Parses zero or more occurrences of `T` separated by punctuation of type
    /// `P`, with optional trailing punctuation.
    ///
    /// Parsing continues until the end of this parse stream. The entire content
    /// of this parse stream must consist of `T` and `P`.
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_terminated<U>(input: ParseStream, meta: &U) -> ParseResult<Self>
    where
        T: Parse<U>,
        P: Parse<U>,
        U: ?Sized,
    {
        Self::parse_terminated_with(input, T::parse, meta)
    }

    /// Parses zero or more occurrences of `T` using the given parse function,
    /// separated by punctuation of type `P`, with optional trailing
    /// punctuation.
    ///
    /// Like [`parse_terminated`], the entire content of this stream is expected
    /// to be parsed.
    ///
    /// [`parse_terminated`]: Punctuated::parse_terminated
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_terminated_with<U>(
        input: ParseStream,
        parser: fn(ParseStream, &U) -> ParseResult<T>,
        meta: &U,
    ) -> ParseResult<Self>
    where
        P: Parse<U>,
        U: ?Sized,
    {
        let mut punctuated = Punctuated::new();

        loop {
            if input.is_empty() {
                break;
            }
            let value = parser(input, meta)?;
            punctuated.push_value(value);
            if input.is_empty() {
                break;
            }
            let punct = input.parse(meta)?;
            punctuated.push_punct(punct);
        }

        Ok(punctuated)
    }

    /// Parses one or more occurrences of `T` separated by punctuation of type
    /// `P`, not accepting trailing punctuation.
    ///
    /// Parsing continues as long as punctuation `P` is present at the head of
    /// the stream. This method returns upon parsing a `T` and observing that it
    /// is not followed by a `P`, even if there are remaining tokens in the
    /// stream.
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_separated_nonempty<U>(input: ParseStream, meta: &U) -> ParseResult<Self>
    where
        T: Parse<U>,
        P: PToken + Parse<U>,
        U: ?Sized,
    {
        Self::parse_separated_nonempty_with(input, T::parse, meta)
    }

    /// Parses one or more occurrences of `T` using the given parse function,
    /// separated by punctuation of type `P`, not accepting trailing
    /// punctuation.
    ///
    /// Like [`parse_separated_nonempty`], may complete early without parsing
    /// the entire content of this stream.
    ///
    /// [`parse_separated_nonempty`]: Punctuated::parse_separated_nonempty
    ///
    /// *This function is available only if Syn is built with the `"parsing"`
    /// feature.*
    pub fn parse_separated_nonempty_with<U>(
        input: ParseStream,
        parser: fn(ParseStream, &U) -> ParseResult<T>,
        meta: &U,
    ) -> ParseResult<Self>
    where
        P: Peek + Parse<U>,
        U: ?Sized,
    {
        let mut punctuated = Punctuated::new();

        loop {
            let value = parser(input, meta)?;
            punctuated.push_value(value);
            if !P::peek(input) {
                break;
            }
            let punct = input.parse(meta)?;
            punctuated.push_punct(punct);
        }

        Ok(punctuated)
    }
}

use std::iter::FromIterator;

impl<T, P> FromIterator<T> for Punctuated<T, P>
where
    P: Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(i: I) -> Self {
        let mut ret = Punctuated::new();
        ret.extend(i);
        ret
    }
}

impl<T, P> Extend<T> for Punctuated<T, P>
where
    P: Default,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, i: I) {
        for value in i {
            self.push(value);
        }
    }
}

impl<T, P> FromIterator<Pair<T, P>> for Punctuated<T, P> {
    fn from_iter<I: IntoIterator<Item = Pair<T, P>>>(i: I) -> Self {
        let mut ret = Punctuated::new();
        ret.extend(i);
        ret
    }
}

impl<T, P> Extend<Pair<T, P>> for Punctuated<T, P> {
    fn extend<I: IntoIterator<Item = Pair<T, P>>>(&mut self, i: I) {
        assert!(
            self.empty_or_trailing(),
            "Punctuated::extend: Punctuated is not empty or does not have a trailing punctuation",
        );

        let mut nomore = false;
        for pair in i {
            if nomore {
                panic!("Punctuated extended with items after a Pair::End");
            }
            match pair {
                Pair::Punctuated(a, b) => self.inner.push((a, b)),
                Pair::End(a) => {
                    self.last = Some(Box::new(a));
                    nomore = true;
                },
            }
        }
    }
}

impl<T, P> IntoIterator for Punctuated<T, P> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        let mut elements = Vec::with_capacity(self.len());
        elements.extend(self.inner.into_iter().map(|pair| pair.0));
        elements.extend(self.last.map(|t| *t));

        IntoIter {
            inner: elements.into_iter(),
        }
    }
}

impl<'a, T, P> IntoIterator for &'a Punctuated<T, P> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        Punctuated::iter(self)
    }
}

//impl<'a, T, P> IntoIterator for &'a mut Punctuated<T, P> {
//type Item = &'a mut T;
//type IntoIter = IterMut<'a, T>;

//fn into_iter(self) -> Self::IntoIter {
//Punctuated::iter_mut(self)
//}

impl<T, P> Default for Punctuated<T, P> {
    fn default() -> Self {
        Punctuated::new()
    }
}

/// An iterator over borrowed pairs of type `Pair<&T, &P>`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct Pairs<'a, T: 'a, P: 'a> {
    inner: slice::Iter<'a, (T, P)>,
    last: option::IntoIter<&'a T>,
}

impl<'a, T, P> Iterator for Pairs<'a, T, P> {
    type Item = Pair<&'a T, &'a P>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|(t, p)| Pair::Punctuated(t, p))
            .or_else(|| self.last.next().map(Pair::End))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T, P> DoubleEndedIterator for Pairs<'a, T, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last
            .next()
            .map(Pair::End)
            .or_else(|| self.inner.next_back().map(|(t, p)| Pair::Punctuated(t, p)))
    }
}

impl<'a, T, P> ExactSizeIterator for Pairs<'a, T, P> {
    fn len(&self) -> usize {
        self.inner.len() + self.last.len()
    }
}

// No Clone bound on T or P.
impl<'a, T, P> Clone for Pairs<'a, T, P> {
    fn clone(&self) -> Self {
        Pairs {
            inner: self.inner.clone(),
            last: self.last.clone(),
        }
    }
}

/// An iterator over mutably borrowed pairs of type `Pair<&mut T, &mut P>`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct PairsMut<'a, T: 'a, P: 'a> {
    inner: slice::IterMut<'a, (T, P)>,
    last: option::IntoIter<&'a mut T>,
}

impl<'a, T, P> Iterator for PairsMut<'a, T, P> {
    type Item = Pair<&'a mut T, &'a mut P>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|(t, p)| Pair::Punctuated(t, p))
            .or_else(|| self.last.next().map(Pair::End))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T, P> DoubleEndedIterator for PairsMut<'a, T, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last
            .next()
            .map(Pair::End)
            .or_else(|| self.inner.next_back().map(|(t, p)| Pair::Punctuated(t, p)))
    }
}

impl<'a, T, P> ExactSizeIterator for PairsMut<'a, T, P> {
    fn len(&self) -> usize {
        self.inner.len() + self.last.len()
    }
}

/// An iterator over owned pairs of type `Pair<T, P>`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct IntoPairs<T, P> {
    inner: std::vec::IntoIter<(T, P)>,
    last: option::IntoIter<T>,
}

impl<T, P> Iterator for IntoPairs<T, P> {
    type Item = Pair<T, P>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|(t, p)| Pair::Punctuated(t, p))
            .or_else(|| self.last.next().map(Pair::End))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T, P> DoubleEndedIterator for IntoPairs<T, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last
            .next()
            .map(Pair::End)
            .or_else(|| self.inner.next_back().map(|(t, p)| Pair::Punctuated(t, p)))
    }
}

impl<T, P> ExactSizeIterator for IntoPairs<T, P> {
    fn len(&self) -> usize {
        self.inner.len() + self.last.len()
    }
}

impl<T, P> Clone for IntoPairs<T, P>
where
    T: Clone,
    P: Clone,
{
    fn clone(&self) -> Self {
        IntoPairs {
            inner: self.inner.clone(),
            last: self.last.clone(),
        }
    }
}

/// An iterator over owned values of type `T`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct IntoIter<T> {
    inner: std::vec::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> Clone for IntoIter<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        IntoIter {
            inner: self.inner.clone(),
        }
    }
}

/// An iterator over borrowed values of type `&T`.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub struct Iter<'a, T: 'a> {
    // The `Item = &'a T` needs to be specified to support rustc 1.31 and older.
    // On modern compilers we would be able to write just IterTrait<'a, T> where
    // Item can be inferred unambiguously from the supertrait.
    inner: Box<dyn IterTrait<'a, T, Item = &'a T> + 'a>,
}

trait IterTrait<'a, T: 'a>: DoubleEndedIterator<Item = &'a T> + ExactSizeIterator<Item = &'a T> {
    fn clone_box(&self) -> Box<dyn IterTrait<'a, T, Item = &'a T> + 'a>;
}

use std::{option, slice};
struct PrivateIter<'a, T: 'a, P: 'a> {
    inner: slice::Iter<'a, (T, P)>,
    last: option::IntoIter<&'a T>,
}

//pub(crate) fn empty_punctuated_iter<'a, T>() -> Iter<'a, T> {
//Iter {
//inner: Box::new(iter::empty()),
//}

// No Clone bound on T.
impl<'a, T> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone_box(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, T, P> Iterator for PrivateIter<'a, T, P> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|pair| &pair.0).or_else(|| self.last.next())
    }
}

impl<'a, T, P> DoubleEndedIterator for PrivateIter<'a, T, P> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last.next().or_else(|| self.inner.next_back().map(|pair| &pair.0))
    }
}

impl<'a, T, P> ExactSizeIterator for PrivateIter<'a, T, P> {
    fn len(&self) -> usize {
        self.inner.len() + self.last.len()
    }
}

// No Clone bound on T or P.
impl<'a, T, P> Clone for PrivateIter<'a, T, P> {
    fn clone(&self) -> Self {
        PrivateIter {
            inner: self.inner.clone(),
            last: self.last.clone(),
        }
    }
}

impl<'a, T: 'a, I: 'a> IterTrait<'a, T> for I
where
    I: DoubleEndedIterator<Item = &'a T> + ExactSizeIterator<Item = &'a T> + Clone,
{
    fn clone_box(&self) -> Box<dyn IterTrait<'a, T, Item = &'a T> + 'a> {
        Box::new(self.clone())
    }
}

/// A single syntax tree node of type `T` followed by its trailing punctuation
/// of type `P` if any.
///
/// Refer to the [module documentation] for details about punctuated sequences.
///
/// [module documentation]: self
pub enum Pair<T, P> {
    Punctuated(T, P),
    End(T),
}

impl<T, P> Pair<T, P> {
    /// Extracts the syntax tree node from this punctuated pair, discarding the
    /// following punctuation.
    pub fn into_value(self) -> T {
        match self {
            Pair::Punctuated(t, _) | Pair::End(t) => t,
        }
    }

    /// Borrows the syntax tree node from this punctuated pair.
    pub fn value(&self) -> &T {
        match self {
            Pair::Punctuated(t, _) | Pair::End(t) => t,
        }
    }

    /// Mutably borrows the syntax tree node from this punctuated pair.
    pub fn value_mut(&mut self) -> &mut T {
        match self {
            Pair::Punctuated(t, _) | Pair::End(t) => t,
        }
    }

    /// Borrows the punctuation from this punctuated pair, unless this pair is
    /// the final one and there is no trailing punctuation.
    pub fn punct(&self) -> Option<&P> {
        match self {
            Pair::Punctuated(_, p) => Some(p),
            Pair::End(_) => None,
        }
    }

    /// Creates a punctuated pair out of a syntax tree node and an optional
    /// following punctuation.
    pub fn new(t: T, p: Option<P>) -> Self {
        match p {
            Some(p) => Pair::Punctuated(t, p),
            None => Pair::End(t),
        }
    }

    /// Produces this punctuated pair as a tuple of syntax tree node and
    /// optional following punctuation.
    pub fn into_tuple(self) -> (T, Option<P>) {
        match self {
            Pair::Punctuated(t, p) => (t, Some(p)),
            Pair::End(t) => (t, None),
        }
    }
}

impl<T, P> Clone for Pair<T, P>
where
    T: Clone,
    P: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Pair::Punctuated(t, p) => Pair::Punctuated(t.clone(), p.clone()),
            Pair::End(t) => Pair::End(t.clone()),
        }
    }
}

/*
impl<T, P> Index<usize> for Punctuated<T, P> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index == self.len() - 1 {
            match &self.last {
                Some(t) => t,
                None => &self.inner[index].0,
            }
        } else {
            &self.inner[index].0
        }
    }
}

impl<T, P> IndexMut<usize> for Punctuated<T, P> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index == self.len() - 1 {
            match &mut self.last {
                Some(t) => t,
                None => &mut self.inner[index].0,
            }
        } else {
            &mut self.inner[index].0
        }
    }
}
*/
