use crate::{Name, Schema, Ty, TypeContext, Variable};
#[allow(unused_imports)]
use nom::call; // FIXME see https://github.com/Geal/nom/pull/871
use nom::{alpha, digit, types::CompleteStr};
use nom::{
    alt, alt_sep, call_m, do_parse, error_position, expr_res, map, map_res, method, opt, sep,
    separated_list, tag, wrap_sep, ws,
};
use std::num::ParseIntError;

pub struct Parser<'ctx, N: Name>(TypeContext<'ctx, N>);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParseError;

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ParseError")
    }
}

impl std::error::Error for ParseError {}

pub fn parse_type<'ctx, N: Name>(
    ctx: &TypeContext<'ctx, N>,
    input: &str,
) -> Result<Ty<'ctx, N>, ParseError> {
    match Parser::new(ctx.clone()).monotype(CompleteStr(input)).1 {
        Ok((_, t)) => Ok(t),
        _ => Err(ParseError),
    }
}
pub fn parse_typeschema<'ctx, N: Name>(
    ctx: &TypeContext<'ctx, N>,
    input: &str,
) -> Result<Schema<'ctx, N>, ParseError> {
    match Parser::new(ctx.clone()).polytype(CompleteStr(input)).1 {
        Ok((_, t)) => Ok(t),
        _ => Err(ParseError),
    }
}

fn nom_usize(inp: CompleteStr<'_>) -> Result<usize, ParseIntError> {
    inp.parse()
}

impl<'ctx, N: Name> Parser<'ctx, N> {
    fn new(ctx: TypeContext<'ctx, N>) -> Self {
        Parser(ctx)
    }
}
impl<'ctx, N: Name> Parser<'ctx, N> {
    method!(
        var<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>,
        self,
        do_parse!(
            tag!("t") >> num: map_res!(digit, nom_usize) >> (self.0.intern_tvar(Variable(num)))
        )
    );
    method!(
        constructed_simple<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>,
        self,
        do_parse!(
            name_raw: alpha
                >> name: expr_res!(N::parse(&name_raw).map(|name| self.0.intern_name(name)))
                >> (self.0.intern_tcon(name, self.0.intern_args(&[])))
        )
    );
    method!(constructed_complex<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>, mut self,
           do_parse!(
               name_raw: alpha >>
               name: expr_res!(N::parse(&name_raw).map(|name| self.0.intern_name(name))) >>
               tag!("(") >>
               args: separated_list!(tag!(","), ws!(call_m!(self.monotype))) >>
               tag!(")") >>
               (self.0.intern_tcon(name, self.0.intern_args(&args))))
    );
    method!(arrow<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>, mut self,
           do_parse!(
               alpha: ws!(alt!(call_m!(self.parenthetical) |
                               call_m!(self.var) |
                               call_m!(self.constructed_complex) |
                               call_m!(self.constructed_simple))) >>
               alt!(tag!("→") | tag!("->")) >>
               beta: ws!(call_m!(self.monotype)) >>
               (self.0.arrow(alpha, beta)))
    );
    method!(parenthetical<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>, mut self,
           do_parse!(
               tag!("(") >>
               interior: call_m!(self.arrow) >>
               tag!(")") >>
               (interior))
    );
    method!(binding<Parser<'ctx, N>, CompleteStr<'_>, Schema<'ctx, N>>, mut self,
           do_parse!(
               opt!(tag!("∀")) >>
               tag!("t") >>
               variable: map_res!(digit, nom_usize) >>
               ws!(tag!(".")) >>
               body: call_m!(self.polytype) >>
               (self.0.intern_polytype(Variable(variable), body)))
    );
    method!(monotype<Parser<'ctx, N>, CompleteStr<'_>, Ty<'ctx, N>>, mut self,
           alt!(call_m!(self.arrow) |
                call_m!(self.var) |
                call_m!(self.constructed_complex) |
                call_m!(self.constructed_simple))
    );
    method!(polytype<Parser<'ctx, N>, CompleteStr<'_>, Schema<'ctx, N>>, mut self,
        alt!(call_m!(self.binding) |
             map!(call_m!(self.monotype), |t| self.0.intern_monotype(t)))
    );
}
