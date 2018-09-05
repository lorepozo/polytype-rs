use nom::types::CompleteStr;
use nom::{alpha, digit};
use std::marker::PhantomData;
use std::num::ParseIntError;

use {Name, Type, TypeSchema};

pub fn parse_type<N: Name>(input: &str) -> Result<Type<N>, ()> {
    match Parser::default().monotype(CompleteStr(input)).1 {
        Ok((_, t)) => Ok(t),
        _ => Err(()),
    }
}
pub fn parse_typeschema<N: Name>(input: &str) -> Result<TypeSchema<N>, ()> {
    match Parser::default().polytype(CompleteStr(input)).1 {
        Ok((_, t)) => Ok(t),
        _ => Err(()),
    }
}

fn nom_u16(inp: CompleteStr) -> Result<u16, ParseIntError> {
    inp.parse()
}

// hack for polymorphism with nom
pub struct Parser<N: Name>(PhantomData<N>);
impl<N: Name> Default for Parser<N> {
    fn default() -> Self {
        Parser(PhantomData)
    }
}
impl<N: Name> Parser<N> {
    method!(
        var<Parser<N>, CompleteStr, Type<N>>,
        self,
        do_parse!(tag!("t") >> num: map_res!(digit, nom_u16) >> (Type::Variable(num)))
    );
    method!(
        constructed_simple<Parser<N>, CompleteStr, Type<N>>,
        self,
        do_parse!(
            name_raw: alpha
                >> name: expr_res!(N::parse(&name_raw))
                >> (Type::Constructed(name, vec![]))
        )
    );
    method!(constructed_complex<Parser<N>, CompleteStr, Type<N>>, mut self,
               do_parse!(
                   name_raw: alpha >>
                   name: expr_res!(N::parse(&name_raw)) >>
                   tag!("(") >>
                   args: separated_list!(tag!(","), ws!(call_m!(self.monotype))) >>
                   tag!(")") >>
                   (Type::Constructed(name, args)))
        );
    method!(arrow<Parser<N>, CompleteStr, Type<N>>, mut self,
               do_parse!(
                   alpha: ws!(alt!(call_m!(self.parenthetical) |
                                   call_m!(self.var) |
                                   call_m!(self.constructed_complex) |
                                   call_m!(self.constructed_simple))) >>
                   alt!(tag!("→") | tag!("->")) >>
                   beta: ws!(call_m!(self.monotype)) >>
                   (Type::arrow(alpha, beta)))
        );
    method!(parenthetical<Parser<N>, CompleteStr, Type<N>>, mut self,
               do_parse!(
                   tag!("(") >>
                   interior: call_m!(self.arrow) >>
                   tag!(")") >>
                   (interior))
        );
    method!(binding<Parser<N>, CompleteStr, TypeSchema<N>>, mut self,
               do_parse!(
                   opt!(tag!("∀")) >>
                   tag!("t") >>
                   variable: map_res!(digit, nom_u16) >>
                   ws!(tag!(".")) >>
                   body: map!(call_m!(self.polytype), Box::new) >>
                   (TypeSchema::Polytype{variable, body}))
        );
    method!(monotype<Parser<N>, CompleteStr, Type<N>>, mut self,
               alt!(call_m!(self.arrow) |
                    call_m!(self.var) |
                    call_m!(self.constructed_complex) |
                    call_m!(self.constructed_simple))
        );
    method!(polytype<Parser<N>, CompleteStr, TypeSchema<N>>, mut self,
            alt!(call_m!(self.binding) |
                 map!(call_m!(self.monotype), TypeSchema::Monotype))
        );
}
