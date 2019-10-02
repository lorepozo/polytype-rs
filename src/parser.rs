use nom::{alpha, digit, types::CompleteStr};
use nom::{alt, call_m, do_parse, expr_res, map, map_res, method, opt, separated_list, tag, ws};

#[allow(unused_imports)]
use nom::call; // FIXME see https://github.com/Geal/nom/pull/871

use std::marker::PhantomData;
use std::num::ParseIntError;

use crate::{Name, Type, TypeSchema};

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

fn nom_usize(inp: CompleteStr<'_>) -> Result<usize, ParseIntError> {
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
        var<Parser<N>, CompleteStr<'_>, Type<N>>,
        self,
        do_parse!(tag!("t") >> num: map_res!(digit, nom_usize) >> (Type::Variable(num)))
    );
    method!(
        constructed_simple<Parser<N>, CompleteStr<'_>, Type<N>>,
        self,
        do_parse!(
            name_raw: alpha
                >> name: expr_res!(N::parse(&name_raw))
                >> (Type::Constructed(name, vec![]))
        )
    );
    method!(constructed_complex<Parser<N>, CompleteStr<'_>, Type<N>>, mut self,
               do_parse!(
                   name_raw: alpha >>
                   name: expr_res!(N::parse(&name_raw)) >>
                   tag!("(") >>
                   args: separated_list!(tag!(","), ws!(call_m!(self.monotype))) >>
                   tag!(")") >>
                   (Type::Constructed(name, args)))
        );
    method!(arrow<Parser<N>, CompleteStr<'_>, Type<N>>, mut self,
               do_parse!(
                   alpha: ws!(alt!(call_m!(self.parenthetical) |
                                   call_m!(self.var) |
                                   call_m!(self.constructed_complex) |
                                   call_m!(self.constructed_simple))) >>
                   alt!(tag!("→") | tag!("->")) >>
                   beta: ws!(call_m!(self.monotype)) >>
                   (Type::arrow(alpha, beta)))
        );
    method!(parenthetical<Parser<N>, CompleteStr<'_>, Type<N>>, mut self,
               do_parse!(
                   tag!("(") >>
                   interior: call_m!(self.arrow) >>
                   tag!(")") >>
                   (interior))
        );
    method!(binding<Parser<N>, CompleteStr<'_>, TypeSchema<N>>, mut self,
               do_parse!(
                   opt!(tag!("∀")) >>
                   tag!("t") >>
                   variable: map_res!(digit, nom_usize) >>
                   ws!(tag!(".")) >>
                   body: map!(call_m!(self.polytype), Box::new) >>
                   (TypeSchema::Polytype{variable, body}))
        );
    method!(monotype<Parser<N>, CompleteStr<'_>, Type<N>>, mut self,
               alt!(call_m!(self.arrow) |
                    call_m!(self.var) |
                    call_m!(self.constructed_complex) |
                    call_m!(self.constructed_simple))
        );
    method!(polytype<Parser<N>, CompleteStr<'_>, TypeSchema<N>>, mut self,
            alt!(call_m!(self.binding) |
                 map!(call_m!(self.monotype), TypeSchema::Monotype))
        );
}
impl<N: Name> TypeSchema<N> {
    /// Parse a [`TypeSchema`] from a string. This round-trips with [`Display`].
    /// This is a **leaky** operation and should be avoided wherever possible:
    /// names of constructed types will remain until program termination.
    ///
    /// The "for-all" `∀` is optional.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{ptp, tp, TypeSchema};
    /// let t_par = TypeSchema::parse("∀t0. t0 -> t0").expect("valid type");
    /// let t_lit = ptp!(0; @arrow[tp!(0), tp!(0)]);
    /// assert_eq!(t_par, t_lit);
    ///
    /// let s = "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1";
    /// let t: TypeSchema<&'static str> = TypeSchema::parse(s).expect("valid type");
    /// let round_trip = t.to_string();
    /// assert_eq!(s, round_trip);
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn parse(s: &str) -> Result<TypeSchema<N>, ()> {
        parse_typeschema(s)
    }
}
impl<N: Name> Type<N> {
    /// Parse a type from a string. This round-trips with [`Display`]. This is a
    /// **leaky** operation and should be avoided wherever possible: names of
    /// constructed types will remain until program termination.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, Type};
    /// let t_par = Type::parse("int -> hashmap(str, list(bool))").expect("valid type");
    /// let t_lit = tp!(@arrow[
    ///     tp!(int),
    ///     tp!(hashmap(
    ///         tp!(str),
    ///         tp!(list(tp!(bool))),
    ///     )),
    /// ]);
    /// assert_eq!(t_par, t_lit);
    ///
    /// let s = "(t1 → t0 → t1) → t1 → list(t0) → t1";
    /// let t: Type<&'static str> = Type::parse(s).expect("valid type");
    /// let round_trip = t.to_string();
    /// assert_eq!(s, round_trip);
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    pub fn parse(s: &str) -> Result<Type<N>, ()> {
        parse_type(s)
    }
}
