use std::fmt::Formatter;
use std::str::FromStr;

use winnow::{
    ascii::{alpha1, digit1, multispace0},
    combinator::{alt, delimited, opt, preceded, separated, separated_pair},
    prelude::*,
    Parser,
};

use crate::{Name, Type, TypeScheme};

#[derive(Debug)]
pub struct ParseError(pub(crate) String);
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for ParseError {}

impl<N: Name> FromStr for TypeScheme<N> {
    type Err = ParseError;

    /// Parse a [`TypeScheme`] from a string. This round-trips with [`Display`].
    /// This is a **leaky** operation and should be avoided wherever possible:
    /// names of constructed types will remain until program termination.
    ///
    /// The "for-all" `∀` is optional.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{ptp, tp, TypeScheme};
    /// let t_par: TypeScheme = "∀t0. t0 -> t0".parse().expect("invalid type");
    /// let t_lit = ptp!(0; @arrow[tp!(0), tp!(0)]);
    /// assert_eq!(t_par, t_lit);
    ///
    /// let s = "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1";
    /// let t: TypeScheme<&'static str> = s.parse().expect("invalid type");
    /// let round_trip = t.to_string();
    /// assert_eq!(s, round_trip);
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    /// [`TypeScheme`]: enum.TypeScheme.html
    fn from_str(s: &str) -> Result<TypeScheme<N>, ParseError> {
        parse_polytype
            .parse(s)
            .map_err(|e| ParseError(e.to_string()))
    }
}

impl<N: Name> FromStr for Type<N> {
    type Err = ParseError;

    /// Parse a type from a string. This round-trips with [`Display`]. This is a
    /// **leaky** operation and should be avoided wherever possible: names of
    /// constructed types will remain until program termination.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, Type};
    /// let t_par: Type = "int -> hashmap(str, list(bool))".parse().expect("valid type");
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
    /// let t: Type<&'static str> = s.parse().expect("valid type");
    /// let round_trip = t.to_string();
    /// assert_eq!(s, round_trip);
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    fn from_str(s: &str) -> Result<Type<N>, ParseError> {
        parse_monotype
            .parse(s)
            .map_err(|e| ParseError(e.to_string()))
    }
}

fn parse_var<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    preceded('t', digit1)
        .parse_to()
        .map(Type::Variable)
        .parse_next(input)
}
fn parse_constructed_simple<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    alpha1
        .try_map(N::parse)
        .map(|name| Type::Constructed(name, vec![]))
        .parse_next(input)
}
fn parse_constructed_complex<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    let (name, args) = (
        alpha1.try_map(N::parse),
        delimited(
            '(',
            separated(
                0..,
                delimited(multispace0, parse_monotype, multispace0),
                ',',
            ),
            ')',
        ),
    )
        .parse_next(input)?;
    Ok(Type::Constructed(name, args))
}

fn parse_arrow<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    let (alpha, beta) = delimited(
        multispace0,
        separated_pair(
            alt((
                parse_parenthetical,
                parse_var,
                parse_constructed_complex,
                parse_constructed_simple,
            )),
            delimited(multispace0, alt(("→", "->")), multispace0),
            parse_monotype,
        ),
        multispace0,
    )
    .parse_next(input)?;
    Ok(Type::arrow(alpha, beta))
}

fn parse_parenthetical<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    delimited('(', parse_arrow, ')').parse_next(input)
}

fn parse_binding<N: Name>(input: &mut &str) -> PResult<TypeScheme<N>> {
    let (variable, body) = preceded(
        opt('∀'),
        separated_pair(
            preceded('t', digit1).parse_to::<usize>(),
            delimited(multispace0, '.', multispace0),
            parse_polytype,
        ),
    )
    .parse_next(input)?;
    let body = Box::new(body);
    Ok(TypeScheme::Polytype { variable, body })
}

fn parse_monotype<N: Name>(input: &mut &str) -> PResult<Type<N>> {
    alt((
        parse_arrow,
        parse_var,
        parse_constructed_complex,
        parse_constructed_simple,
    ))
    .parse_next(input)
}

fn parse_polytype<N: Name>(input: &mut &str) -> PResult<TypeScheme<N>> {
    alt((parse_binding, parse_monotype.map(TypeScheme::Monotype))).parse_next(input)
}
