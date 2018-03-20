/// Creates an [`arrow`] of `tp0 → tp1 → ...` (convenience for nested
/// arrows).
///
/// This is equivalent to:
///
/// ```rust,ignore
/// Type::arrow(tp0,
///             Type::arrow(tp1,
///                         Type::arrow(tp2,
///                         ...
///                         )
///             )
/// )
/// ```
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate polytype;
/// use polytype::{Type};
///
/// # fn main() {
/// let t = arrow![Type::Variable(0), Type::Variable(1), Type::Variable(2)];
/// assert_eq!(format!("{}", t), "t0 → t1 → t2");
/// // Equivalent to:
/// let t_eq = Type::arrow(Type::Variable(0),
///                        Type::arrow(Type::Variable(1),
///                                    Type::Variable(2)));
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// [`arrow`]: enum.Type.html#method.arrow
#[macro_export]
macro_rules! arrow {
    [$x:expr] => ($x);
    [$x:expr, $($xs:expr),*] => (
        match ($x, arrow![$($xs),+]) {
            (arg, ret) => $crate::Type::arrow(arg, ret)
        }
    );
    [$x:expr, $($xs:expr,)*] => (arrow![$x, $($xs),*])
}

/// Creates a [`Type::Constructed`] or [`Type::Variable`][] (convenience for
/// common pattern).
///
/// ```rust,ignore
/// // Equivalent to:
/// Type::Constructed(ident, vec![
///     tp1,
///     tp2,
///     ...
/// ])
/// // or
/// Type::Variable(n)
/// ```
///
/// # Examples
///
/// Make a primitive type:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::Type;
/// # fn main() {
/// let t = tp!(int);
/// assert_eq!(format!("{}", t), "int");
/// // Equivalent to:
/// let t_eq = Type::Constructed("int", vec![]);
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Make a variable type:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::Type;
/// # fn main() {
/// let t = tp!(0);
/// assert_eq!(format!("{}", t), "t0");
/// // Equivalent to:
/// let t_eq = Type::Variable(0);
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Make a composite type:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::Type;
/// # fn main() {
/// let tint = tp!(int);
/// let tstr = tp!(str);
/// let t = tp!(dict(tstr, tint));
/// assert_eq!(format!("{}", t), "dict(str,int)");
/// // Equivalent to:
/// let t_eq = Type::Constructed("dict", vec![
///     Type::Constructed("str", vec![]),
///     Type::Constructed("int", vec![]),
/// ]);
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Nest them for more complex types:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::Type;
/// # fn main() {
/// // mapi: (int → α → β) → [α] → [β]
/// let t = arrow![
///     arrow![tp!(int), tp!(0), tp!(1)],
///     tp!(list(tp!(0))),
///     tp!(list(tp!(1))),
/// ];
/// assert_eq!(format!("{}", t), "(int → t0 → t1) → list(t0) → list(t1)");
/// # }
/// ```
///
/// [`Type::Constructed`]: enum.Type.html#variant.Constructed
/// [`Type::Variable`]: enum.Type.html#variant.Variable
#[macro_export]
macro_rules! tp {
    ($n:ident) => ($crate::Type::Constructed(stringify!($n), Vec::new()));
    ($n:ident($($x:expr),*)) => {
        $crate::Type::Constructed(stringify!($n), vec![$($x),*])
    };
    ($n:ident($($x:expr,)*)) => (tp!($n($($x),*)));
    ($n:expr) => ($crate::Type::Variable($n));
}

/// Creates a [`TypeSchema::Polytype`] or [`TypeSchema::Monotype`][]
/// (convenience for common pattern).
///
/// ```rust,ignore
/// // Equivalent to:
/// TypeSchema::Polytype(ident, tp)
/// // Or
/// TypeSchema::Monotype(tp)
/// ```
///
/// *Note:* The syntax follows `ptp!(0, 1,...n, typeschema)` or `ptp!(0, 1,...n;
/// type)` where `n` can be any number of quantified variables to be bound. See
/// below for more details.
///
/// # Examples
///
/// Make a monotype:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::{Type, TypeSchema};
/// # fn main() {
/// let t = ptp!(tp!(int));
/// assert_eq!(format!("{}", t), "int");
/// // Equivalent to:
/// let t_eq = TypeSchema::Monotype(Type::Constructed("int", vec![]));
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Make a bound type (from a [`TypeSchema`]):
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::{Type, TypeSchema};
/// # fn main() {
/// let inner_polytype = ptp!(1; arrow![tp!(0), tp!(1), tp!(0)]);
/// let t = ptp!(0, inner_polytype);
/// assert_eq!(format!("{}", t), "∀t0. ∀t1. t0 → t1 → t0");
/// // Equivalent to:
/// let t_eq = TypeSchema::Polytype{
///     variable: 0,
///     body: Box::new(
///         TypeSchema::Polytype{
///             variable: 1,
///             body: Box::new(
///                 TypeSchema::Monotype(
///                     Type::Constructed(
///                         "→",
///                         vec![Type::Variable(0),
///                              Type::Constructed(
///                                  "→",
///                                  vec![Type::Variable(1),
///                                       Type::Variable(0)
///                                  ]
///                              )
///                         ]
///                     )
///                 )
///             )
///         }
///     )
/// };
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Make a bound type (from a [`Type`]):
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::{Type, TypeSchema};
/// # fn main() {
/// let t = ptp!(0; arrow![tp!(0), tp!(0)]);
/// assert_eq!(format!("{}", t), "∀t0. t0 → t0");
/// // Equivalent to:
/// let t_eq = TypeSchema::Polytype{
///     variable: 0,
///     body: Box::new(
///         TypeSchema::Monotype(
///             Type::Constructed(
///                 "→",
///                 vec![Type::Variable(0),
///                      Type::Variable(0)]
///             )
///         )
///     )
/// };
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// [`TypeSchema::Polytype`]: enum.TypeSchema.html#variant.Polytype
/// [`TypeSchema::Monotype`]: enum.TypeSchema.html#variant.Monotype
/// [`TypeSchema`]: enum.TypeSchema.html
/// [`Type`]: enum.Type.html
#[macro_export]
macro_rules! ptp {
    ($n:expr; $body:expr) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new(ptp!($body)),
        }
    };
    ($n:expr, $body:expr) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new($body),
        }
    };
    ($n:expr, $($tail:tt)+) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new(ptp!($($tail)+)),
        }
    };
    ($t:expr) => {
        $crate::TypeSchema::Monotype($t)
    };
}
