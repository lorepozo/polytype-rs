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
/// // equivalent to:
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
/// // equivalent to:
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
/// // equivalent to:
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
/// // equivalent to:
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
/// // equivalent to:
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

/// Creates a [`Polytype::Binding`] or [`Polytype::Monotype`][] (convenience for
/// common pattern).
///
/// ```rust,ignore
/// // equivalent to:
/// Polytype::Binding(ident, tp)
/// // or
/// Polytype::Monotype(tp)
/// ```
///
/// # Examples
///
/// Make a monotype:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::{Type, Polytype};
/// # fn main() {
/// let t = ptp!(tp!(int));
/// assert_eq!(format!("{}", t), "int");
/// // equivalent to:
/// let t_eq = Polytype::Monotype(Type::Constructed("int", vec![]));
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// Make a bound type:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # use polytype::{Type, Polytype};
/// # fn main() {
/// let t = ptp!(0, ptp!(arrow![tp!(0), tp!(0)]));
/// assert_eq!(format!("{}", t), "∀t0. t0 → t0");
/// // equivalent to:
/// let t_eq = Polytype::Binding{
///     variable: 0,
///     body: Box::new(
///         Polytype::Monotype(
///             Type::Constructed("→",
///                               vec![Type::Variable(0),
///                                    Type::Variable(0)])))};
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// [`Polytype::Binding`]: enum.Polytype.html#variant.Binding
/// [`Polytype::Monotype`]: enum.Polytype.html#variant.Monotype
#[macro_export]
macro_rules! ptp {
    ($n:expr, $t:expr) => {
        $crate::Polytype::Binding{
            variable: $n,
            body: Box::new($t),
        }
    };
    ($t:expr) => ($crate::Polytype::Monotype($t));
}
