/// Creates a [`Type::Arrow`] of `tp0 → tp1 → ...` (convenience for nested arrows).
///
/// This is equivalent to:
///
/// ```rust,ignore
/// Type::Arrow(Box::new(Arrow {
///     arg: tp0,
///     ret: Type::Arrow(Box::new(Arrow {
///         arg: tp1,
///         ret: Type::Arrow(Box::new(Arrow {
///             arg: tp2,
///             ...
///         })),
///     })),
/// }))
/// ```
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate polytype;
/// use polytype::{Arrow, Type};
///
/// # fn main() {
/// let t = arrow![Type::Variable(0), Type::Variable(1), Type::Variable(2)];
/// assert_eq!(format!("{}", t), "t0 → t1 → t2");
/// // equivalent to:
/// let t_eq = Type::Arrow(Box::new(Arrow{
///     arg: Type::Variable(0),
///     ret: Type::Arrow(Box::new(Arrow{
///         arg: Type::Variable(1),
///         ret: Type::Variable(2),
///     })),
/// }));
/// assert_eq!(t, t_eq);
/// # }
/// ```
///
/// [`Type::Arrow`]: enum.Type.html#variant.Arrow
#[macro_export]
macro_rules! arrow {
    [$x:expr] => ($x);
    [$x:expr, $($xs:expr),*] => (
        match ($x, arrow![$($xs),+]) {
            (arg, ret) => $crate::Type::Arrow(Box::new($crate::Arrow { arg, ret }))
        }
    );
    [$x:expr, $($xs:expr,)*] => (arrow![$x, $($xs),*])
}

/// Creates a [`Type::Constructed`] or [`Type::Variable`][] (convenience for common pattern).
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
