/// Creates a [`Type`][] (convenience for common patterns).
///
/// Specifically, a `Type<&'static str>`, where all names are static strings.
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
/// // or
/// Type::arrow(
///     tp0,
///     Type::arrow(
///         tp1,
///         Type::arrow(
///             tp2,
///             ...,
///         )
///     )
/// )
/// ```
///
/// # Examples
///
/// Make a primitive type:
///
/// ```
/// # use polytype::{tp, Type};
/// let t = tp!(int);
/// assert_eq!(format!("{}", t), "int");
/// // Equivalent to:
/// let t_eq = Type::Constructed("int", vec![]);
/// assert_eq!(t, t_eq);
/// ```
///
/// Make a variable type:
///
/// ```
/// # use polytype::{tp, Type};
/// let t = tp!(0);
/// assert_eq!(format!("{}", t), "t0");
/// // Equivalent to:
/// let t_eq = Type::Variable(0);
/// assert_eq!(t, t_eq);
/// ```
///
/// Make a composite type:
///
/// ```
/// # use polytype::{tp, Type};
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
/// ```
///
/// Make an arrow:
///
/// ```
/// # use polytype::{tp, Type};
/// let t = tp!(@arrow[Type::Variable(0), Type::Variable(1), Type::Variable(2)]);
/// assert_eq!(format!("{}", t), "t0 → t1 → t2");
/// // Equivalent to:
/// let t_eq = Type::arrow(
///     Type::Variable(0),
///     Type::arrow(
///         Type::Variable(1),
///         Type::Variable(2),
///     )
/// );
/// assert_eq!(t, t_eq);
/// ```
///
/// Nest them for more complex types:
///
/// ```
/// # use polytype::{tp, Type};
/// // mapi: (int → α → β) → [α] → [β]
/// let t = tp!(@arrow[
///     tp!(@arrow[tp!(int), tp!(0), tp!(1)]),
///     tp!(list(tp!(0))),
///     tp!(list(tp!(1))),
/// ]);
/// assert_eq!(format!("{}", t), "(int → t0 → t1) → list(t0) → list(t1)");
/// ```
///
/// [`Type`]: enum.Type.html
#[macro_export]
macro_rules! tp {
    ($n:ident) => ($crate::Type::Constructed(stringify!($n), Vec::new()));
    ($n:ident($($x:expr),*)) => {
        $crate::Type::Constructed(stringify!($n), vec![$($x),*])
    };
    ($n:ident($($x:expr,)*)) => ($crate::tp!($n($($x),*)));
    ($n:expr) => ($crate::Type::Variable($n) as $crate::Type<&'static str>);
    (@arrow[$x:expr]) => ($x as $crate::Type<&'static str>);
    (@arrow[$x:expr, $($xs:expr),*]) => (
        match ($x, $crate::tp!(@arrow[$($xs),+])) {
            (arg, ret) => $crate::Type::arrow(arg, ret)
        }
    );
    (@arrow[$x:expr, $($xs:expr,)*]) => ($crate::tp!(@arrow[$x, $($xs),*]))
}

/// Creates a [`TypeSchema`][] (convenience for common patterns).
///
/// Specifically, a `TypeSchema<&'static str>`, where all names are static strings.
///
/// ```rust,ignore
/// // Equivalent to:
/// TypeSchema::Monotype(tp)
/// // Or
/// TypeSchema::Polytype {
///     variable1,
///     body: Box::new(TypeSchema::Polytype {
///         variable2,
///         body: ...
///     })
/// }
/// ```
///
/// This behaves much like [`tp!`], but this gives a [`TypeSchema`] and you can
/// express quantified type variables in a prefixed comma-delimited list. There
/// are three usage patterns, shown in the examples below.
///
/// # Examples
///
/// If you don't want to do any quantification, using `ptp!` on its own is just
/// like wrapping [`tp!`] with a [`TypeSchema::Monotype`]:
///
/// ```
/// # use polytype::{ptp, tp, Type, TypeSchema};
/// let t = ptp!(dict(tp!(str), tp!(int)));
/// assert_eq!(format!("{}", t), "dict(str,int)");
/// // Equivalent to:
/// let t_eq = TypeSchema::Monotype(
///     Type::Constructed("dict", vec![
///         Type::Constructed("str", vec![]),
///         Type::Constructed("int", vec![]),
///     ])
/// );
/// assert_eq!(t, t_eq);
/// ```
///
/// If you want to do quantification over a known monotype, precede the type
/// with quantified variables follows by a semicolon `;` (note that the
/// subsequent monotype is treated like the [`tp!`] macro):
///
/// ```
/// # use polytype::{ptp, tp, Type, TypeSchema};
/// let t = ptp!(0, 1; @arrow[tp!(0), tp!(1), tp!(0)]);
/// assert_eq!(format!("{}", t), "∀t0. ∀t1. t0 → t1 → t0");
/// // Equivalent to:
/// let t_eq = TypeSchema::Polytype {
///     variable: 0,
///     body: Box::new(TypeSchema::Polytype {
///         variable: 1,
///         body: Box::new(TypeSchema::Monotype(
///             Type::arrow(
///                 Type::Variable(0),
///                 Type::arrow(
///                     Type::Variable(1),
///                     Type::Variable(0),
///                 )
///             )
///         ))
///     })
/// };
/// assert_eq!(t, t_eq);
/// ```
///
/// If you want want do quantification over an existing [`TypeSchema`], use a
/// comma after the quantified variables:
///
/// ```
/// # use polytype::{ptp, tp, Type, TypeSchema};
/// let inner = tp!(@arrow[tp!(0), tp!(1), tp!(0)]);
/// let t = ptp!(0, 1, TypeSchema::Monotype(inner.clone()));
/// assert_eq!(format!("{}", t), "∀t0. ∀t1. t0 → t1 → t0");
/// // Equivalent to:
/// let t_eq = TypeSchema::Polytype {
///     variable: 0,
///     body: Box::new(TypeSchema::Polytype {
///         variable: 1,
///         body: Box::new(TypeSchema::Monotype(inner))
///     })
/// };
/// assert_eq!(t, t_eq);
/// ```
///
/// [`TypeSchema::Polytype`]: enum.TypeSchema.html#variant.Polytype
/// [`TypeSchema::Monotype`]: enum.TypeSchema.html#variant.Monotype
/// [`TypeSchema`]: enum.TypeSchema.html
/// [`Type`]: enum.Type.html
/// [`tp!`]: macro.tp.html
#[macro_export]
macro_rules! ptp {
    ($n:expr; $($t:tt)+) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new($crate::TypeSchema::Monotype($crate::tp!($($t)+))),
        }
    };
    ($n:expr, $body:expr) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new($body),
        }
    };
    ($n:expr, $($t:tt)+) => {
        $crate::TypeSchema::Polytype {
            variable: $n,
            body: Box::new($crate::ptp!($($t)+)),
        }
    };
    ($($t:tt)+) => {
        $crate::TypeSchema::Monotype($crate::tp!($($t)+))
    };
}
