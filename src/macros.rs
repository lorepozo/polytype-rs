/// Creates a [`Ty`] (convenience for common patterns).
///
/// Specifically, a `&Type<'ctx, &'static str>`, where all names are static strings.
///
/// ```rust,ignore
/// // Equivalent to:
/// &'ctx Type::Constructed(ident, vec![
///     tp1,
///     tp2,
///     ...
/// ])
/// // or
/// &'ctx Type::Variable(n)
/// ```
///
/// # Examples
///
/// Make a primitive type:
///
/// ```
/// # use polytype::{tp, with_ctx};
/// # with_ctx(32, |ctx| {
/// let t_macro = tp!(ctx, int);
/// assert_eq!(t_macro.to_string(), "int");
/// // Equivalent to:
/// let name = ctx.intern_name("int");
/// let t_manual = ctx.intern_tcon(name, &[]);
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// Make a variable type:
///
/// ```
/// # use polytype::{tp, with_ctx, Ty, Variable};
/// # with_ctx(32, |ctx| {
/// # ctx.intern_name("int");
/// let t_macro = tp!(ctx, 0);
/// assert_eq!(t_macro.to_string(), "t0");
/// // Equivalent to:
/// let t_manual = ctx.intern_tvar(Variable(0));
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// Make a composite type:
///
/// ```
/// # use polytype::{tp, with_ctx, Ty, Variable};
/// # with_ctx(32, |ctx| {
/// let t_macro = tp!(ctx, dict(tp!(ctx, str), tp!(ctx, int)));
/// assert_eq!(t_macro.to_string(), "dict(str,int)");
/// // Equivalent to:
/// let nint = ctx.intern_name("int");
/// let nstr = ctx.intern_name("str");
/// let ndict = ctx.intern_name("dict");
/// let tint_manual = ctx.intern_tcon(nint, &[]);
/// let tstr_manual = ctx.intern_tcon(nstr, &[]);
/// let t_manual = ctx.intern_tcon(ndict, &[tstr_manual, tint_manual]);
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// Make an arrow:
///
/// ```
/// # use polytype::{tp, with_ctx, Ty, Variable};
/// # with_ctx(32, |ctx| {
/// # ctx.intern_name("int");
/// let t_macro = tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1), tp!(ctx, 2)]);
/// assert_eq!(t_macro.to_string(), "t0 → t1 → t2");
/// // Equivalent to:
/// let t_0 = ctx.intern_tvar(Variable(0));
/// let t_1 = ctx.intern_tvar(Variable(1));
/// let t_2 = ctx.intern_tvar(Variable(2));
/// let t_manual = ctx.arrow_slice(&[t_0, t_1, t_2]);
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// Nest them for more complex types:
///
/// ```
/// # use polytype::{tp, with_ctx, Ty, Variable};
/// # with_ctx(32, |ctx| {
/// // mapi: (int → α → β) → [α] → [β]
/// let t = tp!(ctx, @arrow[
///     tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, 0), tp!(ctx, 1)]),
///     tp!(ctx, list(tp!(ctx, 0))),
///     tp!(ctx, list(tp!(ctx, 1))),
/// ]);
/// assert_eq!(t.to_string(), "(int → t0 → t1) → list(t0) → list(t1)");
/// # })
/// ```
///
/// [`Ty`]: type.Ty.html
#[macro_export]
macro_rules! tp {
    // name of context and name of type.
    ($ctx:ident, $n:ident) => {
        $ctx.intern_tcon($ctx.intern_name(stringify!($n)), &[])
    };
    // name of context, name of head, a comma-separated list of expressions
    ($ctx:ident, $n:ident($($x:expr),*)) => {
        $ctx.intern_tcon($ctx.intern_name(stringify!($n)), &[$($x),*])
    };
    // name of context, name of head,
    // TODO: is this necessary?
    ($ctx:ident, $n:ident($($x:expr,)*)) => ($crate::tp!($ctx, $n($($x),*)));
    // name of context, numerical value that is a variable value.
    ($ctx:ident, $n:expr) => ($ctx.intern_tvar($crate::Variable($n)));
    // Not sure why this is here...shouldn't be a valid type.
    // TODO: revise this to make sure arrows always have two?
    ($ctx:ident, @arrow[$x:expr]) => ($x);
    ($ctx:ident, @arrow[$x:expr, $($xs:expr),*]) => (
        match ($x, $crate::tp!($ctx, @arrow[$($xs),+])) {
            (arg, ret) => $ctx.arrow(arg, ret)
        }
    );
    // another rule matching
    ($ctx:ident, @arrow[$x:expr, $($xs:expr,)*]) => ($crate::tp!($ctx, @arrow[$x, $($xs),*]))
}

/// Creates a [`Schema`] (convenience for common patterns).
///
/// Specifically, a `&Schema<'ctx, &'static str>`, where all names are static strings.
///
/// ```rust,ignore
/// // Equivalent to:
/// &'ctx TypeSchema::Monotype(tp)
/// // Or
/// &'ctx TypeSchema::Polytype {
///     variable1,
///     body: Box::new(TypeSchema::Polytype {
///         variable2,
///         body: ...
///     })
/// }
/// ```
///
/// This behaves much like [`tp!`], but this gives a [`Schema`] and you can
/// express quantified type variables in a prefixed comma-delimited list. There
/// are three usage patterns, shown in the examples below.
///
/// # Examples
///
/// If you don't want to do any quantification, using `ptp!` on its own is just
/// like wrapping a [`Type`] with a [`TypeSchema::Monotype`]:
///
/// ```
/// # use polytype::{tp, ptp, with_ctx};
/// # with_ctx(32, |ctx| {
/// let t_macro = ptp!(ctx, dict(tp!(ctx, str), tp!(ctx, int)));
/// assert_eq!(t_macro.to_string(), "dict(str,int)");
/// // Equivalent to:
/// let nint = ctx.intern_name("int");
/// let nstr = ctx.intern_name("str");
/// let ndict = ctx.intern_name("dict");
/// let tint_manual = ctx.intern_tcon(nint, &[]);
/// let tstr_manual = ctx.intern_tcon(nstr, &[]);
/// let t_manual = ctx.intern_monotype(ctx.intern_tcon(ndict, &[tstr_manual, tint_manual]));
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// If you want to do quantification over a known monotype, precede the type
/// with quantified variables follows by a semicolon `;` (note that the
/// subsequent monotype is treated like the [`tp!`] macro):
///
/// ```
/// # use polytype::{tp, ptp, Variable, with_ctx};
/// # with_ctx(32, |ctx| {
/// # ctx.intern_name("int");
/// let t_macro = ptp!(ctx, 0, 1; @arrow[tp!(ctx, 0), tp!(ctx, 1), tp!(ctx, 0)]);
/// assert_eq!(t_macro.to_string(), "∀t0. ∀t1. t0 → t1 → t0");
/// // Equivalent to:
/// let t_0 = ctx.intern_tvar(Variable(0));
/// let t_1 = ctx.intern_tvar(Variable(1));
/// let t_arrow = ctx.arrow_slice(&[t_0, t_1, t_0]);
/// let t_manual = ctx.intern_polytype(
///     Variable(0),
///     ctx.intern_polytype(
///         Variable(1),
///         ctx.intern_monotype(t_arrow),
///     )
/// );
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// If you want want do quantification over an existing [`TypeSchema`], use a
/// comma after the quantified variables:
///
/// ```
/// # use polytype::{tp, ptp, Variable, with_ctx};
/// # with_ctx(32, |ctx| {
/// # ctx.intern_name("int");
/// let inner = ptp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1), tp!(ctx, 0)]);
/// let t_macro = ptp!(ctx, 0, 1, inner);
/// assert_eq!(t_macro.to_string(), "∀t0. ∀t1. t0 → t1 → t0");
/// // Equivalent to:
/// let t_manual = ctx.intern_polytype(
///     Variable(0),
///     ctx.intern_polytype(
///         Variable(1),
///         inner,
///     )
/// );
/// assert_eq!(t_macro, t_manual);
/// # })
/// ```
///
/// [`TypeSchema`]: enum.TypeSchema.html
/// [`TypeSchema::Polytype`]: enum.TypeSchema.html#variant.Polytype
/// [`TypeSchema::Monotype`]: enum.TypeSchema.html#variant.Monotype
/// [`Schema`]: type.Schema.html
/// [`Type`]: enum.Type.html
/// [`tp!`]: macro.tp.html
#[macro_export]
macro_rules! ptp {
    ($ctx:ident, $n:expr; $($t:tt)+) => {
        $ctx.intern_polytype($crate::Variable($n), $crate::ptp!($ctx, $($t)+))
    };
    ($ctx:ident, $n:expr, $body:expr) => {
        $ctx.intern_polytype($crate::Variable($n), $body)
    };
    ($ctx:ident, $n:expr, $($t:tt)+) => {
        $ctx.intern_polytype($crate::Variable($n), $crate::ptp!($ctx, $($t)+))
    };
    ($ctx:ident, $($t:tt)+) => {
        $ctx.intern_monotype($crate::tp!($ctx, $($t)+))
    };
}
