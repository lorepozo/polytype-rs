//! A [Hindley-Milner polymorphic typing system].
//!
//! A [`TypeSchema`] is a type that may have universally quantified type
//! variables. You can use [`TypeSchema::instantiate`] to produce a
//! corresponding [`Type`], which is unquantified. Both can contain
//! [`Variable`]s, which are concrete but unknown types. [`Type::unify`] unifies
//! two [`Type`]s, recording constraints on [`Variable`]s in a [`Substitution`].
//! The [`Infer`] trait provides a simple interface for using these abilities to
//! support custom type inference and type checking algorithms. All types are
//! managed within a given [`TypeContext`], which interns type information for
//! faster inference. As a result, most user-facing access comes by way of
//! [`Schema`] and [`Ty`], references to interned [`TypeSchema`]s and [`Type`]s,
//! respectively.
//!
//! For brevity, the documentation heavily uses the two provided macros [`tp`]
//! and [`ptp`] when creating types.
//!
//! # Examples
//!
//! The basics:
//!
//! ```
//! use polytype::{ptp, tp, with_ctx, Context, Source, Substitution, Variable};
//!
//! // Types are defined with respect to a given TypeContext. Here, it's `ctx`.
//! with_ctx(32, |ctx| {
//!   // filter: ∀α. (α → bool) → [α] → [α]
//!   let t = ptp!(ctx, 0; @arrow[
//!       tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, bool)]),
//!       tp!(ctx, list(tp!(ctx, 0))),
//!       tp!(ctx, list(tp!(ctx, 0))),
//!   ]);
//!
//!   // Quantified type schemas provide polymorphic behavior.
//!   assert_eq!(t.to_string(), "∀t0. (t0 → bool) → list(t0) → list(t0)");
//!
//!   // We can instantiate type schemas to remove quantifiers
//!   let mut source = Source::default();
//!   let t = t.instantiate(&ctx, &mut source);
//!   assert_eq!(t.to_string(), "(t0 → bool) → list(t0) → list(t0)");
//!
//!   // We can register a substitution for t0 in the context:
//!   let mut sub = Substitution::with_capacity(ctx, 32);
//!   sub.add(Variable(0), tp!(ctx, int));
//!   let t = t.apply(&sub);
//!   assert_eq!(t.to_string(), "(int → bool) → list(int) → list(int)");
//! })
//! ```
//!
//! Extended example:
//!
//! ```
//! use polytype::{ptp, tp, with_ctx, Context, Source, Type};
//!
//! with_ctx(32, |ctx| {
//!     // reduce: ∀α. ∀β. (β → α → β) → β → [α] → β
//!     let t = ptp!(ctx, 0, 1; @arrow[
//!         tp!(ctx, @arrow[tp!(ctx, 1), tp!(ctx, 0), tp!(ctx, 1)]),
//!         tp!(ctx, 1),
//!         tp!(ctx, list(tp!(ctx, 0))),
//!         tp!(ctx, 1),
//!     ]);
//!     assert_eq!(t.to_string(), "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//!     // We also create a source of fresh type variables.
//!     let mut src = Source::default();
//!
//!     // Consider reduce when applied to a function that adds two `ints`.
//!
//!     // Let's create a type representing binary addition.
//!     let tint = tp!(ctx, int);
//!     let tplus = tp!(ctx, @arrow[tint, tint, tint]);
//!     assert_eq!(tplus.to_string(), "int → int → int");
//!
//!     // We instantiate the type schema of reduce within our context
//!     // so new type variables will be distinct
//!     let t = t.instantiate(&ctx, &mut src);
//!     assert_eq!(t.to_string(), "(t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//!     // By unifying, we can ensure function applications obey type requirements.
//!     let treturn = tp!(ctx, src.fresh());
//!     let targ1 = tp!(ctx, src.fresh());
//!     let targ2 = tp!(ctx, src.fresh());
//!     let sub = Type::unify(&[(
//!         t,
//!         tp!(ctx, @arrow[
//!             tplus,
//!             targ1,
//!             targ2,
//!             treturn,
//!         ])
//!     )], &ctx).expect("unifies");
//!
//!     // We can also now infer what arguments are needed and what gets returned
//!     assert_eq!(targ1.apply(&sub), tint);                  // inferred arg 1: int
//!     assert_eq!(targ2.apply(&sub), tp!(ctx, list(tint)));  // inferred arg 2: list(int)
//!     assert_eq!(treturn.apply(&sub), tint);                // inferred return: int
//!
//!     // Finally, we can see what form reduce takes by applying the new substitution
//!     let t = t.apply(&sub);
//!     assert_eq!(t.to_string(), "(int → int → int) → int → list(int) → int");
//! })
//! ```
//!
//! [`ptp`]: macro.ptp.html
//! [`tp`]: macro.tp.html
//! [`Infer`]: trait.Infer.html
//! [`Substitution`]: struct.Substitution.html
//! [`Type`]: enum.Type.html
//! [`Type::unify`]: enum.Type.html#method.unify
//! [`TypeContext`]: struct.TypeContext.html
//! [`TypeSchema::instantiate`]: enum.TypeSchema.html#method.instantiate
//! [`TypeSchema`]: enum.TypeSchema.html
//! [`Schema`]: type.Schema.html
//! [`Ty`]: type.Ty.html
//! [Hindley-Milner polymorphic typing system]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system

mod context;
mod macros;
mod parser;
mod source;
mod substitution;
mod types;

pub use context::{with_ctx, Context, TypeContext};
pub use source::{Source, SourceChange};
use std::hash::Hash;
pub use substitution::{Snapshot, Substitution};
pub use types::{Schema, Ty, Type, TypeSchema, UnificationError, Variable};

/// Types require a `Name` for comparison.
///
/// We mandate that [`arrow`] be implemented for any such names, and we provide an implementation
/// for `&'static str`.
///
/// # Examples
///
/// Using static strings:
///
/// ```
/// # use polytype::with_ctx;
/// with_ctx(32, |ctx| {
///     let tint = ctx.intern_tcon(ctx.intern_name("int"), &[]);
/// })
/// ```
///
/// A custom implementation:
///
/// ```
/// # use polytype::{with_ctx, Name};
/// #[derive(Clone, PartialEq, Eq, Hash)]
/// struct N(u8);
///
/// impl Name for N {
///     type ParseError = &'static str;
///     fn arrow() -> Self {
///         N(0)
///     }
///     fn parse(s: &str) -> Result<Self, Self::ParseError> {
///         s.parse::<u8>().map(|n| N(n)).or(Err("failed to parse Name"))
///     }
/// }
///
/// with_ctx(32, |ctx| {
///     let tint = ctx.intern_tcon(ctx.intern_name(N(1)), &[]);
/// })
/// ```
///
/// [`arrow`]: #tymethod.arrow
pub trait Name: Clone + Eq + Hash {
    /// A description of a failed `Name` parse.
    type ParseError;
    /// A specific name representing an arrow must be declared.
    fn arrow() -> Self;
    /// A way of displaying the name.
    fn show(&self) -> String {
        String::from("<unshowable type>")
    }
    /// To go from a particular name's string representation to a `Name`. This should round-trip
    /// with [`show`].
    ///
    /// [`show`]: #method.show
    fn parse(s: &str) -> Result<Self, Self::ParseError>;
    /// Returns `true` if the name represents an arrow, else `false`.
    fn is_arrow(&self) -> bool {
        *self == Self::arrow()
    }
}
impl Name for &'static str {
    type ParseError = &'static str;
    /// The rightwards arrow in unicode: `→`.
    #[inline(always)]
    fn arrow() -> &'static str {
        "→"
    }
    #[inline(always)]
    fn show(&self) -> String {
        (*self).to_string()
    }
    /// **LEAKY** because it gives the string a static lifetime.
    #[inline(always)]
    fn parse(s: &str) -> Result<&'static str, Self::ParseError> {
        Ok(unsafe { &mut *Box::into_raw(s.to_string().into_boxed_str()) })
    }
    /// Checks whether a name is the rightwards arrow in unicode: `→`.
    #[inline(always)]
    fn is_arrow(&self) -> bool {
        *self == "→"
    }
}

/// An interface for things that are typable.
///
/// # Examples
///
/// In the simplest case, you statically know what the type is:
///
/// ```
/// use polytype::{tp, with_ctx, Infer, Ty, TypeContext, UnificationError};
///
/// struct MyPrimitive;
/// impl<'ctx> Infer<'ctx, TypeContext<'ctx>> for MyPrimitive {
///     fn infer(&self, ctx: &TypeContext<'ctx>) -> Result<Ty<'ctx>, UnificationError<'ctx>> {
///         Ok(tp!(ctx, my_thing_tp))
///     }
/// }
///
/// with_ctx(32, |ctx| {
///     assert_eq!(MyPrimitive.infer(&ctx), Ok(tp!(ctx, my_thing_tp)));
/// })
/// ```
///
/// A more complex case builds a new type given typed items.
///
/// ```
/// use polytype::{
///     ptp, tp, with_ctx, Source, Substitution, Infer,
///     Ty, Type, TypeContext, Schema, UnificationError
/// };
/// use std::cell::RefCell;
///
/// // the RefCell allows us to mutate the context during inference
/// type MyCtx<'ctx> = RefCell<(Source, TypeContext<'ctx>)>;
///
/// struct Primitive<'ctx>(Schema<'ctx>);
/// impl<'ctx> Infer<'ctx, MyCtx<'ctx>> for Primitive<'ctx> {
///     fn infer(&self, ctx: &MyCtx<'ctx>) -> Result<Ty<'ctx>, UnificationError<'ctx>> {
///         let mut inner = ctx.borrow_mut();
///         let tctx = inner.1;
///         Ok(self.0.instantiate(&tctx, &mut inner.0))
///     }
/// }
///
/// struct Application<A, B> {
///     left: A,
///     right: B,
/// }
/// impl<'ctx, A, B> Infer<'ctx, MyCtx<'ctx>> for Application<A, B>
///   where
///     A: Infer<'ctx, MyCtx<'ctx>>,
///     B: Infer<'ctx, MyCtx<'ctx>>
/// {
///     fn infer(&self, ctx: &MyCtx<'ctx>) -> Result<Ty<'ctx>, UnificationError<'ctx>> {
///         let ft = self.left.infer(ctx)?;
///         let xt = self.right.infer(ctx)?;
///         let mut ctx = ctx.borrow_mut();
///         let tctx = ctx.1;
///         let ret = tp![tctx, ctx.0.fresh()];
///         let sub = Type::unify(&[(ft, tctx.arrow(xt, ret))], &tctx)?;
///         Ok(ret.apply(&sub))
///     }
/// }
///
/// with_ctx(32, |ctx| {
///     let f = Primitive(ptp!(ctx, @arrow[tp!(ctx, foo), tp!(ctx, bar)]));
///     let x = Primitive(ptp!(ctx, foo));
///     let fx = Application { left: f, right: x };
///     let c = RefCell::new((Source::default(), ctx));
///     assert_eq!(fx.infer(&c), Ok(tp!(ctx, bar)));
/// })
/// ```
///
/// A more sophisticated case has the types maintained externally:
///
/// ```
/// use polytype::{ptp, tp, with_ctx, Infer, Schema, Source, Substitution, Ty, Type, TypeContext, UnificationError, Variable};
/// use std::{cell::RefCell, collections::HashMap};
///
/// // in this example, every Term has a Type defined through the Lexicon
/// enum Term {
///     GlobalVariable(u32),
///     Application { op: u32, args: Vec<Term> },
/// }
/// struct Lexicon<'ctx> {
///     src: RefCell<Source>,
///     sub: RefCell<Substitution<'ctx>>,
///     ctx: TypeContext<'ctx>,
///     ops: HashMap<u32, Schema<'ctx>>,
///     global_vars: RefCell<HashMap<u32, Ty<'ctx>>>,
/// }
///
/// impl<'ctx> Infer<'ctx, Lexicon<'ctx>> for Term {
///     fn infer(&self, lex: &Lexicon<'ctx>) -> Result<Ty<'ctx>, UnificationError<'ctx>> {
///         match self {
///             Term::GlobalVariable(v) => Ok(lex
///                 .global_vars
///                 .borrow_mut()
///                 .entry(*v)
///                 .or_insert_with(|| lex.ctx.intern_tvar(Variable(lex.src.borrow_mut().fresh())))),
///             Term::Application { op, args } => {
///                 let mut arg_types: Vec<Ty> = args
///                     .into_iter()
///                     .map(|arg| arg.infer(lex))
///                     .collect::<Result<Vec<_>, _>>()?;
///                 let mut src = lex.src.borrow_mut();
///                 let ret = lex.ctx.intern_tvar(Variable(src.fresh()));
///                 arg_types.push(ret);
///                 let func_type = lex.ops[op].instantiate(&lex.ctx, &mut src);
///                 Type::unify_with_sub(&[(func_type, lex.ctx.arrow_slice(&arg_types))], &mut lex.sub.borrow_mut())?;
///                 Ok(ret.apply(&lex.sub.borrow()))
///             }
///         }
///     }
/// }
///
/// with_ctx(32, |ctx| {
///     let mut h = HashMap::new();
///     h.insert(0, ptp!(ctx, 0; @arrow[tp!(ctx, 0), tp!(ctx, foo)]));
///     h.insert(1, ptp!(ctx, @arrow[tp!(ctx, bar), tp!(ctx, baz)]));
///     let lex = Lexicon {
///         src: RefCell::new(Source::default()),
///         sub: RefCell::new(Substitution::with_capacity(ctx, 32)),
///         ops: h,
///         global_vars: RefCell::new(HashMap::new()),
///         ctx,
///     };
///     let term = Term::Application {
///         op: 0,
///         args: vec![Term::Application {
///             op: 1,
///             args: vec![Term::GlobalVariable(42)],
///         }],
///     };
///     assert_eq!(term.infer(&lex), Ok(tp!(ctx, foo)));
///     assert_eq!(
///         lex.global_vars
///             .borrow()
///             .get(&42)
///             .map(|t| t.apply(&lex.sub.borrow())),
///         Some(tp!(ctx, bar))
///     );
/// })
/// ```
pub trait Infer<'ctx, Context, E = UnificationError<'ctx>, N: Name = &'static str> {
    /// Given a context, return a principal typing or fail.
    fn infer(&self, ctx: &Context) -> Result<Ty<'ctx, N>, E>;
}
