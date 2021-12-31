//! A [Hindley-Milner polymorphic typing system].
//!
//! For brevity, the documentation heavily uses the two provided macros when
//! creating types.
//!
//! A [`TypeSchema`] is a type that may have universally quantified type
//! variables. A [`Context`] keeps track of assignments made to type variables
//! so that you may manipulate [`Type`]s, which are unquantified and concrete.
//! Hence a `TypeSchema` can be instantiated, using [`TypeSchema::instantiate`],
//! into a `Context` in order to produce a corresponding `Type`. Two `Type`s
//! under a particular `Context` can be unified using [`Context::unify`], which
//! may record new type variable assignments in the `Context`.
//!
//! # Examples
//!
//! The basics:
//!
//! ```
//! use polytype::{ptp, tp, Context};
//!
//! // filter: ∀α. (α → bool) → [α] → [α]
//! let t = ptp!(0; @arrow[
//!     tp!(@arrow[tp!(0), tp!(bool)]),
//!     tp!(list(tp!(0))),
//!     tp!(list(tp!(0))),
//! ]);
//!
//! // Quantified type schemas provide polymorphic behavior.
//! assert_eq!(t.to_string(), "∀t0. (t0 → bool) → list(t0) → list(t0)");
//!
//! // We can instantiate type schemas to remove quantifiers
//! let mut ctx = Context::default();
//! let t = t.instantiate(&mut ctx);
//! assert_eq!(t.to_string(), "(t0 → bool) → list(t0) → list(t0)");
//!
//! // We can register a substitution for t0 in the context:
//! ctx.extend(0, tp!(int));
//! let t = t.apply(&ctx);
//! assert_eq!(t.to_string(), "(int → bool) → list(int) → list(int)");
//! ```
//!
//! Extended example:
//!
//! ```
//! use polytype::{ptp, tp, Context};
//!
//! // reduce: ∀α. ∀β. (β → α → β) → β → [α] → β
//! // We can represent the type schema of reduce using the included macros:
//! let t = ptp!(0, 1; @arrow[
//!     tp!(@arrow[tp!(1), tp!(0), tp!(1)]),
//!     tp!(1),
//!     tp!(list(tp!(0))),
//!     tp!(1),
//! ]);
//! assert_eq!(t.to_string(), "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//! // Let's consider reduce when applied to a function that adds two ints
//!
//! // First, we create a new typing context to manage typing bookkeeping.
//! let mut ctx = Context::default();
//!
//! // Let's create a type representing binary addition.
//! let tplus = tp!(@arrow[tp!(int), tp!(int), tp!(int)]);
//! assert_eq!(tplus.to_string(), "int → int → int");
//!
//! // We instantiate the type schema of reduce within our context
//! // so new type variables will be distinct
//! let t = t.instantiate(&mut ctx);
//! assert_eq!(t.to_string(), "(t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//! // By unifying, we can ensure function applications obey type requirements.
//! let treturn = ctx.new_variable();
//! let targ1 = ctx.new_variable();
//! let targ2 = ctx.new_variable();
//! ctx.unify(
//!     &t,
//!     &tp!(@arrow[
//!         tplus.clone(),
//!         targ1.clone(),
//!         targ2.clone(),
//!         treturn.clone(),
//!     ]),
//! ).expect("unifies");
//!
//! // We can also now infer what arguments are needed and what gets returned
//! assert_eq!(targ1.apply(&ctx), tp!(int));             // inferred arg 1: int
//! assert_eq!(targ2.apply(&ctx), tp!(list(tp!(int))));  // inferred arg 2: list(int)
//! assert_eq!(treturn.apply(&ctx), tp!(int));           // inferred return: int
//!
//! // Finally, we can see what form reduce takes by applying the new substitution
//! let t = t.apply(&ctx);
//! assert_eq!(t.to_string(), "(int → int → int) → int → list(int) → int");
//! ```
//!
//! [`Context`]: struct.Context.html
//! [`Context::unify`]: struct.Context.html#method.unify
//! [`Type`]: enum.Type.html
//! [`TypeSchema::instantiate`]: enum.TypeSchema.html#method.instantiate
//! [`TypeSchema`]: enum.TypeSchema.html
//! [Hindley-Milner polymorphic typing system]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system

mod context;
mod macros;
#[cfg(feature = "parser")]
mod parser;
mod types;

pub use context::{Context, ContextChange, UnificationError};
#[cfg(feature = "parser")]
pub use parser::ParseError;
pub use types::{Type, TypeSchema, Variable};

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
/// # use polytype::Type;
/// let t = Type::Constructed("int", vec![])
/// # ;
/// ```
///
/// A custom implementation:
///
/// ```
/// # use polytype::{Type, Name};
/// #[derive(Clone, PartialEq, Eq)]
/// struct N(u8);
///
/// impl Name for N {
///     fn arrow() -> Self {
///         N(0)
///     }
/// }
///
/// let t: Type<N> = Type::Constructed(N(1), vec![])
/// # ;
/// ```
///
/// [`arrow`]: #tymethod.arrow
pub trait Name: Clone + Eq {
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
    #[cfg(feature = "parser")]
    fn parse(_s: &str) -> Result<Self, ParseError> {
        Err(ParseError)
    }

    fn is_arrow(&self) -> bool {
        *self == Self::arrow()
    }
}
impl Name for &'static str {
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
    #[cfg(feature = "parser")]
    #[inline(always)]
    fn parse(s: &str) -> Result<&'static str, ParseError> {
        Ok(unsafe { &mut *Box::into_raw(s.to_string().into_boxed_str()) })
    }
    /// The rightwards arrow in unicode: `→`.
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
/// use polytype::{tp, Infer, Type, UnificationError};
///
/// struct MyPrimitive;
/// impl Infer<()> for MyPrimitive {
///     fn infer(&self, _ctx: &()) -> Result<Type, UnificationError> {
///         Ok(tp!(my_thing_tp))
///     }
/// }
///
/// assert_eq!(MyPrimitive.infer(&()), Ok(tp!(my_thing_tp)));
/// ```
///
/// A more complex case builds a new type given typed items.
///
/// ```
/// use polytype::{ptp, tp, Context, Infer, Type, TypeSchema, UnificationError};
/// use std::cell::RefCell;
///
/// type MyCtx = RefCell<Context>; // the RefCell allows us to mutate the context during inference
///
/// struct Primitive(TypeSchema);
/// impl Infer<MyCtx> for Primitive {
///     fn infer(&self, ctx: &MyCtx) -> Result<Type, UnificationError> {
///         Ok(self.0.instantiate(&mut ctx.borrow_mut()))
///     }
/// }
///
/// struct Application<A, B> {
///     left: A,
///     right: B,
/// }
/// impl<A: Infer<MyCtx>, B: Infer<MyCtx>> Infer<MyCtx> for Application<A, B> {
///     fn infer(&self, ctx: &MyCtx) -> Result<Type, UnificationError> {
///         let ft = self.left.infer(ctx)?;
///         let xt = self.right.infer(ctx)?;
///         let mut ctx = ctx.borrow_mut();
///         let ret = ctx.new_variable();
///         ctx.unify(&ft, &Type::arrow(xt, ret.clone()))?;
///         Ok(ret.apply(&ctx))
///     }
/// }
///
/// let f = Primitive(ptp!(@arrow[tp!(foo), tp!(bar)]));
/// let x = Primitive(ptp!(foo));
/// let fx = Application { left: f, right: x };
/// let ctx = RefCell::new(Context::default());
/// assert_eq!(fx.infer(&ctx), Ok(tp!(bar)));
/// ```
///
/// A more sophisticated case has the types maintained externally:
///
/// ```
/// use polytype::{ptp, tp, Context, Infer, Type, TypeSchema, UnificationError};
/// use std::{cell::RefCell, collections::HashMap};
///
/// // in this example, every Term has a Type defined through the Lexicon
/// enum Term {
///     GlobalVariable(u32),
///     Application { op: u32, args: Vec<Term> },
/// }
/// struct Lexicon {
///     ctx: RefCell<Context>,
///     ops: HashMap<u32, TypeSchema>,
///     global_vars: RefCell<HashMap<u32, Type>>,
/// }
///
/// impl Infer<Lexicon> for Term {
///     fn infer(&self, lex: &Lexicon) -> Result<Type, UnificationError> {
///         match self {
///             Term::GlobalVariable(v) => Ok(lex
///                 .global_vars
///                 .borrow_mut()
///                 .entry(*v)
///                 .or_insert_with(|| lex.ctx.borrow_mut().new_variable())
///                 .clone()),
///             Term::Application { op, args } => {
///                 let mut arg_types: Vec<Type> = args
///                     .into_iter()
///                     .map(|arg| arg.infer(lex))
///                     .collect::<Result<Vec<_>, _>>()?;
///                 let mut ctx = lex.ctx.borrow_mut();
///                 let ret = ctx.new_variable();
///                 arg_types.push(ret.clone());
///                 let func_type = lex.ops[op].instantiate(&mut ctx);
///                 ctx.unify(&func_type, &Type::from(arg_types))?;
///                 Ok(ret.apply(&ctx))
///             }
///         }
///     }
/// }
///
/// let mut h = HashMap::new();
/// h.insert(0, ptp!(0; @arrow[tp!(0), tp!(foo)]));
/// h.insert(1, ptp!(@arrow[tp!(bar), tp!(baz)]));
/// let lex = Lexicon {
///     ctx: RefCell::new(Context::default()),
///     ops: h,
///     global_vars: RefCell::new(HashMap::new()),
/// };
/// let term = Term::Application {
///     op: 0,
///     args: vec![Term::Application {
///         op: 1,
///         args: vec![Term::GlobalVariable(42)],
///     }],
/// };
/// assert_eq!(term.infer(&lex), Ok(tp!(foo)));
/// assert_eq!(
///     lex.global_vars
///         .borrow()
///         .get(&42)
///         .map(|t| t.apply(&lex.ctx.borrow())),
///     Some(tp!(bar))
/// );
/// ```
pub trait Infer<Context, E = UnificationError, N: Name = &'static str> {
    fn infer(&self, ctx: &Context) -> Result<Type<N>, E>;
}
