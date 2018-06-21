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
//! # #[macro_use] extern crate polytype;
//! use polytype::Context;
//!
//! # fn main() {
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
//! # }
//! ```
//!
//! Extended example:
//!
//! ```
//! # #[macro_use] extern crate polytype;
//! use polytype::Context;
//!
//! # fn main() {
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
//! # }
//! ```
//!
//! [`Context`]: struct.Context.html
//! [`Context::unify`]: struct.Context.html#method.unify
//! [`Type`]: enum.Type.html
//! [`TypeSchema::instantiate`]: enum.TypeSchema.html#method.instantiate
//! [`TypeSchema`]: enum.TypeSchema.html
//! [Hindley-Milner polymorphic typing system]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system

extern crate itertools;
#[macro_use]
extern crate nom;

#[macro_use]
mod macros;
mod context;
mod parser;
mod types;

pub use context::{Context, ContextChange, UnificationError};
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
    fn parse(&str) -> Result<Self, ()> {
        Err(())
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
        self.to_string()
    }
    /// **LEAKY** because it gives the string a static lifetime.
    #[inline(always)]
    fn parse(s: &str) -> Result<&'static str, ()> {
        Ok(unsafe { &mut *Box::into_raw(s.to_string().into_boxed_str()) })
    }
    /// The rightwards arrow in unicode: `→`.
    #[inline(always)]
    fn is_arrow(&self) -> bool {
        *self == "→"
    }
}
