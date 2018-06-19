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
//! // We can register a substiution for t0 in the context:
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
mod parser;

use itertools::Itertools;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

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

/// Represents a [type variable][1] (an unknown type).
///
/// [1]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system#Free_type_variables
pub type Variable = u16;

/// Represents [polytypes][1] (uninstantiated, universally quantified types).
///
/// The primary ways of creating a `TypeSchema` are with the [`ptp!`] macro or
/// with [`Type::generalize`].
///
/// [1]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system#Polytype
/// [`ptp!`]: macro.ptp.html
/// [`Type::generalize`]: enum.Type.html#method.generalize
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TypeSchema<N: Name = &'static str> {
    /// Non-polymorphic types (e.g. `α → β`, `int → bool`)
    Monotype(Type<N>),
    /// Polymorphic types (e.g. `∀α. α → α`, `∀α. ∀β. α → β`)
    Polytype {
        /// The [`Variable`] being bound
        ///
        /// [`Variable`]: type.Variable.html
        variable: Variable,
        /// The type in which `variable` is bound
        body: Box<TypeSchema<N>>,
    },
}
impl<N: Name> TypeSchema<N> {
    /// Checks whether a variable is bound in the quantification of a polytype.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = ptp!(0; @arrow[tp!(0), tp!(1)]); // ∀α. α → β
    /// assert!(t.is_bound(0));
    /// assert!(!t.is_bound(1));
    /// # }
    /// ```
    pub fn is_bound(&self, v: Variable) -> bool {
        match *self {
            TypeSchema::Monotype(_) => false,
            TypeSchema::Polytype { variable, .. } if variable == v => true,
            TypeSchema::Polytype { ref body, .. } => body.is_bound(v),
        }
    }
    /// Returns a set of each [`Variable`] bound by the [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = ptp!(0, 1; @arrow[tp!(1), tp!(2), tp!(3)]); // ∀α. ∀β. β → ɣ → δ
    /// assert_eq!(t.bound_vars(), vec![0, 1]);
    /// # }
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn bound_vars(&self) -> Vec<Variable> {
        let mut t = self;
        let mut bvs = Vec::new();
        while let TypeSchema::Polytype { variable, ref body } = *t {
            bvs.push(variable);
            t = body
        }
        bvs
    }
    /// Returns a set of each free [`Variable`] in the [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = ptp!(0, 1; @arrow[tp!(1), tp!(2), tp!(3)]); // ∀α. ∀β. β → ɣ → δ
    /// let mut free = t.free_vars();
    /// free.sort();
    /// assert_eq!(free, vec![2, 3]);
    /// # }
    /// ```
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn free_vars(&self) -> Vec<Variable> {
        let mut s = HashSet::new();
        self.free_vars_internal(&mut s);
        s.into_iter().collect()
    }
    fn free_vars_internal(&self, s: &mut HashSet<Variable>) {
        match *self {
            TypeSchema::Monotype(ref t) => t.vars_internal(s),
            TypeSchema::Polytype { variable, ref body } => {
                body.free_vars_internal(s);
                s.remove(&variable);
            }
        }
    }
    /// Instantiate a [`TypeSchema`] in the context by removing quantifiers.
    ///
    /// All type variables will be replaced with fresh type variables.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// let mut ctx = Context::default();
    ///
    /// let t1 = ptp!(3; list(tp!(3)));
    /// let t2 = ptp!(3; list(tp!(3)));
    ///
    /// let t1 = t1.instantiate(&mut ctx);
    /// let t2 = t2.instantiate(&mut ctx);
    /// assert_eq!(t1.to_string(), "list(t0)");
    /// assert_eq!(t2.to_string(), "list(t1)");
    /// # }
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn instantiate(&self, ctx: &mut Context<N>) -> Type<N> {
        self.instantiate_internal(ctx, &mut HashMap::new())
    }
    fn instantiate_internal(
        &self,
        ctx: &mut Context<N>,
        substitution: &mut HashMap<Variable, Type<N>>,
    ) -> Type<N> {
        match *self {
            TypeSchema::Monotype(ref t) => t.substitute(substitution),
            TypeSchema::Polytype { variable, ref body } => {
                substitution.insert(variable, ctx.new_variable());
                body.instantiate_internal(ctx, substitution)
            }
        }
    }
    /// Like [`instantiate`], but works in-place.
    ///
    /// [`instantiate`]: #method.instantiate
    pub fn instantiate_owned(self, ctx: &mut Context<N>) -> Type<N> {
        self.instantiate_owned_internal(ctx, &mut HashMap::new())
    }
    fn instantiate_owned_internal(
        self,
        ctx: &mut Context<N>,
        substitution: &mut HashMap<Variable, Type<N>>,
    ) -> Type<N> {
        match self {
            TypeSchema::Monotype(mut t) => {
                t.substitute_mut(substitution);
                t
            }
            TypeSchema::Polytype { variable, body } => {
                substitution.insert(variable, ctx.new_variable());
                body.instantiate_owned_internal(ctx, substitution)
            }
        }
    }
    /// Parse a [`TypeSchema`] from a string. This round-trips with [`Display`].
    /// This is a **leaky** operation and should be avoided wherever possible:
    /// names of constructed types will remain until program termination.
    ///
    /// The "for-all" `∀` is optional.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::TypeSchema;
    /// let t_par = TypeSchema::parse("∀t0. t0 -> t0").expect("valid type");
    /// let t_lit = ptp!(0; @arrow[tp!(0), tp!(0)]);
    /// assert_eq!(t_par, t_lit);
    ///
    /// let s = "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1";
    /// let t: TypeSchema<&'static str> = TypeSchema::parse(s).expect("valid type");
    /// let round_trip = t.to_string();
    /// assert_eq!(s, round_trip);
    /// # }
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn parse(s: &str) -> Result<TypeSchema<N>, ()> {
        parser::parse_typeschema(s)
    }
}
impl<N: Name> fmt::Display for TypeSchema<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            TypeSchema::Polytype { variable, ref body } => write!(f, "∀t{}. {}", variable, body),
            TypeSchema::Monotype(ref t) => t.fmt(f),
        }
    }
}

/// Represents [monotypes][1] (fully instantiated, unquantified types).
///
/// The primary ways to create a `Type` are with either the [`tp!`] macro or
/// [`TypeSchema::instantiate`]. [`Type::arrow`] constructs function types (i.e.  `α → β`), as does
/// conversion (`Type::from`) with `Vec` and `VecDeque` for curried arrows.
///
/// [`tp!`]: macro.tp.html
/// [`TypeSchema::instantiate`]: enum.TypeSchema.html#method.instantiate
/// [`Type::arrow`]: enum.TypeSchema.html#method.instantiate
/// [1]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system#Monotypes
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type<N: Name = &'static str> {
    /// Primitive or composite types (e.g. `int`, `List(α)`, `α → β`)
    ///
    /// # Examples
    ///
    /// Primitives have no associated types:
    ///
    /// ```
    /// # use polytype::Type;
    /// let tint = Type::Constructed("int", vec![]);
    /// assert_eq!(tint.to_string(), "int")
    /// ```
    ///
    /// Composites have associated types:
    ///
    /// ```
    /// # use polytype::Type;
    /// let tint = Type::Constructed("int", vec![]);
    /// let tlist_of_ints = Type::Constructed("list", vec![tint]);
    /// assert_eq!(tlist_of_ints.to_string(), "list(int)");
    /// ```
    ///
    /// With the macro:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = tp!(list(tp!(int)));
    /// assert_eq!(t.to_string(), "list(int)");
    /// # }
    /// ```
    ///
    /// Function types, or "arrows", are constructed with either [`Type::arrow`], two
    /// implementations of `Type::from` — one for [`Vec<Type>`] and one for [`VecDeque<Type>`] — or
    /// the macro:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::Type;
    /// # fn main() {
    /// let t = Type::arrow(tp!(int), tp!(bool));
    /// assert_eq!(t.to_string(), "int → bool");
    ///
    /// let t = Type::from(vec![tp!(int), tp!(int), tp!(bool)]);
    /// assert_eq!(t.to_string(), "int → int → bool");
    ///
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]); // prefer this over Type::from
    /// assert_eq!(t.to_string(), "int → int → bool");
    /// # }
    /// ```
    ///
    /// [`Type::arrow`]: enum.Type.html#method.arrow
    /// [`Vec<Type>`]: enum.Type.html#impl-From<Vec<Type<N>>>
    /// [`VecDeque<Type>`]: enum.Type.html#impl-From<VecDeque<Type<N>>>
    Constructed(N, Vec<Type<N>>),
    /// Type variables (e.g. `α`, `β`).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Type;
    /// // any function: α → β
    /// let t = tp!(@arrow[Type::Variable(0), Type::Variable(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    /// # }
    /// ```
    ///
    /// With the macro:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// // map: (α → β) → [α] → [β]
    /// let t = tp!(@arrow[
    ///     tp!(@arrow[tp!(0), tp!(1)]),
    ///     tp!(list(tp!(0))),
    ///     tp!(list(tp!(1))),
    /// ]);
    /// assert_eq!(t.to_string(), "(t0 → t1) → list(t0) → list(t1)");
    /// # }
    /// ```
    Variable(Variable),
}
impl<N: Name> Type<N> {
    /// Construct a function type (i.e. `alpha` → `beta`).
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::Type;
    /// # fn main() {
    /// let t = Type::arrow(tp!(int), tp!(bool));
    /// assert_eq!(t.to_string(), "int → bool");
    /// # }
    /// ```
    pub fn arrow(alpha: Type<N>, beta: Type<N>) -> Type<N> {
        Type::Constructed(N::arrow(), vec![alpha, beta])
    }
    /// If the type is an arrow, get its associated argument and return types.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some((left, right)) = t.as_arrow() {
    ///     assert_eq!(left.to_string(), "int");
    ///     assert_eq!(right.to_string(), "int → bool");
    /// } else { unreachable!() }
    /// # }
    /// ```
    pub fn as_arrow(&self) -> Option<(&Type<N>, &Type<N>)> {
        match *self {
            Type::Constructed(ref n, ref args) if n.is_arrow() => Some((&args[0], &args[1])),
            _ => None,
        }
    }
    fn occurs(&self, v: Variable) -> bool {
        match *self {
            Type::Constructed(_, ref args) => args.iter().any(|t| t.occurs(v)),
            Type::Variable(n) => n == v,
        }
    }
    /// Supplying `is_return` helps arrows look cleaner.
    fn show(&self, is_return: bool) -> String {
        match *self {
            Type::Variable(v) => format!("t{}", v),
            Type::Constructed(ref name, ref args) => {
                if args.is_empty() {
                    name.show()
                } else if name.is_arrow() {
                    Type::arrow_show(args, is_return)
                } else {
                    format!(
                        "{}({})",
                        name.show(),
                        args.iter().map(|t| t.show(true)).join(",")
                    )
                }
            }
        }
    }
    /// Show specifically for arrow types
    fn arrow_show(args: &[Type<N>], is_return: bool) -> String {
        if is_return {
            format!("{} → {}", args[0].show(false), args[1].show(true))
        } else {
            format!("({} → {})", args[0].show(false), args[1].show(true))
        }
    }
    /// If the type is an arrow, recursively get all curried function arguments.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some(args) = t.args() {
    ///     assert_eq!(args.len(), 2);
    ///     assert_eq!(args[0].to_string(), "int");
    ///     assert_eq!(args[1].to_string(), "int");
    /// } else { unreachable!() }
    /// # }
    /// ```
    pub fn args(&self) -> Option<VecDeque<&Type<N>>> {
        match *self {
            Type::Constructed(ref n, ref args) if n.is_arrow() => {
                let mut tps = VecDeque::with_capacity(1);
                tps.push_back(&args[0]);
                let mut tp = &args[1];
                loop {
                    match *tp {
                        Type::Constructed(ref n, ref args) if n.is_arrow() => {
                            tps.push_back(&args[0]);
                            tp = &args[1];
                        }
                        _ => break,
                    }
                }
                Some(tps)
            }
            _ => None,
        }
    }
    /// If the type is an arrow, get its ultimate return type.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some(ret) = t.returns() {
    ///     assert_eq!(ret.to_string(), "bool");
    /// } else { unreachable!() }
    /// # }
    /// ```
    pub fn returns(&self) -> Option<&Type<N>> {
        match *self {
            Type::Constructed(ref n, ref args) if n.is_arrow() => {
                let mut tp = &args[1];
                loop {
                    match *tp {
                        Type::Constructed(ref n, ref args) if n.is_arrow() => {
                            tp = &args[1];
                        }
                        _ => break,
                    }
                }
                Some(tp)
            }
            _ => None,
        }
    }
    /// Applies the type in a [`Context`].
    ///
    /// This will substitute type variables for the values associated with them
    /// by the context.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// let mut ctx = Context::default();
    /// ctx.unify(&tp!(0), &tp!(int)).expect("unifies");
    ///
    /// let t = tp!(list(tp!(0)));
    /// assert_eq!(t.to_string(), "list(t0)");
    /// let t = t.apply(&ctx);
    /// assert_eq!(t.to_string(), "list(int)");
    /// # }
    /// ```
    ///
    /// [`Context`]: struct.Context.html
    pub fn apply(&self, ctx: &Context<N>) -> Type<N> {
        match *self {
            Type::Constructed(ref name, ref args) => {
                let args = args.iter().map(|t| t.apply(ctx)).collect();
                Type::Constructed(name.clone(), args)
            }
            Type::Variable(v) => ctx
                .substitution
                .get(&v)
                .cloned()
                .unwrap_or_else(|| Type::Variable(v)),
        }
    }
    /// Like [`apply`], but works in-place.
    ///
    /// [`apply`]: #method.apply
    pub fn apply_mut(&mut self, ctx: &Context<N>) {
        match *self {
            Type::Constructed(_, ref mut args) => for t in args {
                t.apply_mut(ctx)
            },
            Type::Variable(v) => {
                *self = ctx
                    .substitution
                    .get(&v)
                    .cloned()
                    .unwrap_or_else(|| Type::Variable(v));
            }
        }
    }
    /// Generalizes the type by quantifying over free variables in a [`TypeSchema`].
    ///
    /// Variables specified by `bound` remain unquantified.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, Type};
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    ///
    /// let mut ctx = Context::default();
    /// ctx.extend(0, tp!(int));
    ///
    /// let t_gen = t.apply(&ctx).generalize(&[]);
    /// assert_eq!(t_gen.to_string(), "∀t1. int → t1");
    ///
    /// let t_gen = t.apply(&ctx).generalize(&[1]);
    /// assert_eq!(t_gen.to_string(), "int → t1");
    /// # }
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn generalize(&self, bound: &[Variable]) -> TypeSchema<N> {
        let fvs = self
            .vars()
            .into_iter()
            .filter(|x| !bound.contains(x))
            .collect::<Vec<Variable>>();
        let mut t = TypeSchema::Monotype(self.clone());
        for v in fvs {
            t = TypeSchema::Polytype {
                variable: v,
                body: Box::new(t),
            };
        }
        t
    }
    /// Compute all the variables present in a type.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, Type};
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    ///
    /// let mut vars = t.vars();
    /// vars.sort();
    /// assert_eq!(vars, vec![0, 1]);
    /// # }
    /// ```
    pub fn vars(&self) -> Vec<Variable> {
        let mut s = HashSet::new();
        self.vars_internal(&mut s);
        s.into_iter().collect()
    }
    fn vars_internal(&self, s: &mut HashSet<Variable>) {
        match *self {
            Type::Constructed(_, ref args) => for arg in args {
                arg.vars_internal(s);
            },
            Type::Variable(v) => {
                s.insert(v);
            }
        }
    }
    /// Perform a substitution. This is analogous to [`apply`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Type;
    /// # use std::collections::HashMap;
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    ///
    /// let mut substitution = HashMap::new();
    /// substitution.insert(0, tp!(int));
    /// substitution.insert(1, tp!(bool));
    ///
    /// let t = t.substitute(&substitution);
    /// assert_eq!(t.to_string(), "int → bool");
    /// # }
    /// ```
    ///
    /// [`apply`]: #method.apply
    pub fn substitute(&self, substitution: &HashMap<Variable, Type<N>>) -> Type<N> {
        match *self {
            Type::Constructed(ref name, ref args) => {
                let args = args.iter().map(|t| t.substitute(substitution)).collect();
                Type::Constructed(name.clone(), args)
            }
            Type::Variable(v) => substitution
                .get(&v)
                .cloned()
                .unwrap_or_else(|| Type::Variable(v)),
        }
    }
    /// Like [`substitute`], but works in-place.
    ///
    /// [`substitute`]: #method.substitute
    pub fn substitute_mut(&mut self, substitution: &HashMap<Variable, Type<N>>) {
        match *self {
            Type::Constructed(_, ref mut args) => for t in args {
                t.substitute_mut(substitution)
            },
            Type::Variable(v) => {
                if let Some(t) = substitution.get(&v) {
                    *self = t.clone()
                }
            }
        }
    }
    /// Parse a type from a string. This round-trips with [`Display`]. This is a
    /// **leaky** operation and should be avoided wherever possible: names of
    /// constructed types will remain until program termination.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Type;
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
    /// # }
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    pub fn parse(s: &str) -> Result<Type<N>, ()> {
        parser::parse_type(s)
    }
}
impl<N: Name> fmt::Display for Type<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.show(true))
    }
}
impl<N: Name> From<VecDeque<Type<N>>> for Type<N> {
    fn from(mut tps: VecDeque<Type<N>>) -> Type<N> {
        match tps.len() {
            0 => panic!("cannot create a type from nothing"),
            1 => tps.pop_front().unwrap(),
            2 => {
                let alpha = tps.pop_front().unwrap();
                let beta = tps.pop_front().unwrap();
                Type::arrow(alpha, beta)
            }
            _ => {
                let alpha = tps.pop_front().unwrap();
                Type::arrow(alpha, tps.into())
            }
        }
    }
}
impl<N: Name> From<Vec<Type<N>>> for Type<N> {
    fn from(mut tps: Vec<Type<N>>) -> Type<N> {
        let mut beta = tps
            .pop()
            .unwrap_or_else(|| panic!("cannot create a type from nothing"));
        while let Some(alpha) = tps.pop() {
            beta = Type::arrow(alpha, beta)
        }
        beta
    }
}

/// Errors during unification.
#[derive(Debug, Clone, PartialEq)]
pub enum UnificationError<N: Name = &'static str> {
    /// `Occurs` happens when occurs checks fail (i.e. a type variable is
    /// unified recursively). The id of the bad type variable is supplied.
    Occurs(Variable),
    /// `Failure` happens when symbols or type variants don't unify because of
    /// structural differences.
    Failure(Type<N>, Type<N>),
}
impl<N: Name> fmt::Display for UnificationError<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            UnificationError::Occurs(v) => write!(f, "Occurs({})", v),
            UnificationError::Failure(ref t1, ref t2) => {
                write!(f, "Failure({}, {})", t1.show(false), t2.show(false))
            }
        }
    }
}
impl<N: Name + fmt::Debug> std::error::Error for UnificationError<N> {
    fn description(&self) -> &'static str {
        "unification failed"
    }
}

/// A type environment. Useful for reasoning about [`Type`]s (e.g unification,
/// type inference).
///
/// Contexts track substitutions and generate fresh type variables.
///
/// [`Type`]: enum.Type.html
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context<N: Name = &'static str> {
    substitution: HashMap<Variable, Type<N>>,
    next: Variable,
}
impl<N: Name> Default for Context<N> {
    fn default() -> Self {
        Context {
            substitution: HashMap::new(),
            next: 0,
        }
    }
}
impl<N: Name> Context<N> {
    /// The substitution managed by the context.
    pub fn substitution(&self) -> &HashMap<Variable, Type<N>> {
        &self.substitution
    }
    /// Reset the substitution to the empty substitution while leaving its ability to generate fresh [`Variable`]s intact.
    ///
    /// [`Variable`]: type.Variable.html
    pub fn reset(&mut self) {
        self.substitution = HashMap::new();
    }
    /// Create a new substitution for [`Type::Variable`] number `v` to the
    /// [`Type`] `t`.
    ///
    /// [`Type`]: enum.Type.html
    /// [`Type::Variable`]: enum.Type.html#variant.Variable
    pub fn extend(&mut self, v: Variable, t: Type<N>) {
        if v >= self.next {
            self.next = v + 1
        }
        self.substitution.insert(v, t);
    }
    /// Create a new [`Type::Variable`] from the next unused number.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Type, Context};
    /// let mut ctx = Context::default();
    ///
    /// // Get a fresh variable
    /// let t0 = ctx.new_variable();
    /// assert_eq!(t0, Type::Variable(0));
    ///
    /// // Instantiating a polytype will yield new variables
    /// let t = ptp!(0, 1; @arrow[tp!(0), tp!(1), tp!(1)]);
    /// let t = t.instantiate(&mut ctx);
    /// assert_eq!(t.to_string(), "t1 → t2 → t2");
    ///
    /// // Get another fresh variable
    /// let t3 = ctx.new_variable();
    /// assert_eq!(t3, Type::Variable(3));
    /// # }
    /// ```
    ///
    /// [`Type::Variable`]: enum.Type.html#variant.Variable
    pub fn new_variable(&mut self) -> Type<N> {
        self.next += 1;
        Type::Variable(self.next - 1)
    }
    /// Create constraints within the context that ensure `t1` and `t2`
    /// unify.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(@arrow[tp!(int), tp!(0)]);
    /// let t2 = tp!(@arrow[tp!(1), tp!(bool)]);
    /// ctx.unify(&t1, &t2).expect("unifies");
    ///
    /// let t1 = t1.apply(&ctx);
    /// let t2 = t2.apply(&ctx);
    /// assert_eq!(t1, t2);  // int → bool
    /// # }
    /// ```
    ///
    /// Unification errors leave the context unaffected. A
    /// [`UnificationError::Failure`] error happens when symbols don't match:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(@arrow[tp!(int), tp!(0)]);
    /// let t2 = tp!(@arrow[tp!(bool), tp!(1)]);
    /// let res = ctx.unify(&t1, &t2);
    ///
    /// if let Err(UnificationError::Failure(left, right)) = res {
    ///     // failed to unify t1 with t2.
    ///     assert_eq!(left, tp!(int));
    ///     assert_eq!(right, tp!(bool));
    /// } else { unreachable!() }
    /// # }
    /// ```
    ///
    /// An [`UnificationError::Occurs`] error happens when the same type
    /// variable occurs in both types in a circular way. Ensure you
    /// [`instantiate`][] your types properly, so type variables don't overlap
    /// unless you mean them to.
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(1);
    /// let t2 = tp!(@arrow[tp!(bool), tp!(1)]);
    /// let res = ctx.unify(&t1, &t2);
    ///
    /// if let Err(UnificationError::Occurs(v)) = res {
    ///     // failed to unify t1 with t2 because of circular type variable occurrence.
    ///     // t1 would have to be bool -> bool -> ... ad infinitum.
    ///     assert_eq!(v, 1);
    /// } else { unreachable!() }
    /// # }
    /// ```
    ///
    /// [`UnificationError::Failure`]: enum.UnificationError.html#variant.Failure
    /// [`UnificationError::Occurs`]: enum.UnificationError.html#variant.Occurs
    /// [`instantiate`]: enum.Type.html#method.instantiate
    pub fn unify(&mut self, t1: &Type<N>, t2: &Type<N>) -> Result<(), UnificationError<N>> {
        let mut t1 = t1.clone();
        let mut t2 = t2.clone();
        t1.apply_mut(self);
        t2.apply_mut(self);
        let mut ctx = self.clone();
        ctx.unify_internal(t1, t2)?;
        *self = ctx;
        Ok(())
    }
    /// Like [`unify`], but may affect the context even under failure. Hence, use this if you
    /// discard the context upon failure.
    ///
    /// [`unify`]: #method.unify
    pub fn unify_fast(
        &mut self,
        mut t1: Type<N>,
        mut t2: Type<N>,
    ) -> Result<(), UnificationError<N>> {
        t1.apply_mut(self);
        t2.apply_mut(self);
        self.unify_internal(t1, t2)
    }
    /// unify_internal may mutate the context even with an error. The context on
    /// which it's called should be discarded if there's an error.
    fn unify_internal(&mut self, t1: Type<N>, t2: Type<N>) -> Result<(), UnificationError<N>> {
        if t1 == t2 {
            return Ok(());
        }
        match (t1, t2) {
            (Type::Variable(v), t2) => {
                if t2.occurs(v) {
                    Err(UnificationError::Occurs(v))
                } else {
                    self.extend(v, t2.clone());
                    Ok(())
                }
            }
            (t1, Type::Variable(v)) => {
                if t1.occurs(v) {
                    Err(UnificationError::Occurs(v))
                } else {
                    self.extend(v, t1.clone());
                    Ok(())
                }
            }
            (Type::Constructed(n1, a1), Type::Constructed(n2, a2)) => {
                if n1 != n2 {
                    Err(UnificationError::Failure(
                        Type::Constructed(n1, a1),
                        Type::Constructed(n2, a2),
                    ))
                } else {
                    for (mut t1, mut t2) in a1.into_iter().zip(a2) {
                        t1.apply_mut(self);
                        t2.apply_mut(self);
                        self.unify_internal(t1, t2)?;
                    }
                    Ok(())
                }
            }
        }
    }
    /// Merge two type contexts.
    ///
    /// Every [`Type`] ([`TypeSchema`]) that corresponds to the `other` context
    /// must be reified using [`ContextChange::reify_type`]
    /// ([`ContextChange::reify_typeschema`]). Any [`Variable`] in `sacreds`
    /// will not be changed by the context (i.e. reification will ignore it).
    ///
    /// # Examples
    ///
    /// without sacred variables
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::{Type, Context};
    /// # fn main() {
    /// let mut ctx = Context::default();
    /// let a = ctx.new_variable();
    /// let b = ctx.new_variable();
    /// ctx.unify(&Type::arrow(a, b), &tp!(@arrow[tp!(int), tp!(bool)])).unwrap();
    /// // ctx uses t0 and t1
    ///
    /// let mut ctx2 = Context::default();
    /// let pt = ptp!(0, 1; @arrow[tp!(0), tp!(1)]);
    /// let mut t = pt.instantiate(&mut ctx2);
    /// ctx2.extend(0, tp!(bool));
    /// assert_eq!(t.apply(&ctx2).to_string(), "bool → t1");
    /// // ctx2 uses t0 and t1
    ///
    /// let ctx_change = ctx.merge(ctx2, vec![]);
    /// // rewrite all terms under ctx2 using ctx_change
    /// ctx_change.reify_type(&mut t);
    /// assert_eq!(t.to_string(), "t2 → t3");
    /// assert_eq!(t.apply(&ctx).to_string(), "bool → t3");
    ///
    /// assert_eq!(ctx.new_variable(), tp!(4));
    /// # }
    /// ```
    ///
    /// with sacred variables
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::{Type, Context};
    /// # fn main() {
    /// let mut ctx = Context::default();
    /// let a = ctx.new_variable();
    /// let b = ctx.new_variable();
    /// ctx.unify(&Type::arrow(a, b), &tp!(@arrow[tp!(int), tp!(bool)])).unwrap();
    /// // ctx uses t0 and t1
    ///
    /// let mut ctx2 = Context::default();
    /// let a = ctx2.new_variable();
    /// let b = ctx2.new_variable();
    /// let mut t = Type::arrow(a, b);
    /// ctx2.extend(0, tp!(bool));
    /// assert_eq!(t.apply(&ctx2).to_string(), "bool → t1");
    /// // ctx2 uses t0 and t1
    ///
    /// let ctx_change = ctx.merge(ctx2, vec![1]);
    /// // rewrite all terms under ctx2 using ctx_change
    /// ctx_change.reify_type(&mut t);
    /// // t1 from ctx2 is preserved *and* constrained by ctx
    /// assert_eq!(t.to_string(), "t2 → t1");
    /// assert_eq!(t.apply(&ctx).to_string(), "bool → bool");
    ///
    /// assert_eq!(ctx.new_variable(), tp!(4));
    /// # }
    /// ```
    /// [`ContextChange::reify_type`]: struct.ContextChange.html#method.reify_type
    /// [`ContextChange::reify_typeschema`]: struct.ContextChange.html#method.reify_typeschema
    /// [`Type`]: enum.Type.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    /// [`Variable`]: type.TypeSchema.html
    pub fn merge(&mut self, other: Context<N>, sacreds: Vec<Variable>) -> ContextChange {
        let delta = self.next;
        for (v, tp) in other.substitution {
            self.substitution.insert(delta + v, tp);
        }
        self.next += other.next;
        ContextChange { delta, sacreds }
    }
}

/// Allow types to be reified for use in a different context. See [`Context::merge`].
///
/// [`Context::merge`]: struct.Context.html#method.merge
pub struct ContextChange {
    delta: u16,
    sacreds: Vec<Variable>,
}
impl ContextChange {
    /// Reify a [`Type`] for use under a merged [`Context`].
    ///
    /// [`Type`]: enum.Type.html
    /// [`Context`]: struct.Context.html
    pub fn reify_type(&self, tp: &mut Type) {
        match tp {
            Type::Constructed(_, args) => for arg in args {
                self.reify_type(arg)
            },
            Type::Variable(n) if self.sacreds.contains(n) => (),
            Type::Variable(n) => *n += self.delta,
        }
    }
    /// Reify a [`TypeSchema`] for use under a merged [`Context`].
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    /// [`Context`]: struct.Context.html
    pub fn reify_typeschema(&self, tpsc: &mut TypeSchema) {
        match tpsc {
            TypeSchema::Monotype(tp) => self.reify_type(tp),
            TypeSchema::Polytype { variable, body } => {
                *variable += self.delta;
                self.reify_typeschema(body);
            }
        }
    }
}
