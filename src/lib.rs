//! A [Hindley-Milner polymorphic typing system].
//!
//! For brevity, the documentation heavily uses the three provided macros when
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
//! assert_eq!(format!("{}", &t), "∀t0. (t0 → bool) → list(t0) → list(t0)");
//!
//! // We can instantiate type schemas to remove quantifiers
//! let mut ctx = Context::default();
//! let t = t.instantiate(&mut ctx);
//! assert_eq!(format!("{}", &t), "(t0 → bool) → list(t0) → list(t0)");
//!
//! // We can register a substiution for t0 in the context:
//! ctx.extend(0, tp!(int));
//! let t = t.apply(&ctx);
//! assert_eq!(format!("{}", &t), "(int → bool) → list(int) → list(int)");
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
//! assert_eq!(format!("{}", &t), "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//! // Let's consider reduce when applied to a function that adds two ints
//!
//! // First, we create a new typing context to manage typing bookkeeping.
//! let mut ctx = Context::default();
//!
//! // Let's create a type representing binary addition.
//! let tplus = tp!(@arrow[tp!(int), tp!(int), tp!(int)]);
//! assert_eq!(format!("{}", &tplus), "int → int → int");
//!
//! // We instantiate the type schema of reduce within our context
//! // so new type variables will be distinct
//! let t = t.instantiate(&mut ctx);
//! assert_eq!(format!("{}", &t), "(t1 → t0 → t1) → t1 → list(t0) → t1");
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
//! assert_eq!(format!("{}", &t), "(int → int → int) → int → list(int) → int");
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

use itertools::Itertools;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

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
pub enum TypeSchema {
    /// Non-polymorphic types (e.g. `α → β`, `int → bool`)
    Monotype(Type),
    /// Polymorphic types (e.g. `∀α. α → α`, `∀α. ∀β. α → β`)
    Polytype {
        /// The [`Variable`] being bound
        ///
        /// [`Variable`]: type.Variable.html
        variable: Variable,
        /// The type in which `variable` is bound
        body: Box<TypeSchema>,
    },
}
impl TypeSchema {
    /// Returns a set of each [`Variable`] bound by the [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = ptp!(0, 1; @arrow[tp!(1), tp!(2), tp!(3)]);
    /// assert_eq!(
    ///     t.bound_variables(),
    ///     vec![0, 1],
    /// );
    /// # }
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn bound_variables(&self) -> Vec<Variable> {
        let mut t = self;
        let mut bvs = Vec::new();
        while let TypeSchema::Polytype { variable, ref body } = *t {
            bvs.push(variable);
            t = body
        }
        bvs
    }
    pub fn is_bound(&self, v: Variable) -> bool {
        match *self {
            TypeSchema::Monotype(_) => false,
            TypeSchema::Polytype { variable, .. } if variable == v => true,
            TypeSchema::Polytype { ref body, .. } => body.is_bound(v),
        }
    }
    /// Returns a set of each free [`Variable`] in the [`TypeSchema`].
    ///
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn free_vars(&self, ctx: &Context) -> Vec<Variable> {
        let mut s = HashSet::new();
        self.free_vars_internal(ctx, &mut s);
        s.into_iter().collect()
    }
    pub fn free_vars_internal(&self, ctx: &Context, s: &mut HashSet<Variable>) {
        match *self {
            TypeSchema::Monotype(ref t) => t.free_vars_internal(ctx, s),
            TypeSchema::Polytype { variable, ref body } => {
                body.free_vars_internal(ctx, s);
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
    /// assert_eq!(format!("{}", &t1), "list(t0)");
    /// assert_eq!(format!("{}", &t2), "list(t1)");
    /// # }
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn instantiate(&self, ctx: &mut Context) -> Type {
        self.instantiate_internal(ctx, &mut HashMap::new())
    }
    fn instantiate_internal(
        &self,
        ctx: &mut Context,
        substitution: &mut HashMap<Variable, Type>,
    ) -> Type {
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
    pub fn instantiate_owned(self, ctx: &mut Context) -> Type {
        self.instantiate_owned_internal(ctx, &mut HashMap::new())
    }
    fn instantiate_owned_internal(
        self,
        ctx: &mut Context,
        substitution: &mut HashMap<Variable, Type>,
    ) -> Type {
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
    /// let t = TypeSchema::parse(s).expect("valid type");
    /// let round_trip = format!("{}", &t);
    /// assert_eq!(s, round_trip);
    /// # }
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn parse(s: &str) -> Result<TypeSchema, ()> {
        parser::parsep(s)
    }
}
impl fmt::Display for TypeSchema {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            TypeSchema::Polytype { variable, ref body } => write!(f, "∀t{}. {}", variable, body),
            TypeSchema::Monotype(ref t) => t.fmt(f),
        }
    }
}

/// Represents [monotypes][1] (fully instantiated, unquantified types).
///
/// The primary ways of creating a `Type` are with the [`tp!`] macro or with
/// [`TypeSchema::instantiate`].
///
/// [`tp!`]: macro.tp.html
/// [`TypeSchema::instantiate`]: enum.TypeSchema.html#method.instantiate
/// [1]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system#Monotypes
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    /// Primitive or composite types (e.g. `int`, `List(α)`, `α → β`)
    ///
    /// # Examples
    ///
    /// Primitives have no associated types:
    ///
    /// ```
    /// # use polytype::Type;
    /// let tint = Type::Constructed("int", vec![]);
    /// assert_eq!(format!("{}", &tint), "int")
    /// ```
    ///
    /// Composites have associated types:
    ///
    /// ```
    /// # use polytype::Type;
    /// let tint = Type::Constructed("int", vec![]);
    /// let tlist_of_ints = Type::Constructed("list", vec![tint]);
    /// assert_eq!(format!("{}", &tlist_of_ints), "list(int)");
    /// ```
    ///
    /// With the macros:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = tp!(list(tp!(int)));
    /// assert_eq!(format!("{}", &t), "list(int)");
    /// # }
    /// ```
    Constructed(&'static str, Vec<Type>),
    /// Type variables (e.g. `α`, `β`) identified by de Bruin indices.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Type;
    /// // any function: α → β
    /// let t = tp!(@arrow[Type::Variable(0), Type::Variable(1)]);
    /// assert_eq!(format!("{}", &t), "t0 → t1");
    /// # }
    /// ```
    ///
    /// With the macros:
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
    /// assert_eq!(format!("{}", &t), "(t0 → t1) → list(t0) → list(t1)");
    /// # }
    /// ```
    Variable(Variable),
}
impl Type {
    /// Construct a function type (i.e. `alpha` → `beta`).
    pub fn arrow(alpha: Type, beta: Type) -> Type {
        Type::Constructed("→", vec![alpha, beta])
    }
    /// If the type is an arrow, get its associated argument and return types.
    pub fn as_arrow(&self) -> Option<(&Type, &Type)> {
        if let Type::Constructed("→", ref args) = *self {
            Some((&args[0], &args[1]))
        } else {
            None
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
            Type::Constructed(name, ref args) => {
                if args.is_empty() {
                    String::from(name)
                } else if name == "→" {
                    Type::arrow_show(args, is_return)
                } else {
                    format!("{}({})", name, args.iter().map(|t| t.show(true)).join(","))
                }
            }
        }
    }
    /// Show specifically for arrow types
    fn arrow_show(args: &[Type], is_return: bool) -> String {
        if is_return {
            format!("{} → {}", args[0].show(false), args[1].show(true))
        } else {
            format!("({} → {})", args[0].show(false), args[1].show(true))
        }
    }
    /// If the type is an arrow, recursively get all curried function arguments.
    pub fn args(&self) -> Option<VecDeque<&Type>> {
        if let Type::Constructed("→", ref args) = *self {
            let mut tps = VecDeque::with_capacity(1);
            tps.push_back(&args[0]);
            let mut tp = &args[1];
            while let Type::Constructed("→", ref args) = *tp {
                tps.push_back(&args[0]);
                tp = &args[1];
            }
            Some(tps)
        } else {
            None
        }
    }
    /// If the type is an arrow, get its ultimate return type.
    pub fn returns(&self) -> Option<&Type> {
        if let Type::Constructed("→", ref args) = *self {
            let mut tp = &args[1];
            while let Type::Constructed("→", ref args) = *tp {
                tp = &args[1];
            }
            Some(tp)
        } else {
            None
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
    /// assert_eq!(format!("{}", &t), "list(t0)");
    /// let t = t.apply(&ctx);
    /// assert_eq!(format!("{}", &t), "list(int)");
    /// # }
    /// ```
    ///
    /// [`Context`]: struct.Context.html
    pub fn apply(&self, ctx: &Context) -> Type {
        match *self {
            Type::Constructed(name, ref args) => {
                let args = args.iter().map(|t| t.apply(ctx)).collect();
                Type::Constructed(name, args)
            }
            Type::Variable(v) => ctx.substitution
                .get(&v)
                .cloned()
                .unwrap_or_else(|| Type::Variable(v)),
        }
    }
    /// Like [`apply`], but works in-place.
    ///
    /// [`apply`]: #method.apply
    pub fn apply_mut(&mut self, ctx: &Context) {
        match *self {
            Type::Constructed(_, ref mut args) => for t in args {
                t.apply_mut(ctx)
            },
            Type::Variable(v) => {
                *self = ctx.substitution
                    .get(&v)
                    .cloned()
                    .unwrap_or_else(|| Type::Variable(v));
            }
        }
    }
    /// Generalizes the type by binding free variables in a [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, Type};
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(format!("{}", &t), "t0 → t1");
    ///
    /// let mut ctx = Context::default();
    /// ctx.extend(0, tp!(int));
    /// let t_gen = t.apply(&ctx).generalize(&ctx);
    ///
    /// assert_eq!(format!("{}", t_gen), "∀t1. int → t1");
    /// # }
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn generalize(&self, ctx: &Context) -> TypeSchema {
        let fvs = self.free_vars(ctx);
        let mut t = TypeSchema::Monotype(self.clone());
        for v in &fvs {
            t = TypeSchema::Polytype {
                variable: *v,
                body: Box::new(t),
            };
        }
        t
    }
    /// Compute all the free variables in a type.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, Type};
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(format!("{}", &t), "t0 → t1");
    ///
    /// let mut ctx = Context::default();
    /// ctx.extend(0, tp!(int));
    /// let fvs_computed = t.free_vars(&ctx);
    /// let fvs_expected = vec![1];
    ///
    /// assert_eq!(fvs_computed, fvs_expected);
    /// # }
    /// ```
    pub fn free_vars(&self, ctx: &Context) -> Vec<Variable> {
        let mut s = HashSet::new();
        self.free_vars_internal(ctx, &mut s);
        s.into_iter().collect()
    }
    pub fn free_vars_internal(&self, ctx: &Context, s: &mut HashSet<Variable>) {
        match *self {
            Type::Constructed(_, ref args) => for arg in args {
                arg.free_vars_internal(ctx, s);
            },
            Type::Variable(v) => {
                if !ctx.substitution.contains_key(&v) {
                    s.insert(v);
                }
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
    /// assert_eq!(format!("{}", &t), "t0 → t1");
    ///
    /// let mut substitution = HashMap::new();
    /// substitution.insert(0, tp!(int));
    /// substitution.insert(1, tp!(bool));
    /// let t = t.substitute(&substitution);
    ///
    /// assert_eq!(format!("{}", t), "int → bool");
    /// # }
    /// ```
    ///
    /// [`apply`]: #method.apply
    pub fn substitute(&self, substitution: &HashMap<Variable, Type>) -> Type {
        match *self {
            Type::Constructed(name, ref args) => {
                let args = args.iter().map(|t| t.substitute(substitution)).collect();
                Type::Constructed(name, args)
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
    pub fn substitute_mut(&mut self, substitution: &HashMap<Variable, Type>) {
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
    /// let t = Type::parse(s).expect("valid type");
    /// let round_trip = format!("{}", &t);
    /// assert_eq!(s, round_trip);
    /// # }
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    pub fn parse(s: &str) -> Result<Type, ()> {
        parser::parse(s)
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.show(true))
    }
}
impl From<VecDeque<Type>> for Type {
    fn from(mut tps: VecDeque<Type>) -> Type {
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
impl From<Vec<Type>> for Type {
    fn from(tps: Vec<Type>) -> Type {
        Type::from(VecDeque::from(tps))
    }
}

/// Errors during unification.
#[derive(Debug, Clone, PartialEq)]
pub enum UnificationError {
    /// `Occurs` happens when occurs checks fail (i.e. a type variable is
    /// unified recursively). The id of the bad type variable is supplied.
    Occurs(Variable),
    /// `Failure` happens when symbols or type variants don't unify because of
    /// structural differences.
    Failure(Type, Type),
}
impl fmt::Display for UnificationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            UnificationError::Occurs(v) => write!(f, "Occurs({})", v),
            UnificationError::Failure(ref t1, ref t2) => {
                write!(f, "Failure({}, {})", t1.show(false), t2.show(false))
            }
        }
    }
}
impl std::error::Error for UnificationError {
    fn description(&self) -> &str {
        "could not unify"
    }
}

/// A type environment. Useful for reasoning about [`Type`]s (e.g unification,
/// type inference).
///
/// Contexts track substitutions and generate fresh type variables.
///
/// [`Type`]: enum.Type.html
#[derive(Debug, Clone)]
pub struct Context {
    substitution: HashMap<Variable, Type>,
    next: Variable,
}
impl Default for Context {
    fn default() -> Self {
        Context {
            substitution: HashMap::new(),
            next: 0,
        }
    }
}
impl Context {
    /// The substitution managed by the context.
    pub fn substitution(&self) -> &HashMap<Variable, Type> {
        &self.substitution
    }
    /// Create a new substitution for [`Type::Variable`] number `v` to the
    /// [`Type`] `t`.
    ///
    /// [`Type`]: enum.Type.html
    /// [`Type::Variable`]: enum.Type.html#variant.Variable
    pub fn extend(&mut self, v: Variable, t: Type) {
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
    /// assert_eq!(format!("{}", t), "t1 → t2 → t2");
    ///
    /// // Get another fresh variable
    /// let t3 = ctx.new_variable();
    /// assert_eq!(t3, Type::Variable(3));
    /// # }
    /// ```
    ///
    /// [`Type::Variable`]: enum.Type.html#variant.Variable
    pub fn new_variable(&mut self) -> Type {
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
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnificationError> {
        let mut t1 = t1.clone();
        let mut t2 = t2.clone();
        t1.apply_mut(self);
        t2.apply_mut(self);
        let mut ctx = self.clone();
        ctx.unify_internal(t1, t2)?;
        *self = ctx;
        Ok(())
    }
    /// unify_internal may mutate the context even with an error. The context on
    /// which it's called should be discarded if there's an error.
    fn unify_internal(&mut self, t1: Type, t2: Type) -> Result<(), UnificationError> {
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
}

mod parser {
    use std::num::ParseIntError;
    use nom::types::CompleteStr;
    use nom::{alpha, digit};

    use super::{Type, TypeSchema};

    fn nom_u16(inp: CompleteStr) -> Result<u16, ParseIntError> {
        inp.0.parse()
    }

    named!(var<CompleteStr, Type>,
           do_parse!(tag!("t") >>
                     num: map_res!(digit, nom_u16) >>
                     (Type::Variable(num)))
    );
    named!(constructed_simple<CompleteStr, Type>,
           do_parse!(
               name: alpha >>
                   (Type::Constructed(leaky_str(name.0), vec![])))
    );
    named!(constructed_complex<CompleteStr, Type>,
           do_parse!(
               name: alpha >>
                   args: delimited!(
                       tag!("("),
                       separated_list!(tag!(","), ws!(monotype)),
                       tag!(")")
                   ) >>
                   (Type::Constructed(leaky_str(name.0), args)))
    );
    named!(arrow<CompleteStr, Type>,
           do_parse!(alpha: ws!(alt!(parenthetical |
                                     var |
                                     constructed_complex |
                                     constructed_simple)) >>
                     alt!(tag!("→") | tag!("->")) >>
                     beta: ws!(monotype) >>
                     (Type::arrow(alpha, beta)))
    );
    named!(parenthetical<CompleteStr, Type>,
           delimited!(tag!("("), arrow, tag!(")"))
    );
    named!(binding<CompleteStr, TypeSchema>,
           do_parse!(opt!(tag!("∀")) >>
                     tag!("t") >>
                     variable: map_res!(digit, nom_u16) >>
                     ws!(tag!(".")) >>
                     body: map!(polytype, Box::new) >>
                     (TypeSchema::Polytype{variable, body}))
    );
    named!(monotype<CompleteStr, Type>,
           alt!(arrow | var | constructed_complex | constructed_simple)
    );
    named!(polytype<CompleteStr, TypeSchema>,
           alt!(map!(monotype, TypeSchema::Monotype) | binding)
    );

    pub fn parse(input: &str) -> Result<Type, ()> {
        parsem(input)
    }
    pub fn parsem(input: &str) -> Result<Type, ()> {
        match monotype(CompleteStr(input)) {
            Ok((_, t)) => Ok(t),
            _ => Err(()),
        }
    }
    pub fn parsep(input: &str) -> Result<TypeSchema, ()> {
        match polytype(CompleteStr(input)) {
            Ok((_, t)) => Ok(t),
            _ => Err(()),
        }
    }

    fn leaky_str(s: &str) -> &'static str {
        unsafe { &mut *Box::into_raw(s.to_string().into_boxed_str()) }
    }
}
