//! A Hindley-Milner polymorphic typing system.
//!
//! For brevity, the documentation heavily uses the two provided macros when creating types.
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
//! // filter: (α → bool) → [α] → [α]
//! let t = arrow![
//!     arrow![tp!(0), tp!(bool)],
//!     tp!(list(tp!(0))),
//!     tp!(list(tp!(0))),
//! ];
//!
//! assert!(t.is_polymorphic());
//! assert_eq!(format!("{}", &t), "(t0 → bool) → list(t0) → list(t0)");
//!
//! // we can substitute t0 with unification in a type context:
//! let mut ctx = Context::default();
//! ctx.unify(&tp!(0), &tp!(int)).expect("unifies");
//!
//! let t = t.apply(&ctx);
//! assert!(!t.is_polymorphic());
//! assert_eq!(format!("{}", &t), "(int → bool) → list(int) → list(int)");
//! # }
//! ```
//!
//! More about instantiation, and unification:
//!
//! ```
//! # #[macro_use] extern crate polytype;
//! use polytype::Context;
//!
//! # fn main() {
//! // reduce: (β → α → β) → β → [α] → β
//! let t = arrow![
//!     arrow![tp!(1), tp!(0), tp!(1)],
//!     tp!(1),
//!     tp!(list(tp!(0))),
//!     tp!(1),
//! ];
//!
//! assert!(t.is_polymorphic());
//! assert_eq!(format!("{}", &t), "(t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//! // lets consider reduce when applied to a function that adds two ints
//! let tplus = arrow![tp!(int), tp!(int), tp!(int)];
//! assert_eq!(format!("{}", &tplus), "int → int → int");
//!
//! // instantiate polymorphic types within our context so new type variables will be distinct
//! let mut ctx = Context::default();
//! let t = t.instantiate_indep(&mut ctx);
//!
//! // by unifying, we can ensure valid function application and infer what gets returned
//! let treturn = ctx.new_variable();
//! ctx.unify(
//!     &t,
//!     &arrow![
//!         tplus.clone(),
//!         tp!(int),
//!         tp!(list(tp!(int))),
//!         treturn.clone(),
//!     ],
//! ).expect("unifies");
//! assert_eq!(treturn.apply(&ctx), tp!(int));  // inferred return: int
//!
//! // now that unification has happened with ctx, we can see what form reduce takes
//! let t = t.apply(&ctx);
//! assert_eq!(format!("{}", t), "(int → int → int) → int → list(int) → int");
//! # }
//! ```

extern crate itertools;

#[macro_use]
mod macros;

use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::fmt;

/// Represents a type in the Hindley-Milner polymorphic typing system.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    /// For functions `α → β`.
    ///
    /// If a function has many arguments, use currying.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{Arrow, Type};
    /// let t = Type::Arrow(Arrow {
    ///     arg: Box::new(Type::Variable(0)),
    ///     ret: Box::new(Type::Variable(1)),
    /// });
    /// assert_eq!(format!("{}", &t), "t0 → t1");
    /// ```
    ///
    /// With the macros:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// let t = arrow![tp!(0), tp!(1), tp!(int), tp!(bool)];
    /// assert_eq!(format!("{}", &t), "t0 → t1 → int → bool");
    /// # }
    /// ```
    Arrow(Arrow),
    /// For primitive or composite types.
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
    /// let tlist_of_ints = Type::Constructed("list", vec![Box::new(tint)]);
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
    Constructed(&'static str, Vec<Box<Type>>),
    /// For type variables.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Type;
    /// // any function: α → β
    /// let t = arrow![Type::Variable(0), Type::Variable(1)];
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
    /// let t = arrow![
    ///     arrow![tp!(0), tp!(1)],
    ///     tp!(list(tp!(0))),
    ///     tp!(list(tp!(1))),
    /// ];
    /// assert_eq!(format!("{}", &t), "(t0 → t1) → list(t0) → list(t1)");
    /// # }
    /// ```
    Variable(u32),
}
impl Type {
    /// Whether a type has any type variables.
    pub fn is_polymorphic(&self) -> bool {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                arg.is_polymorphic() || ret.is_polymorphic()
            }
            &Type::Constructed(_, ref args) => args.iter().any(|t| t.is_polymorphic()),
            &Type::Variable(_) => true,
        }
    }
    fn occurs(&self, v: u32) -> bool {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => arg.occurs(v) || ret.occurs(v),
            &Type::Constructed(_, ref args) => args.iter().any(|t| t.occurs(v)),
            &Type::Variable(n) => n == v,
        }
    }
    /// Supplying is_return helps arrows look cleaner.
    fn show(&self, is_return: bool) -> String {
        match self {
            &Type::Arrow(ref arrow) => arrow.show(is_return),
            &Type::Constructed(name, ref args) => {
                if args.is_empty() {
                    String::from(name)
                } else {
                    format!("{}({})", name, args.iter().map(|t| t.show(true)).join(","))
                }
            }
            &Type::Variable(v) => format!("t{}", v),
        }
    }
    /// Applies the type in a context.
    ///
    /// This will replace any type variables that have substitutions defined in the context.
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
    pub fn apply(&self, ctx: &Context) -> Type {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                let arg = Box::new(arg.apply(ctx));
                let ret = Box::new(ret.apply(ctx));
                Type::Arrow(Arrow { arg, ret })
            }
            &Type::Constructed(ref name, ref args) => {
                let args = args.iter()
                    .map(|t| t.apply(ctx))
                    .map(|t| Box::new(t))
                    .collect();
                Type::Constructed(name, args)
            }
            &Type::Variable(v) => {
                if let Some(tp) = ctx.substitutions.get(&v) {
                    tp.apply(ctx)
                } else {
                    Type::Variable(v)
                }
            }
        }
    }
    /// Independently instantiates a type in the context.
    ///
    /// All type variables will be replaced with new type variables that the context has not seen.
    /// Equivalent to calling [`Type::instantiate`] with an empty map.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(list(tp!(3)));
    /// let t2 = tp!(list(tp!(3)));
    ///
    /// let t1 = t1.instantiate_indep(&mut ctx);
    /// let t2 = t2.instantiate_indep(&mut ctx);
    /// assert_eq!(format!("{}", &t1), "list(t0)");
    /// assert_eq!(format!("{}", &t2), "list(t1)");
    /// # }
    /// ```
    ///
    /// [`Type::instantiate`]: #method.instantiate
    pub fn instantiate_indep(&self, ctx: &mut Context) -> Type {
        self.instantiate(ctx, &mut HashMap::new())
    }
    /// Dependently instantiates a type in the context.
    ///
    /// All type variables will be replaced with new type variables that the context has not seen,
    /// unless specified by bindings. Mutates bindings for use with other instantiations, so their
    /// type variables are consistent with one another.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// use std::collections::HashMap;
    ///
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(list(tp!(3)));
    /// let t2 = tp!(list(tp!(3)));
    ///
    /// let mut bindings = HashMap::new();
    /// let t1 = t1.instantiate(&mut ctx, &mut bindings);
    /// let t2 = t2.instantiate(&mut ctx, &mut bindings);
    /// assert_eq!(format!("{}", &t1), "list(t0)");
    /// assert_eq!(format!("{}", &t2), "list(t0)");
    /// # }
    /// ```
    pub fn instantiate(&self, ctx: &mut Context, bindings: &mut HashMap<u32, Type>) -> Type {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                if !self.is_polymorphic() {
                    self.clone()
                } else {
                    let arg = Box::new(arg.instantiate(ctx, bindings));
                    let ret = Box::new(ret.instantiate(ctx, bindings));
                    Type::Arrow(Arrow { arg, ret })
                }
            }
            &Type::Constructed(name, ref args) => {
                if !self.is_polymorphic() {
                    self.clone()
                } else {
                    let args = args.iter()
                        .map(|t| t.instantiate(ctx, bindings))
                        .map(|t| Box::new(t))
                        .collect();
                    Type::Constructed(name, args)
                }
            }
            &Type::Variable(v) => bindings
                .entry(v)
                .or_insert_with(|| ctx.new_variable())
                .clone(),
        }
    }
    /// Canonicalizes the type by instantiating in an empty context.
    ///
    /// Replaces type variables according to bindings.
    pub fn canonical(&self, bindings: &mut HashMap<u32, Type>) -> Type {
        let mut ctx = Context::default();
        ctx.next = bindings.len() as u32;
        self.instantiate(&mut ctx, bindings)
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.show(true))
    }
}
impl From<Arrow> for Type {
    fn from(arrow: Arrow) -> Type {
        Type::Arrow(arrow)
    }
}
impl From<VecDeque<Type>> for Type {
    fn from(mut tps: VecDeque<Type>) -> Type {
        match tps.len() {
            0 => panic!("cannot create a type from nothing"),
            1 => tps.pop_front().unwrap(),
            2 => {
                let arg = Box::new(tps.pop_front().unwrap());
                let ret = Box::new(tps.pop_front().unwrap());
                Type::Arrow(Arrow { arg, ret })
            }
            _ => {
                let first_arg = tps.pop_front().unwrap();
                Type::Arrow(Arrow {
                    arg: Box::new(first_arg),
                    ret: Box::new(tps.into()),
                })
            }
        }
    }
}
impl From<Vec<Type>> for Type {
    fn from(tps: Vec<Type>) -> Type {
        Type::from(VecDeque::from(tps))
    }
}

/// A curried function.
///
/// # Examples
///
/// ```
/// use polytype::{Type, Arrow};
///
/// let func = Arrow{
///     arg: Box::new(Type::Variable(0)),
///     ret: Box::new(Type::Arrow(Arrow{
///         arg: Box::new(Type::Variable(1)),
///         ret: Box::new(Type::Variable(2)),
///     })),
/// };
///
/// assert_eq!(Vec::from(func.args()), vec![&Type::Variable(0), &Type::Variable(1)]);
/// assert_eq!(func.returns(), &Type::Variable(2));
/// ```
///
/// With the macros:
///
/// ```
/// # #[macro_use] extern crate polytype;
/// # fn main() {
/// # use polytype::Type;
/// let func = arrow![tp!(0), tp!(1), tp!(2)];
///
/// if let Type::Arrow(arr) = func {
///     assert_eq!(Vec::from(arr.args()), vec![&tp!(0), &tp!(1)]);
///     assert_eq!(arr.returns(), &tp!(2));
/// } else { unreachable!() } // we know func is an arrow
/// # }
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Arrow {
    pub arg: Box<Type>,
    pub ret: Box<Type>,
}
impl Arrow {
    /// Get all arguments to the function, recursing through curried functions.
    pub fn args(&self) -> VecDeque<&Type> {
        if let Type::Arrow(ref arrow) = *self.ret {
            let mut tps = arrow.args();
            tps.push_front(&self.arg);
            tps
        } else {
            let mut tps = VecDeque::new();
            tps.push_front(&*self.arg);
            tps
        }
    }
    /// Get the return type of the function, recursing through curried function returns.
    pub fn returns(&self) -> &Type {
        if let Type::Arrow(ref arrow) = *self.ret {
            arrow.returns()
        } else {
            &self.ret
        }
    }
    fn show(&self, is_return: bool) -> String {
        if is_return {
            format!("{} → {}", self.arg.show(false), self.ret.show(true))
        } else {
            format!("({} → {})", self.arg.show(false), self.ret.show(true))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnificationError {
    /// `Occurs` is the error when the same type variable occurs in both types in a circular way.
    /// The number of the circular type variable is supplied.
    Occurs(u32),
    /// `Failure` happens when symbols or type variants don't match.
    Failure(Type, Type),
}
impl fmt::Display for UnificationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            &UnificationError::Occurs(v) => write!(f, "Occurs({})", v),
            &UnificationError::Failure(ref t1, ref t2) => {
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

/// Context is a type environment, keeping track of substitutions and type variables. Useful for
/// _unifying_ (and inferring) types.
#[derive(Debug, Clone)]
pub struct Context {
    substitutions: HashMap<u32, Type>,
    next: u32,
}
impl Default for Context {
    fn default() -> Self {
        Context {
            substitutions: HashMap::new(),
            next: 0,
        }
    }
}
impl Context {
    pub fn substitutions(&self) -> &HashMap<u32, Type> {
        &self.substitutions
    }
    /// Create a new substitution for the type variable numbered `v` to the type `t`.
    pub fn extend(&mut self, v: u32, t: Type) {
        self.substitutions.insert(v, t);
    }
    /// Create a new [`Type::Variable`] from the next unused number.
    ///
    /// [`Type::Variable`]: enum.Type.html#variant.Variable
    pub fn new_variable(&mut self) -> Type {
        self.next = self.next + 1;
        Type::Variable(self.next - 1)
    }
    /// Create constraints within the context that ensure the two types unify.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::Context;
    /// let mut ctx = Context::default();
    ///
    /// let t1 = arrow![tp!(int), tp!(0)];
    /// let t2 = arrow![tp!(1), tp!(bool)];
    /// ctx.unify(&t1, &t2).expect("unifies");
    ///
    /// let t1 = t1.apply(&ctx);
    /// let t2 = t2.apply(&ctx);
    /// assert_eq!(t1, t2);
    /// # }
    /// ```
    ///
    /// Unification errors leave the context unaffected. A [`UnificationError::Failure`] error
    /// happens when symbols don't match:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = arrow![tp!(int), tp!(0)];
    /// let t2 = arrow![tp!(bool), tp!(1)];
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
    /// An [`UnificationError::Occurs`] error happens when the same type variable occurs in both
    /// types in a circular way. Ensure you [`instantiate`][] (or [`instantiate_indep`]) your types
    /// properly, so type variables don't overlap unless you mean them to.
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Context, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(1);
    /// let t2 = arrow![tp!(bool), tp!(1)];
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
    /// [`instantiate_indep`]: enum.Type.html#method.instantiate_indep
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnificationError> {
        let mut ctx = self.clone();
        ctx.unify_internal(t1, t2)?;
        *self = ctx;
        Ok(())
    }
    /// unify_internal may mutate the context even with an error.
    /// The context on which it's called should be discarded if there's an error.
    fn unify_internal(&mut self, t1: &Type, t2: &Type) -> Result<(), UnificationError> {
        let t1 = t1.apply(&self);
        let t2 = t2.apply(&self);
        if t1 == t2 {
            return Ok(());
        }
        if !t1.is_polymorphic() && !t2.is_polymorphic() {
            return Err(UnificationError::Failure(t1, t2));
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
            (Type::Arrow(a1), Type::Arrow(a2)) => {
                self.unify_internal(&a1.arg, &a2.arg)?;
                self.unify_internal(&a1.ret, &a2.ret)
            }
            (Type::Constructed(n1, a1), Type::Constructed(n2, a2)) => {
                if n1 != n2 {
                    Err(UnificationError::Failure(
                        Type::Constructed(n1, a1),
                        Type::Constructed(n2, a2),
                    ))
                } else {
                    for (t1, t2) in a1.into_iter().zip(a2) {
                        self.unify_internal(&t1, &t2)?;
                    }
                    Ok(())
                }
            }
            (t1, t2) => Err(UnificationError::Failure(t1, t2)),
        }
    }
}
