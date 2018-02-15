//! A Hindley-Milner polymorphic typing system.
//!
//! # Examples
//!
//! The basics:
//!
//! ```
//! // filter: (α → bool) → [α] → [α]
//! # #[macro_use] extern crate polytype;
//! use polytype::{Context, Type};
//!
//! # fn main() {
//! let t0 = Type::Variable(0);
//! let tbool = Type::Constructed("bool", vec![]);
//! fn tlist(tp: Type) -> Type {
//!     Type::Constructed("list", vec![Box::new(tp)])
//! }
//!
//! // the filter type
//! let t = arrow![
//!     arrow![t0.clone(), tbool],
//!     tlist(t0.clone()),
//!     tlist(t0.clone()),
//! ];
//!
//! assert!(t.is_polymorphic());
//! assert_eq!(format!("{}", &t),
//!            "(t0 → bool) → list(t0) → list(t0)");
//!
//! // we can substitute t0 using a type context:
//! let mut ctx = Context::default();
//!
//! let tint = Type::Constructed("int", vec![]);
//! ctx.unify(&t0, &tint).expect("unifies");
//!
//! let t = t.apply(&ctx);
//! assert!(!t.is_polymorphic());
//! assert_eq!(format!("{}", &t),
//!            "(int → bool) → list(int) → list(int)");
//! # }
//! ```
//!
//! More about instantiation, and unification:
//!
//! ```
//! // reduce: (β → α → β) → β → [α] → β
//! # #[macro_use] extern crate polytype;
//! use polytype::{Context, Type};
//!
//! # fn main() {
//! let t0 = Type::Variable(0);
//! let t1 = Type::Variable(1);
//! fn tlist(tp: Type) -> Type {
//!     Type::Constructed("list", vec![Box::new(tp)])
//! }
//!
//! // the reduce type
//! let t = arrow![
//!     arrow![
//!         t1.clone(),
//!         t0.clone(),
//!         t1.clone(),
//!     ],
//!     t1.clone(),
//!     tlist(t0.clone()),
//!     t1.clone(),
//! ];
//!
//! assert!(t.is_polymorphic());
//! assert_eq!(format!("{}", &t),
//!            "(t1 → t0 → t1) → t1 → list(t0) → t1");
//!
//! let tint = Type::Constructed("int", vec![]);
//! let tplus = arrow![tint.clone(), tint.clone(), tint.clone()];  // e.g. add two ints
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
//!         tint.clone(),
//!         tlist(tint.clone()),
//!         treturn.clone(),
//!     ],
//! ).expect("unifies");
//! assert_eq!(treturn.apply(&ctx), tint.clone());  // inferred return: int
//!
//! // now that unification has happened with ctx, we can see what form reduce takes
//! let t = t.apply(&ctx);
//! assert_eq!(format!("{}", t),
//!            "(int → int → int) → int → list(int) → int");
//! # }
//! ```
extern crate itertools;

use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::fmt;

/// Represents a type in the Hindley-Milner polymorphic typing system.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// For functions `α → β`.
    ///
    /// If a function has many arguments, use currying.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{Arrow, Type};
    /// let t = Type::Arrow(Arrow::new(Type::Variable(0), Type::Variable(1)));
    /// assert_eq!(format!("{}", &t),
    ///            "t0 → t1");
    /// ```
    ///
    /// With `arrow!` macro:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::Type;
    /// # fn main() {
    /// let t = arrow![
    ///     Type::Variable(0),
    ///     Type::Variable(1),
    ///     Type::Variable(2),
    ///     Type::Variable(3),
    /// ];
    /// assert_eq!(format!("{}", &t),
    ///            "t0 → t1 → t2 → t3");
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
    /// assert_eq!(format!("{}", &tlist_of_ints),
    ///            "list(int)");
    /// ```
    ///
    /// Composites may often warrant writing shorthand with a dedicated function:
    ///
    /// ```
    /// # use polytype::Type;
    /// fn tlist(tp: Type) -> Type {
    ///     Type::Constructed("list", vec![Box::new(tp)])
    /// }
    ///
    /// let tint = Type::Constructed("int", vec![]);
    /// let tlist_of_ints = tlist(tint);
    /// assert_eq!(format!("{}", &tlist_of_ints),
    ///            "list(int)");
    /// ```
    Constructed(&'static str, Vec<Box<Type>>),
    /// For type variables.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # use polytype::Type;
    /// # fn main() {
    /// // map: (α → β) → [α] → [β]
    /// let t0 = Type::Variable(0);
    /// let t1 = Type::Variable(1);
    /// fn tlist(tp: Type) -> Type {
    ///     Type::Constructed("list", vec![Box::new(tp)])
    /// }
    ///
    /// // the map type
    /// let t = arrow![
    ///     arrow![t0.clone(), t1.clone()],
    ///     tlist(t0.clone()),
    ///     tlist(t1.clone()),
    /// ];
    /// assert_eq!(format!("{}", &t),
    ///            "(t0 → t1) → list(t0) → list(t1)");
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
    /// # use polytype::{Context, Type};
    /// let mut ctx = Context::default();
    /// ctx.unify(&Type::Variable(0), &Type::Constructed("int", vec![])).expect("unifies");
    ///
    /// let t = Type::Constructed("list", vec![Box::new(Type::Variable(0))]);
    /// assert_eq!(format!("{}", &t), "list(t0)");
    /// let t = t.apply(&ctx);
    /// assert_eq!(format!("{}", &t), "list(int)");
    /// ```
    pub fn apply(&self, ctx: &Context) -> Type {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                let arg = arg.apply(ctx);
                let ret = ret.apply(ctx);
                Type::Arrow(Arrow::new(arg, ret))
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
    /// # use polytype::{Context, Type};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
    /// let t2 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
    ///
    /// let t1 = t1.instantiate_indep(&mut ctx);
    /// let t2 = t2.instantiate_indep(&mut ctx);
    /// assert_eq!(format!("{}", &t1), "list(t0)");
    /// assert_eq!(format!("{}", &t2), "list(t1)");
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
    /// # use polytype::{Context, Type};
    /// use std::collections::HashMap;
    ///
    /// let mut ctx = Context::default();
    ///
    /// let t1 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
    /// let t2 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
    ///
    /// let mut bindings = HashMap::new();
    /// let t1 = t1.instantiate(&mut ctx, &mut bindings);
    /// let t2 = t2.instantiate(&mut ctx, &mut bindings);
    /// assert_eq!(format!("{}", &t1), "list(t0)");
    /// assert_eq!(format!("{}", &t2), "list(t0)");
    /// ```
    pub fn instantiate(&self, ctx: &mut Context, bindings: &mut HashMap<u32, Type>) -> Type {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                if !self.is_polymorphic() {
                    self.clone()
                } else {
                    let arg = arg.instantiate(ctx, bindings);
                    let ret = ret.instantiate(ctx, bindings);
                    Arrow::new(arg, ret).into()
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

/// An arrow (function), curried.
///
/// # Examples
///
/// ```
/// use polytype::{Type, Arrow};
///
/// let arrow = Arrow::new(
///     Type::Variable(0),
///     Arrow::new(
///         Type::Variable(1),
///         Type::Variable(2),
///     ).into(),
/// );
///
/// assert_eq!(Vec::from(arrow.args()),
///            vec![&Type::Variable(0), &Type::Variable(1)]);
/// assert_eq!(arrow.returns(),
///            &Type::Variable(2));
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Arrow {
    pub arg: Box<Type>,
    pub ret: Box<Type>,
}
impl Arrow {
    pub fn new(arg: Type, ret: Type) -> Arrow {
        let arg = Box::new(arg);
        let ret = Box::new(ret);
        Arrow { arg, ret }
    }
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
    /// # use polytype::{Arrow, Context, Type};
    /// let mut ctx = Context::default();
    ///
    /// let tbool = Type::Constructed("bool", vec![]);
    /// let tint = Type::Constructed("int", vec![]);
    ///
    /// let t1 = arrow![tint, Type::Variable(0)];
    /// let t2 = arrow![Type::Variable(1), tbool];
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
    /// # use polytype::{Arrow, Context, Type, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let tbool = Type::Constructed("bool", vec![]);
    /// let tint = Type::Constructed("int", vec![]);
    ///
    /// let t1 = arrow![tint.clone(), Type::Variable(0)];
    /// let t2 = arrow![tbool.clone(), Type::Variable(1)];
    /// let res = ctx.unify(&t1, &t2);
    ///
    /// if let Err(UnificationError::Failure(left, right)) = res {
    ///     // failed to unify t1 with t2.
    ///     assert_eq!(left, tint);
    ///     assert_eq!(right, tbool);
    /// } else { unreachable!() }
    /// # }
    /// ```
    ///
    /// An [`UnificationError::Occurs`] error happens when the same type variable occurs in both
    /// types in a circular way:
    ///
    /// ```
    /// # #[macro_use] extern crate polytype;
    /// # fn main() {
    /// # use polytype::{Arrow, Context, Type, UnificationError};
    /// let mut ctx = Context::default();
    ///
    /// let tbool = Type::Constructed("bool", vec![]);
    ///
    /// let t1 = Type::Variable(1);
    /// let t2 = arrow![tbool, Type::Variable(1)];
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

/// Creates a [`Type::Arrow`] of `tp0 → tp1 → ...` (convenice for nested arrows).
///
/// This is equivalent to:
///
/// ```rust,ignore
/// Type::Arrow(Arrow::new(
///     tp0,
///     Arrow::new(
///         tp1,
///         Arrow::new(
///             tp2,
///             ...
///         ).into(),
///     ).into(),
/// ))
/// ```
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate polytype;
/// use polytype::Type;
/// # fn main() {
///
/// let t = arrow![Type::Variable(0), Type::Variable(1), Type::Variable(2)];
/// assert_eq!(format!("{}", t),
///            "t0 → t1 → t2");
/// # }
/// ```
///
/// [`Type::Arrow`]: enum.Type.html#variant.Arrow
#[macro_export]
macro_rules! arrow {
    [$x:expr] => ($x);
    [$x:expr, $($xs:expr),*] => (
        $crate::Type::Arrow($crate::Arrow::new($x, arrow!($($xs),+)))
    );
    [$x:expr, $($xs:expr,)*] => (
        arrow![$x, $($xs),*]
    )
}
