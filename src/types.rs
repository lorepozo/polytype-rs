use itertools::Itertools;
use std::collections::{HashMap, VecDeque};
use std::fmt;

use crate::{Context, Name};

/// Represents a [type variable][1] (an unknown type).
///
/// [1]: https://en.wikipedia.org/wiki/Hindley–Milner_type_system#Free_type_variables
pub type Variable = usize;

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
    /// # use polytype::{ptp, tp};
    /// let t = ptp!(0; @arrow[tp!(0), tp!(1)]); // ∀α. α → β
    /// assert!(t.is_bound(0));
    /// assert!(!t.is_bound(1));
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
    /// # use polytype::{ptp, tp};
    /// let t = ptp!(0, 1; @arrow[tp!(1), tp!(2), tp!(3)]); // ∀α. ∀β. β → ɣ → δ
    /// assert_eq!(t.bound_vars(), vec![0, 1]);
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
    /// # use polytype::{ptp, tp};
    /// let t = ptp!(0, 1; @arrow[tp!(1), tp!(2), tp!(3)]); // ∀α. ∀β. β → ɣ → δ
    /// let mut free = t.free_vars();
    /// free.sort();
    /// assert_eq!(free, vec![2, 3]);
    /// ```
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn free_vars(&self) -> Vec<Variable> {
        let mut vars = vec![];
        self.free_vars_internal(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        vars
    }
    fn free_vars_internal(&self, vars: &mut Vec<Variable>) {
        match *self {
            TypeSchema::Monotype(ref t) => t.vars_internal(vars),
            TypeSchema::Polytype { variable, ref body } => {
                body.free_vars_internal(vars);
                *vars = vars.iter().filter(|&v| v != &variable).cloned().collect();
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
    /// # use polytype::{ptp, tp, Context};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = ptp!(3; list(tp!(3)));
    /// let t2 = ptp!(3; list(tp!(3)));
    ///
    /// let t1 = t1.instantiate(&mut ctx);
    /// let t2 = t2.instantiate(&mut ctx);
    /// assert_eq!(t1.to_string(), "list(t0)");
    /// assert_eq!(t2.to_string(), "list(t1)");
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
}
impl<N: Name> fmt::Display for TypeSchema<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    /// # use polytype::tp;
    /// let t = tp!(list(tp!(int)));
    /// assert_eq!(t.to_string(), "list(int)");
    /// ```
    ///
    /// Function types, or "arrows", are constructed with either [`Type::arrow`], two
    /// implementations of `Type::from` — one for [`Vec<Type>`] and one for [`VecDeque<Type>`] — or
    /// the macro:
    ///
    /// ```
    /// # use polytype::{tp, Type};
    /// let t = Type::arrow(tp!(int), tp!(bool));
    /// assert_eq!(t.to_string(), "int → bool");
    ///
    /// let t = Type::from(vec![tp!(int), tp!(int), tp!(bool)]);
    /// assert_eq!(t.to_string(), "int → int → bool");
    ///
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]); // prefer this over Type::from
    /// assert_eq!(t.to_string(), "int → int → bool");
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
    /// # use polytype::{tp, Type};
    /// // any function: α → β
    /// let t = tp!(@arrow[Type::Variable(0), Type::Variable(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    /// ```
    ///
    /// With the macro:
    ///
    /// ```
    /// # use polytype::tp;
    /// // map: (α → β) → [α] → [β]
    /// let t = tp!(@arrow[
    ///     tp!(@arrow[tp!(0), tp!(1)]),
    ///     tp!(list(tp!(0))),
    ///     tp!(list(tp!(1))),
    /// ]);
    /// assert_eq!(t.to_string(), "(t0 → t1) → list(t0) → list(t1)");
    /// ```
    Variable(Variable),
}
impl<N: Name> Type<N> {
    /// Construct a function type (i.e. `alpha` → `beta`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, Type};
    /// let t = Type::arrow(tp!(int), tp!(bool));
    /// assert_eq!(t.to_string(), "int → bool");
    /// ```
    pub fn arrow(alpha: Type<N>, beta: Type<N>) -> Type<N> {
        Type::Constructed(N::arrow(), vec![alpha, beta])
    }
    /// If the type is an arrow, get its associated argument and return types.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{ptp, tp};
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some((left, right)) = t.as_arrow() {
    ///     assert_eq!(left.to_string(), "int");
    ///     assert_eq!(right.to_string(), "int → bool");
    /// } else { unreachable!() }
    /// ```
    pub fn as_arrow(&self) -> Option<(&Type<N>, &Type<N>)> {
        match *self {
            Type::Constructed(ref n, ref args) if n.is_arrow() => Some((&args[0], &args[1])),
            _ => None,
        }
    }
    pub(crate) fn occurs(&self, v: Variable) -> bool {
        match *self {
            Type::Constructed(_, ref args) => args.iter().any(|t| t.occurs(v)),
            Type::Variable(n) => n == v,
        }
    }
    /// Supplying `is_return` helps arrows look cleaner.
    pub(crate) fn show(&self, is_return: bool) -> String {
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
    /// # use polytype::tp;
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some(args) = t.args() {
    ///     assert_eq!(args.len(), 2);
    ///     assert_eq!(args[0].to_string(), "int");
    ///     assert_eq!(args[1].to_string(), "int");
    /// } else { unreachable!() }
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
    /// If the type is an arrow, recursively get all curried function arguments.
    pub fn args_destruct(self) -> Option<Vec<Type<N>>> {
        match self {
            Type::Constructed(n, mut args) if n.is_arrow() => {
                let mut tps = Vec::with_capacity(1);
                let mut tp = args.pop().unwrap();
                tps.push(args.pop().unwrap());
                loop {
                    match tp {
                        Type::Constructed(n, mut args) if n.is_arrow() => {
                            tp = args.pop().unwrap();
                            tps.push(args.pop().unwrap());
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
    /// # use polytype::tp;
    /// let t = tp!(@arrow[tp!(int), tp!(int), tp!(bool)]);
    /// if let Some(ret) = t.returns() {
    ///     assert_eq!(ret.to_string(), "bool");
    /// } else { unreachable!() }
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
    /// # use polytype::{tp, Context};
    /// let mut ctx = Context::default();
    /// ctx.unify(&tp!(0), &tp!(int)).expect("unifies");
    ///
    /// let t = tp!(list(tp!(0)));
    /// assert_eq!(t.to_string(), "list(t0)");
    /// let t = t.apply(&ctx);
    /// assert_eq!(t.to_string(), "list(int)");
    /// ```
    ///
    /// [`Context`]: struct.Context.html
    pub fn apply(&self, ctx: &Context<N>) -> Type<N> {
        match *self {
            Type::Constructed(ref name, ref args) => {
                let args = args.iter().map(|t| t.apply(ctx)).collect();
                Type::Constructed(name.clone(), args)
            }
            Type::Variable(v) => {
                let maybe_tp = ctx
                    .path_compression_cache
                    .borrow()
                    .get(&v)
                    .or_else(|| ctx.substitution.get(&v))
                    .cloned();
                maybe_tp
                    .map(|mut tp| {
                        tp.apply_mut(ctx);
                        if ctx.path_compression_cache.borrow().get(&v) != Some(&tp) {
                            ctx.path_compression_cache
                                .borrow_mut()
                                .insert(v, tp.clone());
                        }
                        tp
                    })
                    .unwrap_or_else(|| self.clone())
            }
        }
    }
    /// Like [`apply_compress`], but works in-place.
    ///
    /// [`apply_compress`]: #method.apply_compress
    pub fn apply_mut(&mut self, ctx: &Context<N>) {
        match *self {
            Type::Constructed(_, ref mut args) => {
                for t in args {
                    t.apply_mut(ctx)
                }
            }
            Type::Variable(v) => {
                let maybe_tp = ctx
                    .path_compression_cache
                    .borrow()
                    .get(&v)
                    .or_else(|| ctx.substitution.get(&v))
                    .cloned();
                *self = maybe_tp
                    .map(|mut tp| {
                        tp.apply_mut(ctx);
                        ctx.path_compression_cache
                            .borrow_mut()
                            .insert(v, tp.clone());
                        tp
                    })
                    .unwrap_or_else(|| self.clone());
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
    /// # use polytype::{tp, Context};
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
    /// # use polytype::tp;
    /// let t = tp!(@arrow[tp!(0), tp!(1)]);
    /// assert_eq!(t.to_string(), "t0 → t1");
    ///
    /// let mut vars = t.vars();
    /// vars.sort();
    /// assert_eq!(vars, vec![0, 1]);
    /// ```
    pub fn vars(&self) -> Vec<Variable> {
        let mut vars = vec![];
        self.vars_internal(&mut vars);
        vars.sort_unstable();
        vars.dedup();
        vars
    }
    fn vars_internal(&self, vars: &mut Vec<Variable>) {
        match *self {
            Type::Constructed(_, ref args) => {
                for arg in args {
                    arg.vars_internal(vars);
                }
            }
            Type::Variable(v) => vars.push(v),
        }
    }
    /// Perform a substitution. This is analogous to [`apply`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::tp;
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
    /// ```
    ///
    /// [`apply`]: #method.apply
    pub fn substitute(&self, substitution: &HashMap<Variable, Type<N>>) -> Type<N> {
        match *self {
            Type::Constructed(ref name, ref args) => {
                let args = args.iter().map(|t| t.substitute(substitution)).collect();
                Type::Constructed(name.clone(), args)
            }
            Type::Variable(v) => substitution.get(&v).cloned().unwrap_or(Type::Variable(v)),
        }
    }
    /// Like [`substitute`], but works in-place.
    ///
    /// [`substitute`]: #method.substitute
    pub fn substitute_mut(&mut self, substitution: &HashMap<Variable, Type<N>>) {
        match *self {
            Type::Constructed(_, ref mut args) => {
                for t in args {
                    t.substitute_mut(substitution)
                }
            }
            Type::Variable(v) => {
                if let Some(t) = substitution.get(&v) {
                    *self = t.clone()
                }
            }
        }
    }
}
impl<N: Name> fmt::Display for Type<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
