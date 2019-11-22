use crate::{Name, Type, TypeSchema, Variable};
use indexmap::IndexMap;
use std::{collections::HashMap, error, fmt};

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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match *self {
            UnificationError::Occurs(v) => write!(f, "Occurs({})", v),
            UnificationError::Failure(ref t1, ref t2) => {
                write!(f, "Failure({}, {})", t1.show(false), t2.show(false))
            }
        }
    }
}
impl<N: Name + fmt::Debug> error::Error for UnificationError<N> {
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
    pub(crate) substitution: IndexMap<Variable, Type<N>>,
    pub(crate) cache: HashMap<Variable, Type<N>>,
    next: Variable,
}
impl<N: Name> Default for Context<N> {
    fn default() -> Self {
        Context {
            substitution: IndexMap::new(),
            cache: HashMap::new(),
            next: 0,
        }
    }
}
impl<N: Name> Context<N> {
    /// The substitution managed by the context.
    pub fn substitution(&self) -> &IndexMap<Variable, Type<N>> {
        &self.substitution
    }
    /// The number of constraints in the substitution.
    pub fn len(&self) -> usize {
        self.substitution.len()
    }
    /// `true` if the substitution has any constraints, else `false`.
    pub fn is_empty(&self) -> bool {
        self.substitution.is_empty()
    }
    /// Clears the substitution managed by the context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{Type, Context, ptp, tp};
    /// let mut ctx = Context::default();
    ///
    /// // Get a fresh variable
    /// let t0 = ctx.new_variable();
    /// let t1 = ctx.new_variable();
    ///
    /// let clean = ctx.clone();
    ///
    /// if let Type::Variable(N) = t0 {
    ///     ctx.extend(N, tp![t1]);
    ///     let dirty = ctx.clone();
    ///
    ///     ctx.clean();
    ///
    ///     assert_eq!(clean, ctx);
    ///     assert_ne!(clean, dirty);
    /// }
    /// ```
    pub fn clean(&mut self) {
        self.substitution.clear();
        self.cache = HashMap::new();
    }
    /// Removes all but `n` substitutions added to the `Context`.
    pub fn rollback(&mut self, n: usize) {
        self.cache = HashMap::new();
        if n == 0 {
            self.clean()
        } else {
            while n < self.substitution.len() {
                self.substitution.pop();
            }
        }
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
    /// # use polytype::{Type, Context, ptp, tp};
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
    /// # use polytype::{Context, tp};
    /// let mut ctx = Context::default();
    ///
    /// let t1 = tp!(@arrow[tp!(int), tp!(0)]);
    /// let t2 = tp!(@arrow[tp!(1), tp!(bool)]);
    /// ctx.unify(&t1, &t2).expect("unifies");
    ///
    /// let t1 = t1.apply(&ctx);
    /// let t2 = t2.apply(&ctx);
    /// assert_eq!(t1, t2);  // int → bool
    /// ```
    ///
    /// Unification errors leave the context unaffected. A
    /// [`UnificationError::Failure`] error happens when symbols don't match:
    ///
    /// ```
    /// # use polytype::{Context, UnificationError, tp};
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
    /// ```
    ///
    /// An [`UnificationError::Occurs`] error happens when the same type
    /// variable occurs in both types in a circular way. Ensure you
    /// [`instantiate`][] your types properly, so type variables don't overlap
    /// unless you mean them to.
    ///
    /// ```
    /// # use polytype::{Context, UnificationError, tp};
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
    /// ```
    ///
    /// [`UnificationError::Failure`]: enum.UnificationError.html#variant.Failure
    /// [`UnificationError::Occurs`]: enum.UnificationError.html#variant.Occurs
    /// [`instantiate`]: enum.Type.html#method.instantiate
    pub fn unify(&mut self, t1: &Type<N>, t2: &Type<N>) -> Result<(), UnificationError<N>> {
        let rollback_n = self.substitution.len();
        let t1 = t1.apply_compress(self);
        let t2 = t2.apply_compress(self);
        let result = self.unify_internal(t1, t2);
        if result.is_err() {
            self.rollback(rollback_n);
        }
        result
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
        t1.apply_mut_compress(self);
        t2.apply_mut_compress(self);
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
                    self.extend(v, t2);
                    Ok(())
                }
            }
            (t1, Type::Variable(v)) => {
                if t1.occurs(v) {
                    Err(UnificationError::Occurs(v))
                } else {
                    self.extend(v, t1);
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
                        t1.apply_mut_compress(self);
                        t2.apply_mut_compress(self);
                        self.unify_internal(t1, t2)?;
                    }
                    Ok(())
                }
            }
        }
    }
    /// Confines the substitution to those which act on the given variables.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{Context, tp};
    /// let mut ctx = Context::default();
    /// let v0 = ctx.new_variable();
    /// let v1 = ctx.new_variable();
    /// ctx.unify(&v0, &tp!(int));
    /// ctx.unify(&v1, &tp!(bool));
    ///
    /// {
    ///     let sub = ctx.substitution();
    ///     assert_eq!(sub.len(), 2);
    ///     assert_eq!(sub[&0], tp!(int));
    ///     assert_eq!(sub[&1], tp!(bool));
    /// }
    ///
    /// // confine the substitution to v1
    /// ctx.confine(&[1]);
    /// let sub = ctx.substitution();
    /// assert_eq!(sub.len(), 1);
    /// assert_eq!(sub[&1], tp!(bool));
    /// ```
    pub fn confine(&mut self, keep: &[Variable]) {
        let mut substitution = IndexMap::new();
        for v in keep {
            substitution.insert(*v, self.substitution[v].clone());
        }
        self.substitution = substitution;
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
    /// Without sacred variables, which assumes that all type variables between the contexts are
    /// distinct:
    ///
    /// ```
    /// # use polytype::{Type, Context, ptp, tp};
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
    /// ```
    ///
    /// With sacred variables, which specifies which type variables are equivalent in both
    /// contexts:
    ///
    /// ```
    /// # use polytype::{Type, Context, tp};
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
    /// // t1 from ctx2 is preserved *and* constrained by ctx
    /// let ctx_change = ctx.merge(ctx2, vec![1]);
    /// // rewrite all terms under ctx2 using ctx_change
    /// ctx_change.reify_type(&mut t);
    /// assert_eq!(t.to_string(), "t2 → t1");
    /// assert_eq!(t.apply(&ctx).to_string(), "bool → bool");
    ///
    /// assert_eq!(ctx.new_variable(), tp!(4));
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
        // this is intentionally wasting variable space when there are sacreds:
        self.next += other.next;
        ContextChange { delta, sacreds }
    }
}

/// Allow types to be reified for use in a different context. See [`Context::merge`].
///
/// [`Context::merge`]: struct.Context.html#method.merge
pub struct ContextChange {
    delta: usize,
    sacreds: Vec<Variable>,
}
impl ContextChange {
    /// Reify a [`Type`] for use under a merged [`Context`].
    ///
    /// [`Type`]: enum.Type.html
    /// [`Context`]: struct.Context.html
    pub fn reify_type(&self, tp: &mut Type) {
        match tp {
            Type::Constructed(_, args) => {
                for arg in args {
                    self.reify_type(arg)
                }
            }
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
