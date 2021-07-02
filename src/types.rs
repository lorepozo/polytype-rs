use crate::{
    parser::{parse_type, parse_typeschema, ParseError},
    Name, Source, Substitution, TypeContext,
};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};
use std::{error::Error, fmt};

/// The primary way [`Type`]s are handled. This is what a [`TypeContext`] returns when interning a [`Type`].
///
/// [`Type`]: enum.Type.html
/// [`TypeContext`]: struct.TypeContext.html
pub type Ty<'ctx, N = &'static str> = &'ctx Type<'ctx, N>;
/// The primary way [`TypeSchema`]s are handled. This is what a [`TypeContext`] returns when interning a [`TypeSchema`].
///
/// [`TypeSchema`]: enum.TypeSchema.html
/// [`TypeContext`]: struct.TypeContext.html
pub type Schema<'ctx, N = &'static str> = &'ctx TypeSchema<'ctx, N>;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// A type variable representing a definite but unknown type (e.g. `t0`).
pub struct Variable(pub usize);

/// Errors during unification.
#[derive(Debug, Clone, PartialEq)]
pub enum UnificationError<'ctx, N: Name = &'static str> {
    /// `Occurs` happens when occurs checks fail (i.e. a type variable is
    /// unified recursively). The id of the bad type variable is supplied.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, ptp, with_ctx, Type, UnificationError, Variable};
    /// with_ctx(10, |ctx| {
    ///     let t_1 = tp!(ctx, 0);
    ///     let t_2 = tp!(ctx, list(tp!(ctx, 0)));
    ///     assert_eq!(Type::unify(&[(t_1, t_2)], &ctx), Err(UnificationError::Occurs(Variable(0))));
    /// })
    /// ```
    Occurs(Variable),
    /// `Mismatch` happens when symbols or type variants don't unify because of
    /// structural differences.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, ptp, with_ctx, Type, UnificationError};
    /// with_ctx(10, |ctx| {
    ///     let t_1 = tp!(ctx, set(tp!(ctx, 0)));
    ///     let t_2 = tp!(ctx, list(tp!(ctx, 0)));
    ///     assert_eq!(Type::unify(&[(t_1, t_2)], &ctx), Err(UnificationError::Mismatch(t_1, t_2)));
    /// })
    /// ```
    Mismatch(Ty<'ctx, N>, Ty<'ctx, N>),
}
impl<'ctx, N: Name> fmt::Display for UnificationError<'ctx, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match *self {
            UnificationError::Occurs(v) => write!(f, "Occurs({})", v.0),
            UnificationError::Mismatch(ref t1, ref t2) => {
                write!(f, "Mismatch({}, {})", t1.show(false), t2.show(false))
            }
        }
    }
}
impl<'ctx, N: Name + fmt::Debug> Error for UnificationError<'ctx, N> {
    fn description(&self) -> &'static str {
        "unification failed"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A simple unquantified type.
pub enum Type<'ctx, N: Name = &'static str> {
    /// Primitive or composite types (e.g. `int`, `List(α)`, `α → β`)
    ///
    /// For some `Type::Constructed(head, args)`:
    /// - `head` is the type constructor.
    /// - `args` are the arguments to `head`.
    Constructed(&'ctx N, &'ctx [Ty<'ctx, N>]),
    /// Type variables (e.g. `α`, `β`).
    Variable(Variable),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// A potentially quantified (i.e. parametrically polymorphic) type.
pub enum TypeSchema<'ctx, N: Name = &'static str> {
    /// Non-polymorphic types (e.g. `α → β`, `int → bool`)
    Monotype(Ty<'ctx, N>),
    /// Polymorphic types (e.g. `∀α. α → α`, `∀α. ∀β. α → β`)
    ///
    /// For some `TypeSchema::Polytype(variable, body)`:
    /// - `variable` is the [`Variable`] being bound.
    /// - `body` is the type in which `variable` is bound.
    ///
    /// [`Variable`]: type.Variable.html
    Polytype(Variable, Schema<'ctx, N>),
}

impl<'ctx, N: Name> Type<'ctx, N> {
    /// If the type is an arrow, get its associated argument and return types.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext};
    /// with_ctx(10, |ctx| {
    ///     let t = tp!(ctx, @arrow[tp!(ctx, char), tp!(ctx, int), tp!(ctx, bool)]);
    ///     let (left, right) = t.as_arrow().expect("broken arrow");
    ///     assert_eq!(left.to_string(), "char");
    ///     assert_eq!(right.to_string(), "int → bool");
    /// })
    /// ```
    pub fn as_arrow(&self) -> Option<(Ty<'ctx, N>, Ty<'ctx, N>)> {
        match *self {
            Type::Constructed(ref n, ref args) if n.is_arrow() => Some((&args[0], &args[1])),
            _ => None,
        }
    }
    pub(crate) fn occurs(&self, v: Variable) -> bool {
        match *self {
            Type::Constructed(_, args) => args.iter().any(|t| t.occurs(v)),
            Type::Variable(n) => n == v,
        }
    }
    /// Supplying `is_return` helps arrows look cleaner.
    pub(crate) fn show(&self, is_return: bool) -> String {
        match *self {
            Type::Variable(v) => format!("t{}", v.0),
            Type::Constructed(name, args) => {
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
    fn arrow_show(args: &[Ty<'ctx, N>], is_return: bool) -> String {
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
    /// # use polytype::{tp, with_ctx, TypeContext};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = tp!(ctx, @arrow[tp!(ctx, char), tp!(ctx, int), tp!(ctx, bool)]);
    ///     let args = t.args().expect("arguments");
    ///     assert_eq!(args.len(), 2);
    ///     assert_eq!(args[0].to_string(), "char");
    ///     assert_eq!(args[1].to_string(), "int");
    /// })
    /// ```
    // TODO: convert Type::args to an iterator
    // TODO: convert TypeContext::intern_args to take an iterator
    pub fn args(&self) -> Option<Vec<Ty<'ctx, N>>> {
        match *self {
            Type::Constructed(n, args) if n.is_arrow() => {
                let mut tps: Vec<Ty<'ctx, N>> = Vec::with_capacity(10);
                tps.push(&args[0]);
                let mut tp = &args[1];
                loop {
                    match *tp {
                        Type::Constructed(n, args) if n.is_arrow() => {
                            tps.push(&args[0]);
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
    /// # use polytype::{tp, with_ctx, TypeContext};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = tp!(ctx, @arrow[tp!(ctx, char), tp!(ctx, int), tp!(ctx, bool)]);
    ///     let ret = t.returns().expect("return type");
    ///     assert_eq!(ret.to_string(), "bool");
    /// })
    /// ```
    pub fn returns(&self) -> Option<Ty<'ctx, N>> {
        match *self {
            Type::Constructed(n, args) if n.is_arrow() => {
                let mut tp = &args[1];
                loop {
                    match *tp {
                        Type::Constructed(n, args) if n.is_arrow() => {
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
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Type, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t_0 = tp!(ctx, 0);
    ///     let t_int = tp!(ctx, int);
    ///     let t_list_0 = tp!(ctx, list(t_0));
    ///
    ///     let sub = Type::unify(&[(t_0, t_int)], &ctx).expect("unifies");
    ///
    ///     assert_eq!(t_list_0.to_string(), "list(t0)");
    ///
    ///     let t_list_int = t_list_0.apply(&sub);
    ///     assert_eq!(t_list_int.to_string(), "list(int)");
    /// })
    /// ```
    ///
    /// [`Context`]: struct.Context.html
    // TODO: not sure if it's okay to assume this lifetime. I think so.
    pub fn apply(&'ctx self, sub: &Substitution<'ctx, N>) -> Ty<'ctx, N> {
        match *self {
            Type::Constructed(name, args) => {
                let naive_args = args.iter().map(|t| t.apply(sub)).collect_vec();
                if naive_args == args {
                    self
                } else {
                    sub.ctx.intern_tcon(name, &naive_args)
                }
            }
            Type::Variable(v) => sub.get(v).map(|tp| tp.apply(sub)).unwrap_or_else(|| self),
        }
    }
    /// Generalizes the type by quantifying over free variables in a [`TypeSchema`].
    ///
    /// Variables specified by `bound` remain unquantified.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Type, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t_int = tp!(ctx, int);
    ///     let t_0 = tp!(ctx, 0);
    ///     let t_1 = tp!(ctx, 1);
    ///     let t = tp!(ctx, @arrow[t_0, t_1]);
    ///
    ///     let mut sub = Substitution::with_capacity(ctx, 1);
    ///     sub.add(Variable(0), t_int);
    ///
    ///     let t_free = t.apply(&sub).generalize(&[], &ctx);
    ///     assert_eq!(t_free.to_string(), "∀t1. int → t1");
    ///
    ///     let t_bound = t.apply(&sub).generalize(&[Variable(1)], &ctx);
    ///     assert_eq!(t_bound.to_string(), "int → t1");
    /// })
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn generalize(
        &'ctx self,
        bound: &[Variable],
        ctx: &TypeContext<'ctx, N>,
    ) -> Schema<'ctx, N> {
        let fvs = self.vars().into_iter().filter(|x| !bound.contains(x));
        let mut t: Schema<'ctx, N> = ctx.intern_monotype(self);
        for v in fvs {
            t = ctx.intern_polytype(v, t);
        }
        t
    }
    /// Compute all the variables present in a type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, Substitution, TypeContext, Type, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t_0 = ctx.intern_tvar(Variable(0));
    ///     let t_1 = ctx.intern_tvar(Variable(1));
    ///     let t = ctx.arrow(t_0, t_1);
    ///
    ///     assert_eq!(t.to_string(), "t0 → t1");
    ///
    ///     let mut vars = t.vars();
    ///     vars.sort();
    ///     assert_eq!(vars, vec![Variable(0), Variable(1)]);
    /// })
    /// ```
    pub fn vars(&self) -> Vec<Variable> {
        let mut vars = vec![];
        self.vars_internal(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }
    fn vars_internal(&self, vars: &mut Vec<Variable>) {
        match *self {
            Type::Constructed(_, args) => {
                for arg in args {
                    arg.vars_internal(vars);
                }
            }
            Type::Variable(v) => vars.push(v),
        }
    }
    /// Parse a type from a string. This round-trips with [`Display`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, Type, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t_parse = Type::parse(&ctx, "int -> HashMap(t0, List(bool))").expect("valid type");
    ///
    ///     let n_int = ctx.intern_name("int");
    ///     let n_hash = ctx.intern_name("HashMap");
    ///     let n_list = ctx.intern_name("List");
    ///     let n_bool = ctx.intern_name("bool");
    ///     let t_int = ctx.intern_tcon(n_int, &[]);
    ///     let t_0 = ctx.intern_tvar(Variable(0));
    ///     let t_bool = ctx.intern_tcon(n_bool, &[]);
    ///     let t_list = ctx.intern_tcon(n_list, &[t_bool]);
    ///     let t_hash = ctx.intern_tcon(n_hash, &[t_0, t_list]);
    ///     let t_manual = ctx.arrow(t_int, t_hash);
    ///
    ///     assert_eq!(t_parse, t_manual);
    ///
    ///     let s = "(t1 → t0 → t1) → t1 → list(t0) → t1";
    ///     let t = Type::parse(&ctx, s).expect("valid type");
    ///     let round_trip = t.to_string();
    ///     assert_eq!(s, round_trip);
    /// })
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    pub fn parse(ctx: &TypeContext<'ctx, N>, s: &str) -> Result<Ty<'ctx, N>, ParseError> {
        parse_type(ctx, s)
    }
    /// Unify a set of constraints.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, Type};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t1 = Type::parse(&ctx, "int -> t0").expect("t1");
    ///     let t2 = Type::parse(&ctx, "t1 -> bool").expect("t2");
    ///     let sub = Type::unify(&[(t1, t2)], &ctx).expect("sub");
    ///
    ///     let t1 = t1.apply(&sub);
    ///     let t2 = t2.apply(&sub);
    ///     assert_eq!(t1, t2);
    ///     assert_eq!(t1.to_string(), "int → bool");
    /// })
    /// ```
    ///
    /// Unification errors leave the context unaffected. A
    /// [`UnificationError::Mismatch`] error happens when symbols don't match:
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, Type, UnificationError};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t1 = Type::parse(&ctx, "int -> t0").expect("t1");
    ///     let t2 = Type::parse(&ctx, "bool -> t1").expect("t2");
    ///     let res = Type::unify(&[(t1, t2)], &ctx);
    ///
    ///     if let Err(UnificationError::Mismatch(left, right)) = res {
    ///         assert_eq!(left.to_string(), "int");
    ///         assert_eq!(right.to_string(), "bool");
    ///     } else { unreachable!() }
    /// })
    /// ```
    ///
    /// An [`UnificationError::Occurs`] error happens when the same type
    /// variable occurs in both types in a circular way. Ensure you
    /// [`instantiate`][] your types properly, so type variables don't overlap
    /// unless you mean them to.
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, Type, UnificationError, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t1 = Type::parse(&ctx, "t0").expect("t1");
    ///     let t2 = Type::parse(&ctx, "bool -> t0").expect("t2");
    ///     let res = Type::unify(&[(t1, t2)], &ctx);
    ///
    ///     if let Err(UnificationError::Occurs(v)) = res {
    ///         assert_eq!(v, Variable(0));
    ///     } else { unreachable!() }
    /// })
    /// ```
    ///
    /// [`UnificationError::Mismatch`]: enum.UnificationError.html#variant.Mismatch
    /// [`UnificationError::Occurs`]: enum.UnificationError.html#variant.Occurs
    /// [`instantiate`]: enum.Type.html#method.instantiate
    pub fn unify(
        cs: &[(Ty<'ctx, N>, Ty<'ctx, N>)],
        ctx: &TypeContext<'ctx, N>,
    ) -> Result<Substitution<'ctx, N>, UnificationError<'ctx, N>> {
        let mut sub = Substitution::with_capacity(ctx.clone(), 32);
        Type::unify_with_sub(cs, &mut sub).map(|_| sub)
    }
    /// Unify a set of constraints subject to an existing `Substitution`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, Type, TypeContext, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t1 = Type::parse(&ctx, "t0 -> t1").expect("t1");
    ///     let t2 = Type::parse(&ctx, "t2 -> bool").expect("t2");
    ///     let tint = Type::parse(&ctx, "int").expect("tint");
    ///     let mut sub = Substitution::with_capacity(ctx, 10);
    ///     sub.add(Variable(0), tint);
    ///     Type::unify_with_sub(&[(t1, t2)], &mut sub).expect("success");
    ///
    ///     let t1 = t1.apply(&sub);
    ///     let t2 = t2.apply(&sub);
    ///     assert_eq!(t1, t2);
    ///     assert_eq!(t1.to_string(), "int → bool");
    /// })
    /// ```
    pub fn unify_with_sub(
        initial_cs: &[(Ty<'ctx, N>, Ty<'ctx, N>)],
        sub: &mut Substitution<'ctx, N>,
    ) -> Result<(), UnificationError<'ctx, N>> {
        let mut cs: SmallVec<[(&Type<N>, &Type<N>); 32]> = smallvec![];
        for &(s, t) in initial_cs {
            Type::unify_one(s, t, &mut cs, sub)?;
        }
        while let Some((s, t)) = cs.pop() {
            Type::unify_one(s, t, &mut cs, sub)?;
        }
        Ok(())
    }
    /// the internal implementation of a single unification.
    #[inline]
    fn unify_one(
        mut s: Ty<'ctx, N>,
        mut t: Ty<'ctx, N>,
        cs: &mut SmallVec<[(Ty<'ctx, N>, Ty<'ctx, N>); 32]>,
        subs: &mut Substitution<'ctx, N>,
    ) -> Result<(), UnificationError<'ctx, N>> {
        s = s.apply(subs);
        t = t.apply(subs);

        // if they are equal, you're all done with them.
        if s != t {
            match (s, t) {
                (Type::Variable(ref var), Type::Variable(_)) => {
                    subs.add(*var, t);
                }
                (Type::Variable(ref var), t) => {
                    if t.occurs(*var) {
                        return Err(UnificationError::Occurs(*var));
                    } else {
                        subs.add(*var, t);
                    }
                }
                (s, Type::Variable(ref var)) => {
                    if s.occurs(*var) {
                        return Err(UnificationError::Occurs(*var));
                    } else {
                        subs.add(*var, s);
                    }
                }
                (Type::Constructed(n1, a1), Type::Constructed(n2, a2)) => {
                    if n1 != n2 {
                        return Err(UnificationError::Mismatch(s, t));
                    } else {
                        for (&c1, &c2) in a1.iter().zip(a2.iter()) {
                            cs.push((c1, c2));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'ctx, N: Name> fmt::Display for Type<'ctx, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.show(true))
    }
}

impl<'ctx, N: Name> TypeSchema<'ctx, N> {
    /// Checks whether a variable is bound in the quantification of a polytype.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = TypeSchema::parse(&ctx, "t0. t0 -> t1").expect("t");
    ///     assert!(t.is_bound(Variable(0)));
    ///     assert!(!t.is_bound(Variable(1)));
    /// })
    /// ```
    pub fn is_bound(&self, v: Variable) -> bool {
        let mut t = self;
        while let TypeSchema::Polytype(variable, body) = t {
            if *variable == v {
                return true;
            } else {
                t = body
            }
        }
        false
    }
    /// Returns a set of each [`Variable`] bound by the [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = TypeSchema::parse(&ctx, "t0. t1. t1 -> t2 -> t3").expect("t");
    ///     assert_eq!(t.bound_vars(), vec![Variable(0), Variable(1)]);
    /// })
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn bound_vars(&self) -> Vec<Variable> {
        let mut t = self;
        let mut bvs = Vec::with_capacity(self.depth());
        while let TypeSchema::Polytype(variable, body) = *t {
            bvs.push(variable);
            t = body;
        }
        bvs
    }
    /// The number of [`Variable`]s bound by the `TypeSchema`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = TypeSchema::parse(&ctx, "t0. t1. t1 -> t2 -> t3").expect("t");
    ///     assert_eq!(t.depth(), 2);
    /// })
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    pub fn depth(&self) -> usize {
        let mut t = self;
        let mut depth = 0;
        while let TypeSchema::Polytype(_, body) = t {
            depth += 1;
            t = body;
        }
        depth
    }
    /// Returns a set of each free [`Variable`] in the [`TypeSchema`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t = TypeSchema::parse(&ctx, "t0. t1. t1 -> t2 -> t3").expect("t");
    ///     assert_eq!(t.free_vars(), vec![Variable(2), Variable(3)]);
    /// })
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn free_vars(&self) -> Vec<Variable> {
        let mut vars = vec![];
        self.free_vars_internal(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }
    fn free_vars_internal(&self, vars: &mut Vec<Variable>) {
        match *self {
            TypeSchema::Monotype(t) => t.vars_internal(vars),
            TypeSchema::Polytype(variable, body) => {
                body.free_vars_internal(vars);
                *vars = vars.iter().filter(|&v| v != &variable).copied().collect();
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
    /// # use polytype::{with_ctx, Source, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let mut src = Source::default();
    ///     src.fresh(); // Throw away a type variable to match parse.
    ///     let t = TypeSchema::parse(&ctx, "t1. t1 -> t0").expect("t");
    ///     let t_in1 = t.instantiate(&ctx, &mut src);
    ///     let t_in2 = t.instantiate(&ctx, &mut src);
    ///     assert_eq!(t_in1.to_string(), "t1 → t0");
    ///     assert_eq!(t_in2.to_string(), "t2 → t0");
    /// })
    /// ```
    ///
    /// ```
    /// # use polytype::{with_ctx, Source, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let mut src = Source::default();
    ///     let t = TypeSchema::parse(&ctx, "t0. t1. (t0 -> t1) -> t0 -> t1").expect("t");
    ///     let t_in1 = t.instantiate(&ctx, &mut src);
    ///     let t_in2 = t.instantiate(&ctx, &mut src);
    ///     assert_eq!(t_in1.to_string(), "(t0 → t1) → t0 → t1");
    ///     assert_eq!(t_in2.to_string(), "(t2 → t3) → t2 → t3");
    /// })
    /// ```
    ///
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn instantiate(&self, ctx: &TypeContext<'ctx, N>, src: &mut Source) -> Ty<'ctx, N> {
        let mut sub = Substitution::with_capacity(ctx.clone(), self.depth());
        let mut tp = self;
        loop {
            match tp {
                TypeSchema::Polytype(variable, body) => {
                    let t_var = Variable(src.fresh());
                    let t = ctx.intern_tvar(t_var);
                    if *variable != t_var {
                        sub.add(*variable, t);
                    }
                    tp = body;
                }
                TypeSchema::Monotype(t) => return TypeSchema::substitute(t, &sub),
            }
        }
    }
    // A helper function used by `instantiate`.
    fn substitute(tp: Ty<'ctx, N>, sub: &Substitution<'ctx, N>) -> Ty<'ctx, N> {
        match *tp {
            Type::Constructed(name, args) => {
                let naive_args = args
                    .iter()
                    .map(|t| TypeSchema::substitute(t, sub))
                    .collect_vec();
                sub.ctx.intern_tcon(name, &naive_args)
            }
            // Major difference is here: we don't call substitute recursively.
            Type::Variable(v) => sub.get(v).unwrap_or(tp),
        }
    }
    /// Parse a [`TypeSchema`] from a string. This round-trips with [`Display`].
    ///
    /// The "for-all" `∀` is optional.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, TypeSchema, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let t_parse = TypeSchema::parse(&ctx, "∀t0. t0 -> t0").expect("t_parse");
    ///
    ///     let t_0 = ctx.intern_tvar(Variable(0));
    ///     let t_arrow = ctx.arrow(t_0, t_0);
    ///     let t_mono = ctx.intern_monotype(t_arrow);
    ///     let t_manual = ctx.intern_polytype(Variable(0), t_mono);
    ///
    ///     assert_eq!(t_parse, t_manual);
    ///
    ///     let s = "∀t0. ∀t1. (t1 → t0 → t1) → t1 → list(t0) → t1";
    ///     let t = TypeSchema::parse(&ctx, s).expect("t");
    ///     let round_trip = t.to_string();
    ///     assert_eq!(s, round_trip);
    /// })
    /// ```
    ///
    /// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
    /// [`TypeSchema`]: enum.TypeSchema.html
    pub fn parse(ctx: &TypeContext<'ctx, N>, s: &str) -> Result<Schema<'ctx, N>, ParseError> {
        parse_typeschema(ctx, s)
    }
}

impl<'ctx, N: Name> fmt::Display for TypeSchema<'ctx, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match *self {
            TypeSchema::Polytype(variable, body) => write!(f, "∀t{}. {}", variable.0, body),
            TypeSchema::Monotype(ref t) => t.fmt(f),
        }
    }
}
