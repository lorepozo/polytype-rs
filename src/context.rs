use crate::{Name, Schema, Ty, Type, TypeSchema, Variable};
use fnv::FnvHashMap;
use itertools::Itertools;
use std::{
    borrow::Borrow,
    cell::RefCell,
    hash::{Hash, Hasher},
};
use typed_arena::Arena;

struct Interner<'a, K>(RefCell<FnvHashMap<&'a K, ()>>);

struct SliceInterner<'a, K>(RefCell<FnvHashMap<&'a [K], ()>>);

impl<'a, K: Eq + Hash> Interner<'a, K> {
    fn with_capacity(n: usize) -> Self {
        Interner(RefCell::new(FnvHashMap::with_capacity_and_hasher(
            n,
            Default::default(),
        )))
    }
    pub fn intern<Q>(&self, value: K, make: impl FnOnce(K) -> &'a K) -> &'a K
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut table = self.0.borrow_mut();
        // TODO: might not be super-efficient
        if let Some((k, _)) = table.get_key_value(&value) {
            &k
        } else {
            let k = make(value);
            table.insert(k, ());
            k
        }
    }
}

impl<'a, K> Default for Interner<'a, K> {
    fn default() -> Self {
        Interner(RefCell::new(FnvHashMap::default()))
    }
}

impl<'a, K: Eq + Hash> SliceInterner<'a, K> {
    pub fn with_capacity(n: usize) -> Self {
        SliceInterner(RefCell::new(FnvHashMap::with_capacity_and_hasher(
            n,
            Default::default(),
        )))
    }
    pub fn intern(&self, value: &[K], make: impl FnOnce(&[K]) -> &'a [K]) -> &'a [K] {
        let mut table = self.0.borrow_mut();
        // TODO: might not be super-efficient
        let opt: Option<(&&'a [K], _)> = table.get_key_value(value);
        if let Some((k, _)) = opt {
            *k
        } else {
            let k = make(value);
            table.insert(k, ());
            k
        }
    }
}

impl<'a, K> Default for SliceInterner<'a, K> {
    fn default() -> Self {
        SliceInterner(RefCell::new(FnvHashMap::default()))
    }
}

#[derive(Copy)]
/// The universe within which a [`Variable`], [`Type`], or [`TypeSchema`]
/// exists.
///
/// A `TypeContext` interns these values for more efficient reasoning. That is,
/// it stores owned copies of [`Type`]s and [`TypeSchema`]s. Whenever
/// requested, it returns a reference to these values in the form of a [`Ty`] or
/// [`Schema`]. These reference types are the primary way end-users interact
/// with types.
///
/// [`Variable`]: struct.Variable.html
/// [`Type`]: enum.Type.html
/// [`TypeSchema`]: enum.TypeSchema.html
/// [`Ty`]: type.Ty.html
/// [`Schema`]: type.Schema.html
pub struct TypeContext<'ctx, N: Name = &'static str> {
    ctx: &'ctx Context<'ctx, N>,
}

impl<'ctx, N: Name> PartialEq for TypeContext<'ctx, N> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.ctx, other.ctx)
    }
}

impl<'ctx, N: Name> std::fmt::Debug for TypeContext<'ctx, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "TypeContext<'ctx, N> {{ ctx: {:p} }}", self.ctx)
    }
}

impl<'ctx, N: Name> Eq for TypeContext<'ctx, N> {}

impl<'ctx, N: Name> Clone for TypeContext<'ctx, N> {
    fn clone(&self) -> Self {
        TypeContext { ctx: self.ctx }
    }
}

impl<'ctx, N: Name> Hash for TypeContext<'ctx, N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.ctx as *const Context<'ctx, N>).hash(state)
    }
}

/// The inner type managed by a [`TypeContext`]. A `Context` is not manipulated directly.
///
/// [`TypeContext`]: struct.TypeContext.html
pub struct Context<'ctx, N: Name = &'static str> {
    schema_arena: &'ctx Arena<TypeSchema<'ctx, N>>,
    schema_map: Interner<'ctx, TypeSchema<'ctx, N>>,
    type_arena: &'ctx Arena<Type<'ctx, N>>,
    type_map: Interner<'ctx, Type<'ctx, N>>,
    name_arena: &'ctx Arena<N>,
    name_map: Interner<'ctx, N>,
    arg_arena: &'ctx Arena<Ty<'ctx, N>>,
    arg_map: SliceInterner<'ctx, Ty<'ctx, N>>,
}

/// This is the most straightforward way to gain access to a [`TypeContext`].
///
/// `with_ctx` creates a [`TypeContext`], `ctx`, with `n` slots pre-allocated in
/// each arena, calls `f(ctx)`, and returns the result.
///
/// # Examples
///
/// ```
/// # use polytype::{ptp, tp, with_ctx, Context, Source, Substitution, Variable};
/// let t_string = with_ctx(32, |ctx| {
///   // filter: ∀α. (α → bool) → [α] → [α]
///   let t = ptp!(ctx, 0; @arrow[
///       tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, bool)]),
///       tp!(ctx, list(tp!(ctx, 0))),
///       tp!(ctx, list(tp!(ctx, 0))),
///   ]);
///   t.to_string()
/// });
/// assert_eq!(t_string, "∀t0. (t0 → bool) → list(t0) → list(t0)");
/// ```
///
/// [`TypeContext`]: struct.TypeContext.html
pub fn with_ctx<F, R, M: Name>(n: usize, f: F) -> R
where
    F: FnOnce(TypeContext<'_, M>) -> R,
{
    let schemaa: Arena<TypeSchema<'_, M>> = Arena::with_capacity(n);
    let typea: Arena<Type<'_, M>> = Arena::with_capacity(n);
    let namea: Arena<M> = Arena::with_capacity(n);
    let tya: Arena<Ty<'_, M>> = Arena::with_capacity(n);
    let ctx = Context::with_capacity(&schemaa, &typea, &namea, &tya, n);
    let ctx: TypeContext<'_, M> = TypeContext::new(&ctx);
    f(ctx)
}

impl<'ctx, N: Name> TypeContext<'ctx, N> {
    /// Create a new `TypeContext` from a [`Context`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use typed_arena::Arena;
    /// # use polytype::{ptp, tp, Context, TypeContext, Type, TypeSchema, Ty};
    /// let schemaa: Arena<TypeSchema<'_>> = Arena::with_capacity(10);
    /// let typea: Arena<Type<'_>> = Arena::with_capacity(10);
    /// let namea: Arena<&'static str> = Arena::with_capacity(10);
    /// let tya: Arena<Ty<'_>> = Arena::with_capacity(10);
    /// let context = Context::with_capacity(&schemaa, &typea, &namea, &tya, 10);
    /// let ctx = TypeContext::new(&context);
    /// let t = ptp!(ctx, 0; @arrow[
    ///     tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1)]),
    ///     tp!(ctx, list(tp!(ctx, 0))),
    ///     tp!(ctx, list(tp!(ctx, 1))),
    /// ]);
    /// assert_eq!(t.to_string(), "∀t0. (t0 → t1) → list(t0) → list(t1)");
    /// ```
    ///
    /// [`Context`]: struct.Context.html
    pub fn new(ctx: &'ctx Context<'ctx, N>) -> Self {
        TypeContext { ctx }
    }
    /// Intern a variable [`Type`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let t = ctx.intern_tvar(Variable(0));
    ///   assert_eq!(t.to_string(), "t0");
    /// });
    /// ```
    ///
    /// [`Type`]: enum.Type.html
    pub fn intern_tvar(&self, v: Variable) -> Ty<'ctx, N> {
        let t = Type::Variable(v);
        self.ctx
            .type_map
            .intern(t, |t| self.ctx.type_arena.alloc(t))
    }
    /// Intern a `&[`[`Ty`]`]`.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use polytype::{with_ctx, Variable};
    /// # use itertools::Itertools;
    /// with_ctx(32, |ctx| {
    ///   let ts = ctx.intern_args(&[tp!(ctx, int), tp!(ctx, bool)]);
    ///   assert_eq!(format!("[{}]", ts.iter().format!(", ")), "[int, bool]");
    /// });
    /// ```
    ///
    /// [`Ty`]: type.Ty.html
    pub(crate) fn intern_args(&self, args: &[Ty<'ctx, N>]) -> &'ctx [Ty<'ctx, N>] {
        self.ctx.arg_map.intern(args, |args| {
            self.ctx.arg_arena.alloc_extend(args.iter().copied())
        })
    }
    /// Intern a non-variable [`Type`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let name = ctx.intern_name("dict");
    ///   let t = ctx.intern_tcon(name, &[tp!(ctx, int), tp!(ctx, bool)]);
    ///   assert_eq!(t.to_string(), "dict(int,bool)");
    /// });
    /// ```
    ///
    /// [`Type`]: enum.Type.html
    pub fn intern_tcon(&self, head: &'ctx N, args: &[Ty<'ctx, N>]) -> Ty<'ctx, N> {
        let body = self.intern_args(args);
        let t = Type::Constructed(head, body);
        self.ctx
            .type_map
            .intern(t, |t| self.ctx.type_arena.alloc(t))
    }
    /// Intern a function (i.e. arrow) [`Type`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let t = ctx.arrow(tp!(ctx, 0), tp!(ctx, bool));
    ///   assert_eq!(t.to_string(), "t0 → bool");
    /// });
    /// ```
    ///
    /// [`Type`]: enum.Type.html
    pub fn arrow(&self, alpha: Ty<'ctx, N>, beta: Ty<'ctx, N>) -> Ty<'ctx, N> {
        let head = self.intern_name(N::arrow());
        self.intern_tcon(head, &[alpha, beta])
    }
    /// Intern a nested sequence of left-associative functions (i.e. arrow) as a
    /// single [`Type`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let t = ctx.arrow_slice(&[tp!(ctx, 0), tp!(ctx, int), tp!(ctx, bool)]);
    ///   assert_eq!(t.to_string(), "t0 → int → bool");
    /// });
    /// ```
    ///
    /// [`Type`]: enum.Type.html
    pub fn arrow_slice(&self, tps: &[Ty<'ctx, N>]) -> Ty<'ctx, N> {
        tps.iter()
            .rev()
            .copied()
            .fold1(|x, y| self.arrow(y, x))
            .unwrap_or_else(|| panic!("cannot create a type from nothing"))
    }
    /// Intern a [`Ty`] as a [`TypeSchema::Monotype`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let t = tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx,int), tp!(ctx, bool)]);
    ///   let schema = ctx.intern_monotype(t);
    ///   assert_eq!(schema.to_string(), "t0 → int → bool");
    /// });
    /// ```
    ///
    /// [`Ty`]: type.Ty.html
    /// [`TypeSchema::Monotype`]: enum.TypeSchema.html#variant.Monotype
    pub fn intern_monotype(&self, inner: Ty<'ctx, N>) -> Schema<'ctx, N> {
        let t = TypeSchema::Monotype(inner);
        self.ctx
            .schema_map
            .intern(t, |t| self.ctx.schema_arena.alloc(t))
    }
    /// Intern a [`Ty`] as a [`TypeSchema::Polytype`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let t = tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx,int), tp!(ctx, bool)]);
    ///   let mono = ctx.intern_monotype(t);
    ///   let poly = ctx.intern_polytype(Variable(0), mono);
    ///   assert_eq!(poly.to_string(), "∀t0. t0 → int → bool");
    /// });
    /// ```
    ///
    /// [`Ty`]: type.Ty.html
    /// [`TypeSchema::Polytype`]: enum.TypeSchema.html#variant.Polytype
    pub fn intern_polytype(&self, v: Variable, body: Schema<'ctx, N>) -> Schema<'ctx, N> {
        let t = TypeSchema::Polytype(v, body);
        self.ctx
            .schema_map
            .intern(t, |t| self.ctx.schema_arena.alloc(t))
    }
    /// Intern a type constructor name.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let bool_name = ctx.intern_name("bool");
    ///   assert_eq!(*bool_name, "bool");
    /// });
    /// ```
    pub fn intern_name(&self, n: N) -> &'ctx N {
        self.ctx
            .name_map
            .intern(n, |n| self.ctx.name_arena.alloc(n))
    }
}

impl<'ctx, N: Name> Context<'ctx, N> {
    /// Create a `Context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use typed_arena::Arena;
    /// # use polytype::{ptp, tp, Context, TypeContext, Type, TypeSchema, Ty};
    /// let schemaa: Arena<TypeSchema<'_>> = Arena::with_capacity(10);
    /// let typea: Arena<Type<'_>> = Arena::with_capacity(10);
    /// let namea: Arena<&'static str> = Arena::with_capacity(10);
    /// let tya: Arena<Ty<'_>> = Arena::with_capacity(10);
    /// let context = Context::new(&schemaa, &typea, &namea, &tya);
    /// ```
    pub fn new(
        schema_arena: &'ctx Arena<TypeSchema<'ctx, N>>,
        type_arena: &'ctx Arena<Type<'ctx, N>>,
        name_arena: &'ctx Arena<N>,
        arg_arena: &'ctx Arena<Ty<'ctx, N>>,
    ) -> Self {
        Context {
            schema_arena,
            schema_map: Interner::default(),
            type_arena,
            type_map: Interner::default(),
            name_arena,
            name_map: Interner::default(),
            arg_arena,
            arg_map: SliceInterner::default(),
        }
    }
    /// Create a `Context` and reserve capacity for type interning.
    ///
    /// # Examples
    ///
    /// ```
    /// # use typed_arena::Arena;
    /// # use polytype::{ptp, tp, Context, TypeContext, Type, TypeSchema, Ty};
    /// let schemaa: Arena<TypeSchema<'_>> = Arena::with_capacity(10);
    /// let typea: Arena<Type<'_>> = Arena::with_capacity(10);
    /// let namea: Arena<&'static str> = Arena::with_capacity(10);
    /// let tya: Arena<Ty<'_>> = Arena::with_capacity(10);
    /// let context = Context::with_capacity(&schemaa, &typea, &namea, &tya, 10);
    /// ```
    pub fn with_capacity(
        schema_arena: &'ctx Arena<TypeSchema<'ctx, N>>,
        type_arena: &'ctx Arena<Type<'ctx, N>>,
        name_arena: &'ctx Arena<N>,
        arg_arena: &'ctx Arena<Ty<'ctx, N>>,
        n: usize,
    ) -> Self {
        Context {
            schema_arena,
            schema_map: Interner::with_capacity(n),
            type_arena,
            type_map: Interner::with_capacity(n),
            name_arena,
            name_map: Interner::with_capacity(n),
            arg_arena,
            arg_map: SliceInterner::with_capacity(n),
        }
    }
}
