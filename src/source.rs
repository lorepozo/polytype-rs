use crate::{Name, Schema, Ty, Type, TypeContext, TypeSchema, Variable};

/// A way to generate fresh [`Variable`]s.
///
/// [`Variable`]: struct.Variable.html
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Source(pub(crate) usize);

/// Allow types to be reified for use under a different [`Source`].
///
/// [`Source`]: struct.Source.html
pub struct SourceChange {
    pub(crate) delta: usize,
    pub(crate) sacreds: Vec<Variable>,
}

impl Source {
    /// Get a fresh bare [`Variable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Source, TypeContext};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let mut src = Source::default();
    ///   assert_eq!(src.fresh(), 0);
    ///   assert_eq!(src.fresh(), 1);
    ///   assert_eq!(src.fresh(), 2);
    /// });
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    pub fn fresh(&mut self) -> usize {
        let var = self.0;
        self.0 += 1;
        var
    }
    /// Combine two `Source`s.
    ///
    /// This merges `other` into `self` and produces a [`SourceChange`], which
    /// can be used to transform the values produced by `other` to be consistent
    /// with the state of `self` after the merge. Values passed in as `sacreds`
    /// are considered to be shared between the two `Source`s.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Source, TypeContext, Variable};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let mut src_1 = Source::default();
    ///   src_1.fresh();
    ///   src_1.fresh();
    ///   let mut src_2 = Source::default();
    ///   src_2.fresh();
    ///   src_2.fresh();
    ///   let change = src_1.merge(src_2, vec![Variable(1)]);
    ///   assert_eq!(src_1.fresh(), 4);
    ///
    ///   let t_original = tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1)]);
    ///   assert_eq!(t_original.to_string(), "t0 → t1");
    ///
    ///   let t_reified = change.reify_type(t_original, &ctx);
    ///   assert_eq!(t_reified.to_string(), "t2 → t1");
    /// });
    /// ```
    ///
    /// [`Variable`]: type.Variable.html
    pub fn merge(&mut self, other: Self, sacreds: Vec<Variable>) -> SourceChange {
        let delta = self.0;
        // this is intentionally wasting variable space when there are sacreds:
        self.0 += other.0;
        SourceChange { delta, sacreds }
    }
}

impl Default for Source {
    fn default() -> Self {
        Source(0)
    }
}

impl SourceChange {
    /// Reify a [`Ty`] for use under a new [`Source`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Source, TypeContext, Variable};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let mut src_1 = Source::default();
    ///   src_1.fresh();
    ///   src_1.fresh();
    ///   let mut src_2 = Source::default();
    ///   src_2.fresh();
    ///   src_2.fresh();
    ///   let change = src_1.merge(src_2, vec![Variable(1)]);
    ///   assert_eq!(src_1.fresh(), 4);
    ///
    ///   let t_original = tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1)]);
    ///   assert_eq!(t_original.to_string(), "t0 → t1");
    ///
    ///   let t_reified = change.reify_type(t_original, &ctx);
    ///   assert_eq!(t_reified.to_string(), "t2 → t1");
    /// });
    /// ```
    ///
    /// [`Source`]: struct.Source.html
    /// [`Ty`]: type.Ty.html
    pub fn reify_type<'ctx, N: Name>(
        &self,
        tp: Ty<'ctx, N>,
        ctx: &TypeContext<'ctx, N>,
    ) -> Ty<'ctx, N> {
        match *tp {
            Type::Constructed(head, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for arg in args {
                    new_args.push(self.reify_type(arg, ctx));
                }
                let new_args = ctx.intern_args(&new_args);
                ctx.intern_tcon(head, new_args)
            }
            Type::Variable(n) if self.sacreds.contains(&n) => tp,
            Type::Variable(n) => ctx.intern_tvar(Variable(n.0 + self.delta)),
        }
    }
    /// Reify a [`TypeSchema`] for use under a new [`Source`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{ptp, tp, with_ctx, Source, TypeContext, Variable};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let mut src_1 = Source::default();
    ///   src_1.fresh();
    ///   src_1.fresh();
    ///   src_1.fresh();
    ///
    ///   let mut src_2 = Source::default();
    ///   src_2.fresh();
    ///   src_2.fresh();
    ///   src_2.fresh();
    ///
    ///   let change = src_1.merge(src_2, vec![Variable(1)]);
    ///   assert_eq!(src_1.fresh(), 6);
    ///
    ///   let s_original = ptp!(ctx, 0, @arrow[
    ///       tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1)]),
    ///       tp!(ctx, @arrow[tp!(ctx, 2), tp!(ctx, 1)])
    ///   ]);
    ///   assert_eq!(s_original.to_string(), "∀t0. (t0 → t1) → t2 → t1");
    ///
    ///   let s_reified = change.reify_typeschema(s_original, &ctx);
    ///   assert_eq!(s_reified.to_string(), "∀t3. (t3 → t1) → t5 → t1");
    /// });
    /// ```
    ///
    /// [`Schema`]: type.Schema.html
    /// [`Source`]: struct.Source.html
    pub fn reify_typeschema<'ctx, N: Name>(
        &self,
        schema: Schema<'ctx, N>,
        ctx: &TypeContext<'ctx, N>,
    ) -> Schema<'ctx, N> {
        match schema {
            TypeSchema::Monotype(inner) => ctx.intern_monotype(self.reify_type(inner, ctx)),
            TypeSchema::Polytype(variable, body) => {
                let t_var = Variable(variable.0 + self.delta);
                let new_body = self.reify_typeschema(body, ctx);
                ctx.intern_polytype(t_var, new_body)
            }
        }
    }
}
