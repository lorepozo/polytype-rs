use crate::{Name, Ty, TypeContext, Variable};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// A way to mark the current state of a [`Substitution`] such that it can be later restored.
///
/// [`Substitution`]: struct.Substitution.html
pub struct Snapshot(usize);

#[derive(Clone, Debug, PartialEq, Eq)]
/// A mapping from [`Variable`]s to [`Ty`]s indicating that each [`Variable`]
/// can be substituted for the corresponding [`Ty`].
///
/// [`Variable`]: struct.Variable.html
/// [`Ty`]: type.Ty.html
pub struct Substitution<'ctx, N: Name = &'static str> {
    /// The `TypeContext` in which typing takes place.
    pub(crate) ctx: TypeContext<'ctx, N>,
    /// The `Variable` to `Ty` map.
    pub(crate) sub: Vec<(Variable, Ty<'ctx, N>)>,
}

pub struct SubIter<'a, 'ctx, N: Name = &'static str> {
    it: std::slice::Iter<'a, (Variable, Ty<'ctx, N>)>,
}
pub struct SubIterMut<'a, 'ctx, N: Name = &'static str> {
    it: std::slice::IterMut<'a, (Variable, Ty<'ctx, N>)>,
}

impl<'ctx, N: Name> Substitution<'ctx, N> {
    /// Construct an empty `Substitution` with at least capacity for `n` mappings.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext};
    /// with_ctx(32, |ctx: TypeContext<'_>| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   assert_eq!(sub.len(), 0);
    /// });
    /// ```
    pub fn with_capacity(ctx: TypeContext<'ctx, N>, n: usize) -> Self {
        Substitution {
            ctx,
            sub: Vec::with_capacity(n),
        }
    }
    /// Optionally retrieve the [`Ty`] associated with some variable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, Variable, Type};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   assert_eq!( sub.get(Variable(0)), Some(tp!(ctx, int)));
    ///   assert_eq!(sub.get(Variable(1)), None)
    /// });
    /// ```
    pub fn get(&self, q: Variable) -> Option<Ty<'ctx, N>> {
        self.sub.iter().find(|(k, _)| *k == q).map(|(_, v)| *v)
    }
    /// Insert a new mapping into the `Substitution` unless it conflicts with an
    /// existing mapping.
    ///
    /// The return value indicates whether the insertion was successful.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   assert_eq!(sub.len(), 0);
    ///   let added = sub.add(Variable(0), tp!(ctx, int));
    ///   assert!(added);
    ///   assert_eq!(sub.len(), 1);
    ///   let added = sub.add(Variable(0), tp!(ctx, bool));
    ///   assert!(!added);
    ///   assert_eq!(sub.len(), 1);
    /// });
    /// ```
    pub fn add(&mut self, k: Variable, v: Ty<'ctx, N>) -> bool {
        if self.sub.iter().any(|(j, _)| k == *j) {
            false
        } else {
            self.sub.push((k, v));
            true
        }
    }
    /// The `Substitution` as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   sub.add(Variable(1), tp!(ctx, bool));
    ///   let slice = sub.as_slice();
    ///   assert_eq!(slice.len(), 2);
    ///   assert_eq!(slice[0], (Variable(0), tp!(ctx, int)));
    ///   assert_eq!(slice[1], (Variable(1), tp!(ctx, bool)));
    /// });
    /// ```
    pub fn as_slice(&self) -> &[(Variable, Ty<'ctx, N>)] {
        &self.sub
    }
    /// An Iterator over the `Substitution`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   sub.add(Variable(1), tp!(ctx, bool));
    ///   sub.add(Variable(2), tp!(ctx, bool));
    ///   sub.add(Variable(3), tp!(ctx, char));
    ///   sub.add(Variable(4), tp!(ctx, bool));
    ///   assert_eq!(sub.iter().filter(|(v, t)| *t == tp!(ctx, bool)).count(), 3);
    /// });
    /// ```
    pub fn iter<'a>(&'a self) -> SubIter<'a, 'ctx, N> {
        SubIter {
            it: self.sub.iter(),
        }
    }
    /// A mutable Iterator over the `Substitution`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   sub.add(Variable(1), tp!(ctx, bool));
    ///   sub.add(Variable(2), tp!(ctx, bool));
    ///   sub.add(Variable(3), tp!(ctx, char));
    ///   sub.add(Variable(4), tp!(ctx, bool));
    ///   assert_eq!(sub.iter().filter(|(v, t)| *t == tp!(ctx, bool)).count(), 3);
    ///   for (v, t) in sub.iter_mut() {
    ///       *t = tp!(ctx, bool);
    ///   }
    ///   assert_eq!(sub.iter().filter(|(v, t)| *t == tp!(ctx, bool)).count(), 5);
    /// });
    /// ```
    pub fn iter_mut<'a>(&'a mut self) -> SubIterMut<'a, 'ctx, N> {
        SubIterMut {
            it: self.sub.iter_mut(),
        }
    }
    /// The number of constraints in the `Substitution`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   sub.add(Variable(1), tp!(ctx, bool));
    ///   sub.add(Variable(2), tp!(ctx, float));
    ///   sub.add(Variable(3), tp!(ctx, char));
    ///   sub.add(Variable(4), tp!(ctx, string));
    ///   assert_eq!(sub.len(), 5);
    /// });
    /// ```
    pub fn len(&self) -> usize {
        self.sub.len()
    }
    /// `true` if the `Substitution` has any constraints, else `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(32, |ctx| {
    ///   let mut sub = Substitution::with_capacity(ctx, 10);
    ///   assert!(sub.is_empty());
    ///   sub.add(Variable(0), tp!(ctx, int));
    ///   assert!(!sub.is_empty());
    /// });
    /// ```
    pub fn is_empty(&self) -> bool {
        self.sub.is_empty()
    }
    /// Clears the substitution managed by the context.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Substitution, TypeContext, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let mut sub = Substitution::with_capacity(ctx, 1);
    ///
    ///     let clean = sub.clone();
    ///
    ///     sub.add(Variable(0), tp!(ctx, int));
    ///     let dirty = sub.clone();
    ///
    ///     sub.clean();
    ///
    ///     assert_eq!(clean, sub);
    ///     assert_ne!(clean, dirty);
    /// })
    /// ```
    pub fn clean(&mut self) {
        self.sub.clear();
    }
    /// Creates a `Snapshot` to which the `Substitution` can be rolled back.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Snapshot, Substitution, TypeContext, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let mut sub = Substitution::with_capacity(ctx, 5);
    ///     sub.add(Variable(0), tp!(ctx, int));
    ///     sub.add(Variable(1), tp!(ctx, bool));
    ///     sub.add(Variable(2), tp!(ctx, char));
    ///     let snapshot = sub.snapshot();
    ///     assert_eq!(sub.len(), 3);
    ///     sub.add(Variable(3), tp!(ctx, bool));
    ///     sub.add(Variable(4), tp!(ctx, char));
    ///     assert_eq!(sub.len(), 5);
    ///     sub.rollback(snapshot);
    ///     assert_eq!(sub.len(), 3);
    /// })
    /// ```
    pub fn snapshot(&self) -> Snapshot {
        Snapshot(self.len())
    }
    /// Removes all substitutions added to the `Substitution` since the supplied `Snapshot`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use polytype::{tp, with_ctx, Snapshot, Substitution, TypeContext, Variable};
    /// with_ctx(10, |ctx: TypeContext<'_>| {
    ///     let mut sub = Substitution::with_capacity(ctx, 5);
    ///     sub.add(Variable(0), tp!(ctx, int));
    ///     sub.add(Variable(1), tp!(ctx, bool));
    ///     sub.add(Variable(2), tp!(ctx, char));
    ///     let snapshot = sub.snapshot();
    ///     assert_eq!(sub.len(), 3);
    ///     sub.add(Variable(3), tp!(ctx, bool));
    ///     sub.add(Variable(4), tp!(ctx, char));
    ///     assert_eq!(sub.len(), 5);
    ///     sub.rollback(snapshot);
    ///     assert_eq!(sub.len(), 3);
    /// })
    /// ```
    pub fn rollback(&mut self, Snapshot(n): Snapshot) {
        self.sub.truncate(n)
    }
}

impl<'a, 'ctx, N: Name> Iterator for SubIter<'a, 'ctx, N> {
    type Item = &'a (Variable, Ty<'ctx, N>);
    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}

impl<'a, 'ctx, N: Name> Iterator for SubIterMut<'a, 'ctx, N> {
    type Item = &'a mut (Variable, Ty<'ctx, N>);
    fn next(&mut self) -> Option<Self::Item> {
        self.it.next()
    }
}
