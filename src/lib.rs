extern crate itertools;

use itertools::Itertools;

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Arrow(Arrow),
    Constructed(&'static str, Vec<Box<Type>>),
    Variable(u32),
}
impl Type {
    pub fn is_polymorphic(&self) -> bool {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                arg.is_polymorphic() || ret.is_polymorphic()
            }
            &Type::Constructed(_, ref args) => args.iter().any(|t| t.is_polymorphic()),
            &Type::Variable(_) => true,
        }
    }
    pub fn occurs(&self, v: u32) -> bool {
        match self {
            &Type::Arrow(Arrow { ref arg, ref ret }) => arg.occurs(v) || ret.occurs(v),
            &Type::Constructed(_, ref args) => args.iter().any(|t| t.occurs(v)),
            &Type::Variable(n) => n == v,
        }
    }
    /// Supplying is_return helps arrows look cleaner.
    pub fn show(&self, is_return: bool) -> String {
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
                if let Some(tp) = ctx.substitution.get(&v) {
                    tp.apply(ctx)
                } else {
                    Type::Variable(v)
                }
            }
        }
    }
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
    pub fn canonical(&self, bindings: &mut HashMap<u32, Type>) -> Type {
        let mut ctx = Context::default();
        ctx.next = bindings.len() as u32;
        self.instantiate(&mut ctx, bindings)
    }
}
impl From<Arrow> for Type {
    fn from(arrow: Arrow) -> Type {
        Type::Arrow(arrow)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Arrow {
    arg: Box<Type>,
    ret: Box<Type>,
}
impl Arrow {
    pub fn new(arg: Type, ret: Type) -> Arrow {
        let arg = Box::new(arg);
        let ret = Box::new(ret);
        Arrow { arg, ret }
    }
    pub fn args(&self) -> Vec<&Type> {
        if let Type::Arrow(ref arrow) = *self.ret {
            let mut tps = arrow.args();
            tps.insert(0, &self.arg);
            tps
        } else {
            vec![&self.arg]
        }
    }
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

#[derive(Debug)]
pub enum UnificationError {
    Occurs,
    Failure(Type, Type),
}

#[derive(Debug)]
pub struct Context {
    substitution: HashMap<u32, Type>,
    next: u32,
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
    pub fn extend(&mut self, v: u32, t: Type) {
        self.substitution.insert(v, t);
    }
    pub fn new_variable(&mut self) -> Type {
        self.next = self.next + 1;
        Type::Variable(self.next - 1)
    }
    pub fn unify(&mut self, t1: Type, t2: Type) -> Result<(), UnificationError> {
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
                    Err(UnificationError::Occurs)
                } else {
                    self.extend(v, t2.clone());
                    Ok(())
                }
            }
            (t1, Type::Variable(v)) => {
                if t1.occurs(v) {
                    Err(UnificationError::Occurs)
                } else {
                    self.extend(v, t1.clone());
                    Ok(())
                }
            }
            (Type::Arrow(a1), Type::Arrow(a2)) => {
                self.unify(*a1.arg, *a2.arg)?;
                self.unify(*a1.ret, *a2.ret)
            }
            (Type::Constructed(n1, a1), Type::Constructed(n2, a2)) => {
                if n1 != n2 {
                    Err(UnificationError::Failure(
                        Type::Constructed(n1, a1),
                        Type::Constructed(n2, a2),
                    ))
                } else {
                    for (t1, t2) in a1.into_iter().zip(a2) {
                        self.unify(*t1, *t2)?;
                    }
                    Ok(())
                }
            }
            (t1, t2) => Err(UnificationError::Failure(t1, t2)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find_variables(tp: &Type, o: &mut Vec<u32>) {
        match tp {
            &Type::Arrow(Arrow { ref arg, ref ret }) => {
                find_variables(arg, o);
                find_variables(ret, o)
            }
            &Type::Constructed(_, ref args) => for arg in args {
                find_variables(arg, o)
            },
            &Type::Variable(v) => o.push(v),
        }
    }
    fn variables(tp: &Type) -> Vec<u32> {
        let mut v = vec![];
        find_variables(tp, &mut v);
        v
    }

    fn tbool() -> Type {
        Type::Constructed("bool", vec![])
    }
    fn tint() -> Type {
        Type::Constructed("int", vec![])
    }
    fn tlist(tp: Type) -> Type {
        Type::Constructed("list", vec![Box::new(tp)])
    }

    #[test]
    fn test_unify_one_side_polymorphic() {
        let mut ctx = Context::default();
        ctx.unify(
            tlist(Arrow::new(tint(), tbool()).into()),
            tlist(Type::Variable(0)),
        ).expect("one side polymorphic");
    }
    #[test]
    fn test_unify_one_side_polymorphic_fail() {
        let mut ctx = Context::default();
        ctx.unify(Arrow::new(tint(), tbool()).into(), tlist(Type::Variable(0)))
            .expect_err("incompatible types");
    }
    #[test]
    fn test_unify_both_sides_polymorphic() {
        let mut ctx = Context::default();
        ctx.unify(
            tlist(Arrow::new(tint(), Type::Variable(0)).into()),
            tlist(Arrow::new(Type::Variable(1), tbool()).into()),
        ).expect("both sides polymorphic");
    }
    #[test]
    fn test_unify_both_sides_polymorphic_occurs() {
        let mut ctx = Context::default();
        ctx.unify(
            tlist(Arrow::new(tint(), Type::Variable(0)).into()),
            tlist(Arrow::new(Type::Variable(0), tbool()).into()),
        ).expect_err("incompatible polymorphic types");
    }
    #[test]
    fn test_instantiate() {
        let mut ctx = Context::default();
        let mut bindings = HashMap::new();
        let dummy = Type::Constructed(
            "dummy",
            vec![Box::new(tlist(tint())), Box::new(tlist(Type::Variable(3)))],
        );
        ctx.unify(Type::Variable(1), dummy.clone())
            .expect("unify on empty context");

        let t1 = tlist(Arrow::new(tint(), Type::Variable(2)).into())
            .instantiate(&mut ctx, &mut bindings);
        let t2 = tlist(Arrow::new(Type::Variable(2), tbool()).into())
            .instantiate(&mut ctx, &mut bindings);
        let t3 = tlist(Type::Variable(3)).instantiate(&mut ctx, &mut bindings);

        // type variables start at 0
        assert_eq!(bindings.get(&2).unwrap(), &Type::Variable(0));
        assert_eq!(bindings.get(&3).unwrap(), &Type::Variable(1));
        // like replaces like
        assert_eq!(variables(&t1), variables(&t2));
        // substitutions are not made
        assert_eq!(
            t3,
            Type::Constructed("list", vec![Box::new(Type::Variable(1))])
        );
        // context is updated
        assert_eq!(ctx.next, 2);
        assert_eq!(ctx.substitution.get(&1).unwrap(), &dummy);
        assert_eq!(ctx.substitution.len(), 1);
    }
    #[test]
    fn test_canonicalize() {
        let mut bindings = HashMap::new();
        let t1 = tlist(Arrow::new(tint(), Type::Variable(2)).into()).canonical(&mut bindings);
        let t2 = tlist(Arrow::new(Type::Variable(2), tbool()).into()).canonical(&mut bindings);
        let t3 = tlist(Type::Variable(3)).canonical(&mut bindings);

        // type variables start at 0
        assert_eq!(bindings.get(&2).unwrap(), &Type::Variable(0));
        assert_eq!(bindings.get(&3).unwrap(), &Type::Variable(1));
        // like replaces like
        assert_eq!(variables(&t1), variables(&t2));
        assert_eq!(t3, tlist(Type::Variable(1)))
    }
}
