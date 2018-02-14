use itertools::Itertools;

use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub enum Type {
    Arrow(Arrow),
    Constructed(String, Vec<Box<Type>>),
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
            &Type::Constructed(ref name, ref args) => {
                if args.is_empty() {
                    name.clone()
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
                let name = name.clone();
                let args = args.iter().map(|t| Box::new(t.apply(ctx))).collect();
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
}

#[derive(Clone, PartialEq)]
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
    pub fn as_type(self) -> Type {
        Type::Arrow(self)
    }
    fn show(&self, is_return: bool) -> String {
        if is_return {
            format!("{} → {}", self.arg.show(false), self.ret.show(true))
        } else {
            format!("({} → {})", self.arg.show(false), self.ret.show(true))
        }
    }
    pub fn arg_types(&self) -> Vec<&Type> {
        if let Type::Arrow(ref arrow) = *self.ret {
            let mut tps = arrow.arg_types();
            tps.insert(0, &self.arg);
            tps
        } else {
            vec![&self.arg]
        }
    }
    pub fn return_type(&self) -> &Type {
        if let Type::Arrow(ref arrow) = *self.ret {
            arrow.return_type()
        } else {
            &self.ret
        }
    }
}

pub enum UnificationError {
    Occurs,
    UnificationFailure(Box<Type>, Type),
}

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
}
