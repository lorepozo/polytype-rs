use itertools::Itertools;

use std::collections::HashMap;

pub trait Type {
    fn is_polymorphic(&self) -> bool;
    fn occurs(&self, v: u32) -> bool;
    fn as_arrow(&self) -> Option<&Arrow>;
    /// Supplying is_return helps arrows look cleaner.
    fn show(&self, is_return: bool) -> String;
    fn clone_box(&self) -> Box<Type>;
}

pub struct Arrow {
    pub arg: Box<Type>,
    pub ret: Box<Type>,
}
impl Type for Arrow {
    fn is_polymorphic(&self) -> bool {
        self.arg.is_polymorphic() || self.ret.is_polymorphic()
    }
    fn occurs(&self, v: u32) -> bool {
        self.arg.occurs(v) || self.ret.occurs(v)
    }
    fn as_arrow(&self) -> Option<&Arrow> {
        Some(&self)
    }
    fn show(&self, is_return: bool) -> String {
        if is_return {
            format!("{} → {}", self.arg.show(false), self.ret.show(true))
        } else {
            format!("({} → {})", self.arg.show(false), self.ret.show(true))
        }
    }
    fn clone_box(&self) -> Box<Type> {
        Box::new(Arrow {
            arg: self.arg.clone_box(),
            ret: self.ret.clone_box(),
        })
    }
}
impl Arrow {
    pub fn arg_types(&self) -> Vec<&Box<Type>> {
        if let Some(arrow) = self.ret.as_arrow() {
            let mut tps = arrow.arg_types();
            tps.insert(0, &self.arg);
            tps
        } else {
            vec![&self.arg]
        }
    }
    pub fn return_type(&self) -> &Box<Type> {
        if let Some(arrow) = self.ret.as_arrow() {
            arrow.return_type()
        } else {
            &self.ret
        }
    }
}

pub struct Constructed {
    pub name: String,
    pub args: Vec<Box<Type>>,
}
impl Type for Constructed {
    fn is_polymorphic(&self) -> bool {
        self.args.iter().any(|t| t.is_polymorphic())
    }
    fn occurs(&self, v: u32) -> bool {
        self.args.iter().any(|t| t.occurs(v))
    }
    fn as_arrow(&self) -> Option<&Arrow> {
        None
    }
    fn show(&self, _is_return: bool) -> String {
        if self.args.is_empty() {
            self.name.clone()
        } else {
            format!(
                "{}({})",
                &self.name,
                self.args.iter().map(|t| t.show(true)).join(",")
            )
        }
    }
    fn clone_box(&self) -> Box<Type> {
        Box::new(Constructed {
            name: self.name.clone(),
            args: self.args.iter().map(|t| t.clone_box()).collect(),
        })
    }
}

pub struct Variable(u32);
impl Type for Variable {
    fn is_polymorphic(&self) -> bool {
        true
    }
    fn occurs(&self, v: u32) -> bool {
        self.0 == v
    }
    fn as_arrow(&self) -> Option<&Arrow> {
        None
    }
    fn show(&self, _is_return: bool) -> String {
        format!("t{}", self.0)
    }
    fn clone_box(&self) -> Box<Type> {
        Box::new(Variable(self.0))
    }
}

pub enum UnificationError {
    Occurs,
    UnificationFailure(Box<Type>, Box<Type>),
}

pub struct Context {
    substitution: HashMap<u32, Box<Type>>,
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
    pub fn extend(&mut self, v: u32, t: Box<Type>) {
        self.substitution.insert(v, t);
    }
    pub fn new_variable(&mut self) -> Variable {
        self.next = self.next + 1;
        Variable(self.next - 1)
    }
}
