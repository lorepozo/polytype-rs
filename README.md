# polytype

[![Build Status](https://travis-ci.org/lucasem/polytype-rs.svg?branch=master)](https://travis-ci.org/lucasem/polytype-rs)
[![crates.io](https://img.shields.io/crates/v/polytype.svg)](https://crates.io/crates/polytype)
[![docs.rs](https://docs.rs/polytype/badge.svg)](https://docs.rs/polytype)

A [Hindley-Milner](https://wikipedia.org/wiki/Hindley–Milner_type_system) polymorphic typing system.
Implements type inference via unification.

## Usage

```toml
[dependencies]
polytype = "1.1"
```

Provided by **`polytype`** are the
[`Type`](https://docs.rs/polytype/1.1.0/polytype/enum.Type.html) enum and
the [`Context`](https://docs.rs/polytype/1.1.0/polytype/struct.Context.html)
struct.

Unification:

```rust
let mut ctx = Context::default();

let tbool = Type::Constructed("bool", vec![]);
let tint = Type::Constructed("int", vec![]);
fn tlist(tp: Type) -> Type {
    Type::Constructed("list", vec![Box::new(tp)])
}

// t1: list(int → α) ; t2: list(β → bool)
let t1 = tlist(Type::Arrow(Arrow::new(tint, Type::Variable(0))));
let t2 = tlist(Type::Arrow(Arrow::new(Type::Variable(1), tbool)));
ctx.unify(&t1, &t2).expect("unifies");

let t1 = t1.apply(&ctx);
let t2 = t2.apply(&ctx);
assert_eq!(t1, t2); // list(int → bool)
```

Apply a type context:

```rust
let mut ctx = Context::default();
// assign t0 to int
ctx.unify(&Type::Variable(0), &Type::Constructed("int", vec![])).expect("unifies");

let t = Type::Constructed("list", vec![Box::new(Type::Variable(0))]);
assert_eq!(format!("{}", &t), "list(t0)");
let t = t.apply(&ctx);
assert_eq!(format!("{}", &t), "list(int)");
```

Independent instantiation:

```rust
let mut ctx = Context::default();

let t1 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
let t2 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);

let t1 = t1.instantiate_indep(&mut ctx);
let t2 = t2.instantiate_indep(&mut ctx);
assert_eq!(format!("{}", &t1), "list(t0)");
assert_eq!(format!("{}", &t2), "list(t1)");
```

Dependent instantiation:

```rust
use std::collections::HashMap;

let mut ctx = Context::default();

let t1 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);
let t2 = Type::Constructed("list", vec![Box::new(Type::Variable(3))]);

let mut bindings = HashMap::new();
let t1 = t1.instantiate(&mut ctx, &mut bindings);
let t2 = t2.instantiate(&mut ctx, &mut bindings);
assert_eq!(format!("{}", &t1), "list(t0)");
assert_eq!(format!("{}", &t2), "list(t0)");
```

See the [documentation](https://docs.rs/polytype) for more details.
