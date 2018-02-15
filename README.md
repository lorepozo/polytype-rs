# polytype

[![Build Status](https://travis-ci.org/lucasem/polytype-rs.svg?branch=master)](https://travis-ci.org/lucasem/polytype-rs)
[![crates.io](https://img.shields.io/crates/v/polytype.svg)](https://crates.io/crates/polytype)
[![docs.rs](https://docs.rs/polytype/badge.svg)](https://docs.rs/polytype)

A [Hindley-Milner](https://wikipedia.org/wiki/Hindley–Milner_type_system) polymorphic typing system.
Implements type inference via unification.

## Usage

```toml
[dependencies]
polytype = "1.0"
```

Provided by **`polytype`** are the
[`Type`](https://docs.rs/polytype/1.0.2/polytype/enum.Type.html) enum and
the [`Context`](https://docs.rs/polytype/1.0.2/polytype/struct.Context.html)
struct.

The basics:

```rust
// filter: (α → bool) → [α] → [α]
#[macro_use] extern crate polytype;
use polytype::{Context, Type};

fn tlist(tp: Type) -> Type {
    Type::Constructed("list", vec![Box::new(tp)])
}

fn main() {
    let t0 = Type::Variable(0);
    let tbool = Type::Constructed("bool", vec![]);

    // the filter type
    let t = arrow![
        arrow![t0.clone(), tbool],
        tlist(t0.clone()),
        tlist(t0.clone()),
    ];

    assert!(t.is_polymorphic());
    assert_eq!(format!("{}", &t),
               "(t0 → bool) → list(t0) → list(t0)");

    // we can substitute t0 using a type context:
    let mut ctx = Context::default();

    let tint = Type::Constructed("int", vec![]);
    ctx.unify(&t0, &tint).expect("unifies");

    let t = t.apply(&ctx);
    assert!(!t.is_polymorphic());
    assert_eq!(format!("{}", &t),
               "(int → bool) → list(int) → list(int)");
}
```

More about instantiation, and unification:

```rust
// reduce: (β → α → β) → β → [α] → β
#[macro_use] extern crate polytype;
use polytype::{Context, Type};

fn tlist(tp: Type) -> Type {
    Type::Constructed("list", vec![Box::new(tp)])
}

fn main() {
    let t0 = Type::Variable(0);
    let t1 = Type::Variable(1);

    // the reduce type
    let t = arrow![
        arrow![
            t1.clone(),
            t0.clone(),
            t1.clone(),
        ],
        t1.clone(),
        tlist(t0.clone()),
        t1.clone(),
    ];

    assert!(t.is_polymorphic());
    assert_eq!(format!("{}", &t),
               "(t1 → t0 → t1) → t1 → list(t0) → t1");

    let tint = Type::Constructed("int", vec![]);
    let tplus = arrow![tint.clone(), tint.clone(), tint.clone()];  // e.g. add two ints
    assert_eq!(format!("{}", &tplus), "int → int → int");

    // instantiate polymorphic types within our context so new type variables will be distinct
    let mut ctx = Context::default();
    let t = t.instantiate_indep(&mut ctx);

    // by unifying, we can ensure valid function application and infer what gets returned
    let treturn = ctx.new_variable();
    ctx.unify(
        &t,
        &arrow![
            tplus.clone(),
            tint.clone(),
            tlist(tint.clone()),
            treturn.clone(),
        ],
    ).expect("unifies");
    assert_eq!(treturn.apply(&ctx), tint.clone());  // inferred return: int

    // now that unification has happened with ctx, we can see what form reduce takes
    let t = t.apply(&ctx);
    assert_eq!(format!("{}", t),
               "(int → int → int) → int → list(int) → int");
}
```
