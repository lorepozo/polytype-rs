# polytype

[![Build Status](https://travis-ci.org/lorepozo/polytype-rs.svg?branch=master)](https://travis-ci.org/lorepozo/polytype-rs)
[![crates.io](https://img.shields.io/crates/v/polytype.svg)](https://crates.io/crates/polytype)
[![docs.rs](https://docs.rs/polytype/badge.svg)](https://docs.rs/polytype)

A [Hindley-Milner](https://wikipedia.org/wiki/Hindley–Milner_type_system) polymorphic typing system.
Implements type inference via unification.

## Usage

```toml
[dependencies]
polytype = "7.0"
```

**`polytype`** provides the
[`TypeScheme`](https://docs.rs/polytype/~7/polytype/enum.TypeScheme.html) and
[`Type`](https://docs.rs/polytype/~7/polytype/enum.Type.html) enums, the
[`Context`](https://docs.rs/polytype/~7/polytype/struct.Context.html)
struct, and the
[`tp!`](https://docs.rs/polytype/~7/polytype/macro.tp.html) and
[`ptp!`](https://docs.rs/polytype/~7/polytype/macro.ptp.html) macros which
help to concisely create types and type schemes.

Unification:

```rust
let mut ctx = Context::default();

// t1: list(int → α) ; t2: list(β → bool)
let t1 = tp!(list(tp!(@arrow[tp!(int), tp!(0)])));
let t2 = tp!(list(tp!(@arrow[tp!(1), tp!(bool)])));
ctx.unify(&t1, &t2).expect("unifies");

let t1 = t1.apply(&ctx);
let t2 = t2.apply(&ctx);
assert_eq!(t1, t2); // list(int → bool)
```

Apply a type context:

```rust
let mut ctx = Context::default();
// assign t0 to int
ctx.extend(0, tp!(int));

let t = tp!(list(tp!(0)));
assert_eq!(t.to_string(), "list(t0)");
let t = t.apply(&ctx);
assert_eq!(t.to_string(), "list(int)");
```

Instantiate a `TypeScheme`:

```rust
let mut ctx = Context::default();

// ∀α. list(α)
let scheme = ptp!(3; tp!(list(tp!(3))));

// They instantiate to new fresh type variables
let t1 = scheme.instantiate(&mut ctx);
let t2 = scheme.instantiate(&mut ctx);
assert_eq!(t1.to_string(), "list(t0)");
assert_eq!(t2.to_string(), "list(t1)");
```

See the [documentation](https://docs.rs/polytype) for more details.

## Features
By default `polytype` includes a type parser that can be invoked with
[str::parse](https://doc.rust-lang.org/stable/std/primitive.str.html#method.parse).
This can be disabled with `default-features = false`.

