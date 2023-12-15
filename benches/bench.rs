#![feature(test)]

extern crate test;

use polytype::{ptp, tp, Context};
use test::Bencher;

#[bench]
fn instantiate_unify_apply(b: &mut Bencher) {
    b.iter(|| {
        let mut ctx = Context::default();
        let scheme = ptp!(0, 1; @arrow[
            tp!(@arrow[tp!(1), tp!(0), tp!(1)]),
            tp!(1),
            tp!(list(tp!(0))),
            tp!(1),
        ]);
        let t = scheme.instantiate(&mut ctx);
        let target = tp!(@arrow[
            tp!(@arrow[tp!(int), tp!(obj), tp!(int)]),
            ctx.new_variable(),
            ctx.new_variable(),
            ctx.new_variable(),
        ]);
        ctx.unify(&t, &target).unwrap();
        let _t = t.apply(&ctx);
    })
}

#[bench]
fn instantiate_unify_apply_fast(b: &mut Bencher) {
    b.iter(|| {
        let mut ctx = Context::default();
        let scheme = ptp!(0, 1; @arrow[
            tp!(@arrow[tp!(1), tp!(0), tp!(1)]),
            tp!(1),
            tp!(list(tp!(0))),
            tp!(1),
        ]);
        let mut t = scheme.instantiate_owned(&mut ctx);
        let target = tp!(@arrow[
            tp!(@arrow[tp!(int), tp!(obj), tp!(int)]),
            ctx.new_variable(),
            ctx.new_variable(),
            ctx.new_variable(),
        ]);
        ctx.unify_fast(t.clone(), target).unwrap();
        t.apply_mut(&ctx);
    })
}
