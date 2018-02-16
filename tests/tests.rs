extern crate polytype;

use polytype::*;
use std::collections::HashMap;

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

#[test]
fn test_arrow_macro() {
    assert_eq!(arrow!(Type::Variable(0)), Type::Variable(0));
    assert_eq!(
        arrow!(Type::Variable(0), Type::Variable(1), Type::Variable(2)),
        Type::Arrow(Arrow {
            arg: Box::new(Type::Variable(0)),
            ret: Box::new(Type::Arrow(Arrow {
                arg: Box::new(Type::Variable(1)),
                ret: Box::new(Type::Variable(2)),
            })),
        })
    );
    assert_eq!(
        arrow!(
            Type::Variable(0),
            Type::Variable(1),
            Type::Variable(2),
            Type::Variable(3),
        ),
        Type::Arrow(Arrow {
            arg: Box::new(Type::Variable(0)),
            ret: Box::new(Type::Arrow(Arrow {
                arg: Box::new(Type::Variable(1)),
                ret: Box::new(Type::Arrow(Arrow {
                    arg: Box::new(Type::Variable(2)),
                    ret: Box::new(Type::Variable(3)),
                })),
            })),
        })
    );
}

#[test]
fn test_tp_macro() {
    assert_eq!(tp!(bool), Type::Constructed("bool", vec![]));
    assert_eq!(
        tp!(list(tp!(bool))),
        Type::Constructed("list", vec![Box::new(Type::Constructed("bool", vec![]))]),
    );
    assert_eq!(
        tp!(list(tp!(tuple(tp!(bool), tp!(int))))),
        Type::Constructed(
            "list",
            vec![
                Box::new(Type::Constructed(
                    "tuple",
                    vec![
                        Box::new(Type::Constructed("bool", vec![])),
                        Box::new(Type::Constructed("int", vec![])),
                    ],
                )),
            ]
        ),
    );
    assert_eq!(
        tp!(list(
            tp!(unusually_large_identifier_requiring_wrap),
            tp!(unusually_large_identifier_requiring_wrap),
        )),
        Type::Constructed(
            "list",
            vec![
                Box::new(Type::Constructed(
                    "unusually_large_identifier_requiring_wrap",
                    vec![],
                )),
                Box::new(Type::Constructed(
                    "unusually_large_identifier_requiring_wrap",
                    vec![],
                )),
            ],
        ),
    );
    assert_eq!(tp!(0), Type::Variable(0));
    assert_eq!(
        tp!(hashmap(tp!(str), arrow![tp!(int), tp!(0), tp!(bool)])),
        Type::Constructed(
            "hashmap",
            vec![
                Box::new(Type::Constructed("str", vec![])),
                Box::new(Type::Arrow(Arrow {
                    arg: Box::new(Type::Constructed("int", vec![])),
                    ret: Box::new(Type::Arrow(Arrow {
                        arg: Box::new(Type::Variable(0)),
                        ret: Box::new(Type::Constructed("bool", vec![])),
                    })),
                })),
            ]
        )
    );
}

#[test]
fn test_arrow_methods() {
    let t0 = Type::Variable(0);
    let t1 = Type::Constructed("int", vec![]);
    let t2 = Type::Arrow(Arrow {
        arg: Box::new(t0.clone()),
        ret: Box::new(t1.clone()),
    });
    let ta1 = Type::Arrow(Arrow {
        arg: Box::new(t2.clone()),
        ret: Box::new(Type::Arrow(Arrow {
            arg: Box::new(t1.clone()),
            ret: Box::new(t0.clone()),
        })),
    });
    let ta2 = Arrow {
        arg: Box::new(t2.clone()),
        ret: Box::new(Type::Arrow(Arrow {
            arg: Box::new(t1.clone()),
            ret: Box::new(t0.clone()),
        })),
    }.into();
    let ta3 = arrow![t2.clone(), t1.clone(), t0.clone()];
    let ta4 = arrow![arrow![tp!(0), tp!(int)], tp!(int), tp!(0)];
    assert_eq!(ta4, ta1);
    assert_eq!(ta4, ta2);
    assert_eq!(ta4, ta3);
}

#[test]
fn test_unify_one_side_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(&tp!(list(arrow![tp!(int), tp!(bool)])), &tp!(list(tp!(0))))
        .expect("one side polymorphic");
}

#[test]
fn test_unify_one_side_polymorphic_fail() {
    let mut ctx = Context::default();
    ctx.unify(&arrow![tp!(int), tp!(bool)], &tp!(list(tp!(0))))
        .expect_err("incompatible types");
}

#[test]
fn test_unify_both_sides_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(
        &tp!(list(arrow![tp!(int), tp!(0)])),
        &tp!(list(arrow![tp!(1), tp!(bool)])),
    ).expect("both sides polymorphic");
}

#[test]
fn test_unify_both_sides_polymorphic_occurs() {
    let mut ctx = Context::default();
    ctx.unify(&tp!(0), &tp!(list(arrow![tp!(0), tp!(bool)])))
        .expect_err("circular polymorphic types");
}

#[test]
fn test_instantiate() {
    let mut ctx = Context::default();
    let mut bindings = HashMap::new();
    let dummy = tp!(dummy(tp!(list(tp!(int))), tp!(list(tp!(3)))));
    ctx.unify(&tp!(1), &dummy).expect("unify on empty context");

    let t1 = tp!(list(arrow![tp!(int), tp!(2)])).instantiate(&mut ctx, &mut bindings);
    let t2 = tp!(list(arrow![tp!(2), tp!(bool)])).instantiate(&mut ctx, &mut bindings);
    let t3 = tp!(list(tp!(3))).instantiate(&mut ctx, &mut bindings);

    // type variables start at 0
    assert_eq!(bindings.get(&2).unwrap(), &tp!(0));
    assert_eq!(bindings.get(&3).unwrap(), &tp!(1));
    // like replaces like
    assert_eq!(variables(&t1), variables(&t2));
    // substitutions are not made
    assert_eq!(t3, tp!(list(tp!(1))));
    // context is updated
    assert_eq!(ctx.new_variable(), tp!(2));
    assert_eq!(ctx.substitutions().get(&1).unwrap(), &dummy);
    assert_eq!(ctx.substitutions().len(), 1);
}

#[test]
fn test_canonicalize() {
    let mut bindings = HashMap::new();
    let t1 = tp!(list(arrow![tp!(int), tp!(2)])).canonical(&mut bindings);
    let t2 = tp!(list(arrow![tp!(2), tp!(bool)])).canonical(&mut bindings);
    let t3 = tp!(list(tp!(3))).canonical(&mut bindings);

    // type variables start at 0
    assert_eq!(bindings.get(&2).unwrap(), &tp!(0));
    assert_eq!(bindings.get(&3).unwrap(), &tp!(1));
    // like replaces like
    assert_eq!(variables(&t1), variables(&t2));
    assert_eq!(t3, tp!(list(tp!(1))));
}
