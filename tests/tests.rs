extern crate polytype;

use polytype::*;
use std::collections::{HashMap, VecDeque};

fn find_variables(tp: &Type, o: &mut Vec<u32>) {
    match *tp {
        Type::Arrow(ref arr) => {
            find_variables(&arr.arg, o);
            find_variables(&arr.ret, o)
        }
        Type::Constructed(_, ref args) => for arg in args {
            find_variables(arg, o)
        },
        Type::Variable(v) => o.push(v),
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
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Variable(2),
            })),
        }))
    );
    assert_eq!(
        arrow!(
            Type::Variable(0),
            Type::Variable(1),
            Type::Variable(2),
            Type::Variable(3),
        ),
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Arrow(Box::new(Arrow {
                    arg: Type::Variable(2),
                    ret: Type::Variable(3),
                })),
            })),
        }))
    );
}

#[test]
fn test_tp_macro() {
    assert_eq!(tp!(bool), Type::Constructed("bool", vec![]));
    assert_eq!(
        tp!(list(tp!(bool))),
        Type::Constructed("list", vec![Type::Constructed("bool", vec![])]),
    );
    assert_eq!(
        tp!(list(tp!(tuple(tp!(bool), tp!(int))))),
        Type::Constructed(
            "list",
            vec![
                Type::Constructed(
                    "tuple",
                    vec![
                        Type::Constructed("bool", vec![]),
                        Type::Constructed("int", vec![]),
                    ],
                ),
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
                Type::Constructed("unusually_large_identifier_requiring_wrap", vec![]),
                Type::Constructed("unusually_large_identifier_requiring_wrap", vec![]),
            ],
        ),
    );
    assert_eq!(tp!(0), Type::Variable(0));
    assert_eq!(
        tp!(hashmap(tp!(str), arrow![tp!(int), tp!(0), tp!(bool)])),
        Type::Constructed(
            "hashmap",
            vec![
                Type::Constructed("str", vec![]),
                Type::Arrow(Box::new(Arrow {
                    arg: Type::Constructed("int", vec![]),
                    ret: Type::Arrow(Box::new(Arrow {
                        arg: Type::Variable(0),
                        ret: Type::Constructed("bool", vec![]),
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
    let t2 = Type::Arrow(Box::new(Arrow {
        arg: t0.clone(),
        ret: t1.clone(),
    }));
    let ta1 = Type::Arrow(Box::new(Arrow {
        arg: t2.clone(),
        ret: Type::Arrow(Box::new(Arrow {
            arg: t1.clone(),
            ret: t0.clone(),
        })),
    }));
    let ta2 = Arrow {
        arg: t2.clone(),
        ret: Type::Arrow(Box::new(Arrow {
            arg: t1.clone(),
            ret: t0.clone(),
        })),
    }.into();
    let ta3 = arrow![t2.clone(), t1.clone(), t0.clone()];
    let ta4 = arrow![arrow![tp!(0), tp!(int)], tp!(int), tp!(0)];
    assert_eq!(ta4, ta1);
    assert_eq!(ta4, ta2);
    assert_eq!(ta4, ta3);
}

#[test]
fn test_tp_from_vecdeque() {
    let mut tps = VecDeque::new();
    tps.push_back(Type::Variable(0));
    let tp: Type = tps.clone().into();
    assert_eq!(tp, Type::Variable(0));

    tps.push_back(Type::Variable(1));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Variable(1),
        }))
    );

    tps.push_back(Type::Variable(2));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Variable(2),
            })),
        }))
    );
    tps.push_back(Type::Variable(3));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Arrow(Box::new(Arrow {
                    arg: Type::Variable(2),
                    ret: Type::Variable(3),
                })),
            })),
        }))
    );
}

#[test]
fn test_tp_from_vec() {
    let mut tps = Vec::new();
    tps.push(Type::Variable(0));
    let tp: Type = tps.clone().into();
    assert_eq!(tp, Type::Variable(0));

    tps.push(Type::Variable(1));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Variable(1),
        }))
    );

    tps.push(Type::Variable(2));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Variable(2),
            })),
        }))
    );
    tps.push(Type::Variable(3));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::Arrow(Box::new(Arrow {
            arg: Type::Variable(0),
            ret: Type::Arrow(Box::new(Arrow {
                arg: Type::Variable(1),
                ret: Type::Arrow(Box::new(Arrow {
                    arg: Type::Variable(2),
                    ret: Type::Variable(3),
                })),
            })),
        }))
    );
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
    assert_eq!(&bindings[&2], &tp!(0));
    assert_eq!(&bindings[&3], &tp!(1));
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
    assert_eq!(&bindings[&2], &tp!(0));
    assert_eq!(&bindings[&3], &tp!(1));
    // like replaces like
    assert_eq!(variables(&t1), variables(&t2));
    assert_eq!(t3, tp!(list(tp!(1))));
}

#[test]
fn test_parse() {
    let t = tp!(int);
    assert_eq!(&t, &Type::parse("int").expect("parse 1"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 2"));

    let t = tp!(0);
    assert_eq!(&t, &Type::parse("t0").expect("parse 3"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 4"));

    let t = arrow![tp!(int), tp!(int)];
    assert_eq!(&t, &Type::parse("int -> int").expect("parse 5"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 6"));

    let t = tp!(list(arrow![tp!(int), tp!(2)]));
    assert_eq!(&t, &Type::parse("list(int -> t2)").expect("parse 7"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 8"));

    let t = tp!(hashmap(tp!(str), arrow![tp!(int), tp!(0), tp!(bool)]));
    assert_eq!(
        &t,
        &Type::parse("hashmap(str, int -> t0 -> bool)").expect("parse 9")
    );
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 10"));

    let t = arrow![
        arrow![tp!(1), tp!(0), tp!(1)],
        tp!(1),
        tp!(list(tp!(0))),
        tp!(1),
    ];
    assert_eq!(
        &t,
        &Type::parse("(t1 → t0 → t1) → t1 → list(t0) → t1").expect("parse 11")
    );
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 12"));
}
