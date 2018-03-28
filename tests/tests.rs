extern crate polytype;

use polytype::*;
use std::collections::VecDeque;

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
        tp!(hashmap(tp!(str), tp!(@arrow[tp!(int), tp!(0), tp!(bool)]))),
        Type::Constructed(
            "hashmap",
            vec![
                Type::Constructed("str", vec![]),
                Type::arrow(
                    Type::Constructed("int", vec![]),
                    Type::arrow(Type::Variable(0), Type::Constructed("bool", vec![])),
                ),
            ]
        )
    );
    // arrows
    assert_eq!(tp!(@arrow[Type::Variable(0)]), Type::Variable(0));
    let arg = Type::Variable(0);
    let ret = Type::Variable(1);
    let t = tp!(@arrow[arg, ret]);
    assert_eq!(t, tp!(@arrow[Type::Variable(0), Type::Variable(1)]));
    assert_eq!(
        tp!(@arrow[Type::Variable(0), Type::Variable(1), Type::Variable(2)]),
        Type::arrow(
            Type::Variable(0),
            Type::arrow(Type::Variable(1), Type::Variable(2))
        )
    );
    assert_eq!(
        tp!(@arrow[
            Type::Variable(0),
            Type::Variable(1),
            Type::Variable(2),
            Type::Variable(3),
        ]),
        Type::arrow(
            Type::Variable(0),
            Type::arrow(
                Type::Variable(1),
                Type::arrow(Type::Variable(2), Type::Variable(3))
            )
        )
    );
}

#[test]
fn test_ptp_macro() {
    assert_eq!(
        ptp!(bool),
        TypeSchema::Monotype(Type::Constructed("bool", vec![]))
    );
    assert_eq!(
        ptp!(list(tp!(bool))),
        TypeSchema::Monotype(Type::Constructed(
            "list",
            vec![Type::Constructed("bool", vec![])]
        ))
    );
    assert_eq!(
        ptp!(0; 0),
        TypeSchema::Polytype {
            variable: 0,
            body: Box::new(TypeSchema::Monotype(Type::Variable(0))),
        }
    );
    assert_eq!(
        ptp!(0; @arrow[tp!(0), tp!(0)]),
        TypeSchema::Polytype {
            variable: 0,
            body: Box::new(TypeSchema::Monotype(Type::Constructed(
                "→",
                vec![Type::Variable(0), Type::Variable(0)]
            ))),
        }
    );
}

#[test]
fn test_arrow_methods() {
    let t0 = Type::Variable(0);
    let t1 = Type::Constructed("int", vec![]);
    let t2 = Type::arrow(t0.clone(), t1.clone());
    let ta1 = Type::arrow(t2.clone(), Type::arrow(t1.clone(), t0.clone()));
    let ta2 = tp!(@arrow[t2.clone(), t1.clone(), t0.clone()]);
    let ta3 = tp!(@arrow[tp!(@arrow[tp!(0), tp!(int)]), tp!(int), tp!(0)]);
    assert_eq!(ta3, ta1);
    assert_eq!(ta3, ta2);
}

#[test]
fn test_tp_from_vecdeque() {
    let mut tps = VecDeque::new();
    tps.push_back(Type::Variable(0));
    let tp: Type = tps.clone().into();
    assert_eq!(tp, Type::Variable(0));

    tps.push_back(Type::Variable(1));
    let tp: Type = tps.clone().into();
    assert_eq!(tp, Type::arrow(Type::Variable(0), Type::Variable(1)));

    tps.push_back(Type::Variable(2));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::arrow(
            Type::Variable(0),
            Type::arrow(Type::Variable(1), Type::Variable(2))
        )
    );
    tps.push_back(Type::Variable(3));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::arrow(
            Type::Variable(0),
            Type::arrow(
                Type::Variable(1),
                Type::arrow(Type::Variable(2), Type::Variable(3))
            )
        )
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
    assert_eq!(tp, Type::arrow(Type::Variable(0), Type::Variable(1)));

    tps.push(Type::Variable(2));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::arrow(
            Type::Variable(0),
            Type::arrow(Type::Variable(1), Type::Variable(2))
        )
    );
    tps.push(Type::Variable(3));
    let tp: Type = tps.clone().into();
    assert_eq!(
        tp,
        Type::arrow(
            Type::Variable(0),
            Type::arrow(
                Type::Variable(1),
                Type::arrow(Type::Variable(2), Type::Variable(3))
            )
        )
    );
}

#[test]
fn test_unify_one_side_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(
        &tp!(list(tp!(@arrow[tp!(int), tp!(bool)]))),
        &tp!(list(tp!(0))),
    ).expect("one side polymorphic");
}

#[test]
fn test_unify_one_side_polymorphic_fail() {
    let mut ctx = Context::default();
    ctx.unify(&tp!(@arrow[tp!(int), tp!(bool)]), &tp!(list(tp!(0))))
        .expect_err("incompatible types");
}

#[test]
fn test_unify_both_sides_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(
        &tp!(list(tp!(@arrow[tp!(int), tp!(0)]))),
        &tp!(list(tp!(@arrow[tp!(1), tp!(bool)]))),
    ).expect("both sides polymorphic");
}

#[test]
fn test_unify_both_sides_polymorphic_occurs() {
    let mut ctx = Context::default();
    ctx.unify(&tp!(0), &tp!(list(tp!(@arrow[tp!(0), tp!(bool)]))))
        .expect_err("circular polymorphic types");
}

#[test]
fn test_parse() {
    let t = tp!(int);
    assert_eq!(&t, &Type::parse("int").expect("parse 1"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 2"));

    let t = tp!(0);
    assert_eq!(&t, &Type::parse("t0").expect("parse 3"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 4"));

    let t = tp!(@arrow[tp!(int), tp!(int)]);
    assert_eq!(&t, &Type::parse("int -> int").expect("parse 5"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 6"));

    let t = tp!(list(tp!(@arrow[tp!(int), tp!(2)])));
    assert_eq!(&t, &Type::parse("list(int -> t2)").expect("parse 7"));
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 8"));

    let t = tp!(hashmap(tp!(str), tp!(@arrow[tp!(int), tp!(0), tp!(bool)])));
    assert_eq!(
        &t,
        &Type::parse("hashmap(str, int -> t0 -> bool)").expect("parse 9")
    );
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 10"));

    let t = tp!(@arrow[
        tp!(@arrow[tp!(1), tp!(0), tp!(1)]),
        tp!(1),
        tp!(list(tp!(0))),
        tp!(1),
    ]);
    assert_eq!(
        &t,
        &Type::parse("(t1 → t0 → t1) → t1 → list(t0) → t1").expect("parse 11")
    );
    assert_eq!(t, Type::parse(&format!("{}", t)).expect("parse 12"));
}
