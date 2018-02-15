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
fn test_arrow_macro() {
    arrow!(Type::Variable(0));
    arrow!(Type::Variable(0), Type::Variable(1), Type::Variable(2));
    arrow!(
        Type::Variable(0),
        Type::Variable(1),
        Type::Variable(2),
        Type::Variable(3),
    );
}
#[test]
fn test_arrow_methods() {
    let t0 = Type::Variable(0);
    let t1 = Type::Constructed("int", vec![]);
    let t2 = Type::Arrow(Arrow::new(t0.clone(), t1.clone()));
    let ta1 = Type::Arrow(Arrow::new(
        t2.clone(),
        Type::Arrow(Arrow::new(t1.clone(), t0.clone())),
    ));
    let ta2 = Type::Arrow(Arrow {
        arg: Box::new(t2.clone()),
        ret: Box::new(Type::Arrow(Arrow {
            arg: Box::new(t1.clone()),
            ret: Box::new(t0.clone()),
        })),
    });
    let ta3 = Arrow::new(t2.clone(), Type::Arrow(Arrow::new(t1.clone(), t0.clone()))).into();
    let ta4 = Arrow {
        arg: Box::new(t2.clone()),
        ret: Box::new(Type::Arrow(Arrow {
            arg: Box::new(t1.clone()),
            ret: Box::new(t0.clone()),
        })),
    }.into();
    let ta5 = arrow![t2.clone(), t1.clone(), t0.clone()];
    assert_eq!(ta5, ta1);
    assert_eq!(ta5, ta2);
    assert_eq!(ta5, ta3);
    assert_eq!(ta5, ta4);
}
#[test]
fn test_unify_one_side_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(
        &tlist(Arrow::new(tint(), tbool()).into()),
        &tlist(Type::Variable(0)),
    ).expect("one side polymorphic");
}
#[test]
fn test_unify_one_side_polymorphic_fail() {
    let mut ctx = Context::default();
    ctx.unify(
        &Arrow::new(tint(), tbool()).into(),
        &tlist(Type::Variable(0)),
    ).expect_err("incompatible types");
}
#[test]
fn test_unify_both_sides_polymorphic() {
    let mut ctx = Context::default();
    ctx.unify(
        &tlist(Arrow::new(tint(), Type::Variable(0)).into()),
        &tlist(Arrow::new(Type::Variable(1), tbool()).into()),
    ).expect("both sides polymorphic");
}
#[test]
fn test_unify_both_sides_polymorphic_occurs() {
    let mut ctx = Context::default();
    ctx.unify(
        &tlist(Arrow::new(tint(), Type::Variable(0)).into()),
        &tlist(Arrow::new(Type::Variable(0), tbool()).into()),
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
    ctx.unify(&Type::Variable(1), &dummy)
        .expect("unify on empty context");

    let t1 =
        tlist(Arrow::new(tint(), Type::Variable(2)).into()).instantiate(&mut ctx, &mut bindings);
    let t2 =
        tlist(Arrow::new(Type::Variable(2), tbool()).into()).instantiate(&mut ctx, &mut bindings);
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
    assert_eq!(ctx.new_variable(), Type::Variable(2));
    assert_eq!(ctx.substitutions().get(&1).unwrap(), &dummy);
    assert_eq!(ctx.substitutions().len(), 1);
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
