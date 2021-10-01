use polytype::*;

#[test]
fn test_tp_macro() {
    with_ctx(1024, |ctx: TypeContext<'_>| {
        assert_eq!(tp!(ctx, bool), &Type::Constructed(&"bool", &[]));
        assert_eq!(
            tp!(ctx, list(tp!(ctx, bool))),
            &Type::Constructed(&"list", &[&Type::Constructed(&"bool", &[])]),
        );
        assert_eq!(
            tp!(ctx, list(tp!(ctx, tuple(tp!(ctx, bool), tp!(ctx, int))))),
            &Type::Constructed(
                &"list",
                &[&Type::Constructed(
                    &"tuple",
                    &[
                        &Type::Constructed(&"bool", &[]),
                        &Type::Constructed(&"int", &[]),
                    ],
                )],
            ),
        );
        assert_eq!(
            tp!(
                ctx,
                list(
                    tp!(ctx, unusually_large_identifier_requiring_wrap),
                    tp!(ctx, unusually_large_identifier_requiring_wrap),
                )
            ),
            &Type::Constructed(
                &"list",
                &[
                    &Type::Constructed(&"unusually_large_identifier_requiring_wrap", &[]),
                    &Type::Constructed(&"unusually_large_identifier_requiring_wrap", &[]),
                ],
            ),
        );
        assert_eq!(tp!(ctx, 0), &Type::Variable(Variable(0)));
        assert_eq!(
            tp!(
                ctx,
                hashmap(
                    tp!(ctx, str),
                    tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, 0), tp!(ctx, bool)])
                )
            ),
            &Type::Constructed(
                &"hashmap",
                &[
                    &Type::Constructed(&"str", &[]),
                    ctx.arrow(
                        &Type::Constructed(&"int", &[]),
                        ctx.arrow(
                            &Type::Variable(Variable(0)),
                            &Type::Constructed(&"bool", &[])
                        ),
                    ),
                ],
            )
        );
        // arrows
        assert_eq!(tp!(ctx, @arrow[tp!(ctx, 0)]), &Type::Variable(Variable(0)));
        let arg = &Type::Variable(Variable(0));
        let ret = &Type::Variable(Variable(1));
        let t = tp!(ctx, @arrow[arg, ret]);
        assert_eq!(
            t,
            tp!(ctx, @arrow[&Type::Variable(Variable(0)), &Type::Variable(Variable(1))])
        );
        assert_eq!(
            tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, 1), tp!(ctx, 2)]),
            ctx.arrow(
                &Type::Variable(Variable(0)),
                ctx.arrow(&Type::Variable(Variable(1)), &Type::Variable(Variable(2))),
            )
        );
        assert_eq!(
            tp!(ctx, @arrow[
                tp!(ctx, 0),
                tp!(ctx, 1),
                tp!(ctx, 2),
                tp!(ctx, 3),
            ]),
            ctx.arrow(
                &Type::Variable(Variable(0)),
                ctx.arrow(
                    &Type::Variable(Variable(1)),
                    ctx.arrow(&Type::Variable(Variable(2)), &Type::Variable(Variable(3))),
                ),
            )
        );
    })
}

#[test]
fn test_ptp_macro() {
    with_ctx(1024, |ctx| {
        assert_eq!(
            ptp!(ctx, bool),
            &TypeSchema::Monotype(&Type::Constructed(&"bool", &[]))
        );
        assert_eq!(
            ptp!(ctx, list(tp!(ctx, bool))),
            &TypeSchema::Monotype(&Type::Constructed(
                &"list",
                &[&Type::Constructed(&"bool", &[])],
            ))
        );
        assert_eq!(
            ptp!(ctx, 0; 0),
            &TypeSchema::Polytype(
                Variable(0),
                &TypeSchema::Monotype(&Type::Variable(Variable(0))),
            )
        );
        assert_eq!(
            ptp!(ctx, 0; @arrow[tp!(ctx, 0), tp!(ctx, 0)]),
            &TypeSchema::Polytype(
                Variable(0),
                &TypeSchema::Monotype(&Type::Constructed(
                    &"→",
                    &[&Type::Variable(Variable(0)), &Type::Variable(Variable(0))],
                )),
            )
        );
    })
}

#[test]
fn test_arrow_methods() {
    with_ctx(1024, |ctx| {
        let t0 = &Type::Variable(Variable(0));
        let t1 = &Type::Constructed(&"int", &[]);
        let t2 = ctx.arrow(t0, t1);
        let ta1 = ctx.arrow(t2, ctx.arrow(t1, t0));
        let ta2 = tp!(ctx, @arrow[t2, t1, t0]);
        let ta3 = tp!(ctx, @arrow[tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, int)]), tp!(ctx, int), tp!(ctx, 0)]);
        assert_eq!(ta3, ta1);
        assert_eq!(ta3, ta2);
        let t = tp!(ctx, @arrow[tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, int)]), tp!(ctx, int), tp!(ctx, 0)]);
        assert_eq!(
            t.args(),
            Some(Vec::from(vec![
                tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, int)]),
                tp!(ctx, int),
            ])),
        );
        assert_eq!(t.returns(), Some(tp!(ctx, 0)));
    })
}

#[test]
fn test_unify_one_side_polymorphic() {
    with_ctx(1024, |ctx| {
        Type::unify(
            &[(
                tp!(ctx, list(tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, bool)]))),
                tp!(ctx, list(tp!(ctx, 0))),
            )],
            &ctx,
        )
        .expect("one side polymorphic");
    })
}

#[test]
fn test_unify_one_side_polymorphic_fail() {
    with_ctx(1024, |ctx| {
        Type::unify(
            &[(
                tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, bool)]),
                tp!(ctx, list(tp!(ctx, 0))),
            )],
            &ctx,
        )
        .expect_err("incompatible types");
    })
}

#[test]
fn test_unify_both_sides_polymorphic() {
    with_ctx(1024, |ctx| {
        Type::unify(
            &[(
                tp!(ctx, list(tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, 0)]))),
                tp!(ctx, list(tp!(ctx, @arrow[tp!(ctx, 1), tp!(ctx, bool)]))),
            )],
            &ctx,
        )
        .expect("both sides polymorphic");
    })
}

#[test]
fn test_unify_both_sides_polymorphic_occurs() {
    with_ctx(1024, |ctx| {
        Type::unify(
            &[(
                tp!(ctx, 0),
                tp!(ctx, list(tp!(ctx, @arrow[tp!(ctx, 0), tp!(ctx, bool)]))),
            )],
            &ctx,
        )
        .expect_err("circular polymorphic types");
    })
}

#[test]
fn test_unify_nonstring_name() {
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct N(u32);
    struct ParseError;
    impl Name for N {
        type ParseError = ParseError;
        fn arrow() -> Self {
            N(0)
        }
        fn parse(s: &str) -> Result<Self, Self::ParseError> {
            match s.parse::<u32>() {
                Ok(n) => Ok(N(n)),
                Err(_) => Err(ParseError),
            }
        }
    }

    with_ctx(1024, |ctx| {
        let mut src = Source::default();

        let ts = TypeSchema::Polytype(
            Variable(0),
            &TypeSchema::Monotype(&Type::Constructed(&N(3), &[&Type::Variable(Variable(0))])),
        );

        let t = ts.instantiate(&ctx, &mut src);
        let t_n1 = ctx.intern_name(N(1));
        let t_n2 = ctx.intern_name(N(2));
        let t_n3 = ctx.intern_name(N(3));
        let t_con1 = ctx.intern_tcon(t_n1, &[]);
        let t_con2 = ctx.intern_tcon(t_n2, &[]);
        let t_arrow = ctx.arrow(t_con1, t_con2);
        let t_test = ctx.intern_tcon(t_n3, &[t_arrow]);
        Type::unify(&[(t_test, t)], &ctx).expect("nonstring one side polymorphic");

        let t = ts.instantiate(&ctx, &mut src);
        let t_test = ctx.arrow(
            &Type::Constructed(&N(1), &[]),
            &Type::Constructed(&N(2), &[]),
        );
        Type::unify(&[(t, t_test)], &ctx).expect_err("nonstring incompatible types");
    })
}

#[test]
fn test_merge_no_sacreds() {
    with_ctx(1024, |ctx| {
        let mut src = Source::default();
        let a = src.fresh();
        let b = src.fresh();
        let _ = src.fresh();
        let ta = ctx.intern_tvar(Variable(a));
        let tb = ctx.intern_tvar(Variable(b));
        let t1 = ctx.arrow(ta, tb);
        let t2 = tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, bool)]);
        let sub1 = Type::unify(&[(t1, t2)], &ctx).unwrap();

        let mut src2 = Source::default();
        let _ = src2.fresh();
        let pt = ptp!(ctx, 0, 1; @arrow[tp!(ctx, 0), tp!(ctx, 1)]);
        let t = pt.instantiate(&ctx, &mut src2);
        let last = ctx.intern_tvar(Variable(src2.fresh()));
        let mut sub2 = Substitution::with_capacity(ctx, 32);
        sub2.add(Variable(2), tp!(ctx, bool));
        assert_eq!(t.apply(&sub2).to_string(), "t1 → bool");

        let src_change = src.merge(src2, vec![]);
        let t_reified = src_change.reify_type(t, &ctx);
        assert_eq!(t_reified.to_string(), "t4 → t5");
        src_change.reify_substitution(&mut sub2, &ctx);
        assert_eq!(t_reified.apply(&sub2).apply(&sub1).to_string(), "t4 → bool");
        let last_reified = src_change.reify_type(last, &ctx);
        assert_eq!(last_reified, tp!(ctx, 6));
        assert_eq!(src.fresh(), 7);
    })
}

#[test]
fn test_merge_with_sacreds() {
    with_ctx(1024, |ctx| {
        let mut src = Source::default();
        let a = src.fresh();
        let b = src.fresh();
        let _ = src.fresh();
        let ta = ctx.intern_tvar(Variable(a));
        let tb = ctx.intern_tvar(Variable(b));
        let t1 = ctx.arrow(ta, tb);
        let t2 = tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, bool)]);
        let sub1 = Type::unify(&[(t1, t2)], &ctx).unwrap();

        let mut src2 = Source::default();
        let _ = src2.fresh();
        let pt = ptp!(ctx, 0, 1; @arrow[tp!(ctx, 0), tp!(ctx, 1)]);
        let t = pt.instantiate(&ctx, &mut src2);
        let last = ctx.intern_tvar(Variable(src2.fresh()));
        let mut sub2 = Substitution::with_capacity(ctx, 32);
        sub2.add(Variable(2), tp!(ctx, bool));
        assert_eq!(t.apply(&sub2).to_string(), "t1 → bool");

        let src_change = src.merge(src2, vec![Variable(0), Variable(1)]);
        let t_reified = src_change.reify_type(t, &ctx);
        assert_eq!(t_reified.to_string(), "t1 → t5");
        src_change.reify_substitution(&mut sub2, &ctx);
        assert_eq!(
            t_reified.apply(&sub2).apply(&sub1).to_string(),
            "bool → bool"
        );
        let last_reified = src_change.reify_type(last, &ctx);
        assert_eq!(last_reified, tp!(ctx, 6));
        assert_eq!(src.fresh(), 7);
    })
}

#[cfg(feature = "parser")]
#[test]
fn test_parse() {
    with_ctx(1024, |ctx| {
        let t = tp!(ctx, int);
        assert_eq!(&t, &Type::parse(&ctx, "int").expect("parse 1"));
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 2"));

        let t = tp!(ctx, 0);
        assert_eq!(&t, &Type::parse(&ctx, "t0").expect("parse 3"));
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 4"));

        let t = tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, int)]);
        assert_eq!(&t, &Type::parse(&ctx, "int -> int").expect("parse 5"));
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 6"));

        let t = tp!(ctx, list(tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, 2)])));
        assert_eq!(&t, &Type::parse(&ctx, "list(int -> t2)").expect("parse 7"));
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 8"));

        let t = tp!(
            ctx,
            hashmap(
                tp!(ctx, str),
                tp!(ctx, @arrow[tp!(ctx, int), tp!(ctx, 0), tp!(ctx, bool)])
            )
        );
        assert_eq!(
            &t,
            &Type::parse(&ctx, "hashmap(str, int -> t0 -> bool)").expect("parse 9")
        );
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 10"));

        let t = tp!(ctx, @arrow[
            tp!(ctx, @arrow[tp!(ctx, 1), tp!(ctx, 0), tp!(ctx, 1)]),
            tp!(ctx, 1),
            tp!(ctx, list(tp!(ctx, 0))),
            tp!(ctx, 1),
        ]);
        assert_eq!(
            &t,
            &Type::parse(&ctx, "(t1 → t0 → t1) → t1 → list(t0) → t1").expect("parse 11")
        );
        assert_eq!(t, Type::parse(&ctx, &t.to_string()).expect("parse 12"));
    })
}
