#![allow(dead_code)]

use candid::types::{get_type, Label, Type};
use candid::{candid_method, CandidType, Int};

#[test]
fn test_primitive() {
    assert_eq!(get_type(&true), Type::Bool);
    assert_eq!(get_type(&Box::new(42)), Type::Int32);
    assert_eq!(get_type(&Box::new(Int::from(42))), Type::Int);
    let opt: Option<&str> = None;
    assert_eq!(get_type(&opt), Type::Opt(Box::new(Type::Text)));
    assert_eq!(get_type(&[0, 1, 2, 3]), Type::Vec(Box::new(Type::Int32)));
}

#[test]
fn test_struct() {
    #[derive(Debug, CandidType)]
    struct Newtype(Int);
    assert_eq!(Newtype::ty(), Type::Int,);
    #[derive(Debug, CandidType)]
    struct A {
        foo: Int,
        bar: bool,
    }
    assert_eq!(
        A::ty(),
        Type::Record(vec![field("bar", Type::Bool), field("foo", Type::Int),])
    );

    #[derive(Debug, CandidType)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }
    let res = G { g1: 42, g2: true };
    assert_eq!(
        get_type(&res),
        Type::Record(vec![field("g1", Type::Int32), field("g2", Type::Bool)])
    );

    #[derive(Debug, CandidType)]
    struct List {
        head: i32,
        tail: Option<Box<List>>,
    }
    assert_eq!(
        List::ty(),
        Type::Record(vec![
            field("head", Type::Int32),
            field(
                "tail",
                Type::Opt(Box::new(Type::Knot(candid::types::TypeId::of::<List>())))
            )
        ])
    );
}

#[test]
fn test_variant() {
    #[allow(dead_code)]
    #[derive(Debug, CandidType)]
    enum E {
        Foo,
        Bar(bool, i32),
        Baz { a: i32, b: u32 },
        Newtype(bool),
    }

    let v = E::Bar(true, 42);
    assert_eq!(
        get_type(&v),
        Type::Variant(vec![
            field(
                "Bar",
                Type::Record(vec![
                    unnamed_field(0, Type::Bool),
                    unnamed_field(1, Type::Int32)
                ])
            ),
            field(
                "Baz",
                Type::Record(vec![field("a", Type::Int32), field("b", Type::Nat32)])
            ),
            field("Foo", Type::Null),
            field("Newtype", Type::Bool),
        ])
    );
}

#[test]
fn test_func() {
    #[candid_method(query, rename = "TEST")]
    fn test(a: String, b: i32) -> (String, i32) {
        (a, b)
    }
    #[derive(CandidType)]
    struct List {
        head: i8,
        tail: Box<List>,
    }

    #[derive(CandidType)]
    enum A {
        A1(u16),
        A2(List),
        A3(String, candid::Principal),
    }

    #[candid_method(query)]
    fn id_struct(a: (List,)) -> List {
        a.0
    }

    #[candid_method]
    fn id_variant(a: A) -> A {
        a
    }

    candid::export_service!();
    println!("{}", export_service());
    assert!(false);
}

fn field(id: &str, ty: Type) -> candid::types::Field {
    candid::types::Field {
        id: Label::Named(id.to_string()),
        ty,
    }
}

fn unnamed_field(id: u32, ty: Type) -> candid::types::Field {
    candid::types::Field {
        id: Label::Id(id),
        ty,
    }
}
