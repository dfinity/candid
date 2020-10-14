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

#[derive(CandidType)]
pub struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

#[test]
fn test_func() {
    #[candid_method(query, rename = "TEST")]
    fn test(a: String, b: i32) -> (String, i32) {
        (a, b)
    }

    mod internal {
        use candid::CandidType;
        #[derive(CandidType)]
        pub struct List<T> {
            head: T,
            tail: Option<Box<List<T>>>,
        }
        #[derive(CandidType)]
        pub struct Wrap(List<i8>);
        #[derive(CandidType)]
        pub struct NamedStruct {
            a: u16,
            b: i32,
        }
        #[derive(CandidType)]
        pub enum A {
            A1(super::List<i8>, Box<List<i8>>, Wrap),
            A2(String, candid::Principal),
            A3(candid::Int),
            // This struct happens to have the same candid type as NamedStruct
            A4 { a: u16, b: i32 },
            A5(NamedStruct),
            A6(Box<NamedStruct>),
            A7 { b: i32, c: u16 },
        }
    }

    #[candid_method(query)]
    fn id_struct(_: (List<u8>,)) -> Result<List<u8>, candid::Empty> {
        unreachable!()
    }

    use internal::A;

    #[candid_method]
    fn id_variant(_: &[internal::A]) -> Result<((A,), A), String> {
        unreachable!()
    }

    candid::export_service!();
    println!("{}", __export_service());
    //assert!(false);
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
