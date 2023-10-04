#![allow(dead_code)]

use std::fmt::Debug;

use candid::{
    candid_method, field,
    ser::IDLBuilder,
    types::value::{IDLValue, IDLValueVisitor},
    types::{get_type, Serializer, Type, TypeInner},
    CandidType, Decode, Deserialize, Encode, Int,
};
use serde::de::DeserializeOwned;

#[test]
fn any_val() {
    fn test_embed<T: DeserializeOwned + Debug + CandidType + PartialEq>(value: T) -> IDLValue {
        #[derive(Debug, Clone, PartialEq)]
        struct IDLValueEmbed(IDLValue);
        impl CandidType for IDLValueEmbed {
            fn _ty() -> Type {
                TypeInner::Reserved.into()
            }
            fn idl_serialize<S: Serializer>(&self, _serializer: S) -> Result<(), S::Error> {
                unimplemented!("IDLValueEmbed is not serializable")
            }
        }
        impl<'de> Deserialize<'de> for IDLValueEmbed {
            fn deserialize<D: serde::de::Deserializer<'de>>(
                deserializer: D,
            ) -> Result<Self, D::Error> {
                deserializer
                    .deserialize_ignored_any(IDLValueVisitor)
                    .map(IDLValueEmbed)
            }
        }

        #[derive(Debug, Clone, PartialEq, Eq, CandidType, Deserialize)]
        struct Embed<T> {
            value: T,
        }

        let orig = Embed { value };
        let bytes1 = Encode!(&orig).unwrap();

        let idl_value = Decode!(&bytes1, Embed<IDLValueEmbed>).unwrap();
        let bytes2 = IDLBuilder::new()
            .value_arg(&idl_value.value.0)
            .unwrap()
            .serialize_to_vec()
            .unwrap();
        let new = Decode!(&bytes2, T).unwrap();
        assert_eq!(orig.value, new);
        idl_value.value.0
    }

    #[derive(Debug, Clone, PartialEq, Eq, CandidType, Deserialize)]
    enum E {
        Foo,
        Bar(bool, i32),
        Baz { a: i32, b: u32 },
        Newtype(bool),
    }
    #[derive(Debug, Clone, PartialEq, Eq, CandidType, Deserialize)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }

    let v = test_embed(E::Foo);
    assert!(matches!(v, IDLValue::Variant(_)));

    let v = test_embed(E::Bar(true, 42));
    assert!(matches!(v, IDLValue::Variant(_)));

    let v = test_embed(G {
        g1: E::Bar(true, 42),
        g2: G {
            g1: E::Baz { a: -199, b: 14 },
            g2: E::Newtype(false),
        },
    });
    assert!(matches!(v, IDLValue::Record(_)));
}

#[test]
fn test_primitive() {
    assert_eq!(get_type(&true), TypeInner::Bool.into());
    assert_eq!(get_type(&Box::new(42)), TypeInner::Int32.into());
    assert_eq!(get_type(&Box::new(Int::from(42))), TypeInner::Int.into());
    let opt: Option<&str> = None;
    assert_eq!(
        get_type(&opt),
        TypeInner::Opt(TypeInner::Text.into()).into()
    );
    assert_eq!(
        get_type(&[0, 1, 2, 3]),
        TypeInner::Vec(TypeInner::Int32.into()).into()
    );
}

#[test]
fn test_struct() {
    #[derive(Debug, CandidType)]
    struct Newtype(Int);
    assert_eq!(Newtype::ty(), TypeInner::Int.into());
    #[derive(Debug, CandidType)]
    struct A {
        foo: Int,
        bar: bool,
    }
    assert_eq!(
        A::ty(),
        TypeInner::Record(vec![
            field! {bar: TypeInner::Bool.into()},
            field! {foo: TypeInner::Int.into()}
        ])
        .into()
    );

    #[derive(Debug, CandidType)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }
    let res = G { g1: 42, g2: true };
    assert_eq!(
        get_type(&res),
        TypeInner::Record(vec![
            field! {g1: TypeInner::Int32.into()},
            field! {g2: TypeInner::Bool.into()}
        ])
        .into()
    );

    #[derive(Debug, CandidType)]
    struct List {
        head: i32,
        tail: Option<Box<List>>,
    }
    assert_eq!(
        List::ty(),
        TypeInner::Record(vec![
            field!{head: TypeInner::Int32.into()},
            field!{tail: TypeInner::Opt(TypeInner::Knot(candid::types::TypeId::of::<List>()).into()).into()}
        ])
        .into()
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
        TypeInner::Variant(vec![
            field! {Bar:
                TypeInner::Record(vec![
                    field!{0: TypeInner::Bool.into()},
                    field!{1: TypeInner::Int32.into()}
                ])
                .into()
            },
            field! {
                Baz:
                TypeInner::Record(vec![
                    field!{a: TypeInner::Int32.into()},
                    field!{b: TypeInner::Nat32.into()}
                ])
                .into()
            },
            field! {Foo: TypeInner::Null.into()},
            field! {Newtype: TypeInner::Bool.into()},
        ])
        .into()
    );
}

#[derive(CandidType)]
pub struct List<T> {
    head: T,
    tail: Option<Box<List<T>>>,
}

#[test]
fn test_func() {
    #[candid_method(query, rename = "🐂")]
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
    use internal::A;
    #[candid::candid_method]
    fn id_variant(_: &[internal::A]) -> Result<((A,), A), String> {
        unreachable!()
    }
    #[candid_method(oneway)]
    fn oneway(_: &str) {
        unreachable!()
    }

    #[candid_method(query)]
    fn id_struct(_: (List<u8>,)) -> Result<List<u8>, candid::Empty> {
        unreachable!()
    }
    #[candid_method(composite_query)]
    fn id_struct_composite(_: (List<u8>,)) -> Result<List<u8>, candid::Empty> {
        unreachable!()
    }

    #[candid_method(init)]
    fn init(_: List<i128>) {}

    candid::export_service!();
    let expected = r#"type A = variant {
  A1 : record { List_1; Wrap; Wrap };
  A2 : record { text; principal };
  A3 : int;
  A4 : NamedStruct;
  A5 : NamedStruct;
  A6 : NamedStruct;
  A7 : record { b : int32; c : nat16 };
};
type Box = record { head : int8; tail : opt Box };
type List = record { head : nat8; tail : opt List };
type List_1 = record { head : int8; tail : opt List_1 };
type List_2 = record { head : int; tail : opt List_2 };
type NamedStruct = record { a : nat16; b : int32 };
type Result = variant { Ok : List; Err : empty };
type Result_1 = variant { Ok : record { record { A }; A }; Err : text };
type Wrap = record { head : int8; tail : opt Box };
service : (List_2) -> {
  id_struct : (record { List }) -> (Result) query;
  id_struct_composite : (record { List }) -> (Result) composite_query;
  id_variant : (vec A) -> (Result_1);
  "oneway" : (text) -> () oneway;
  "🐂" : (text, int32) -> (text, int32) query;
}"#;
    assert_eq!(expected, __export_service());
    //println!("{}", __export_service());
    //assert!(false);
}

#[test]
fn test_counter() {
    struct Service {
        counter: usize,
    }
    impl Service {
        fn init() -> Self {
            Service { counter: 0 }
        }
        #[candid_method]
        fn inc(&mut self) {
            self.counter += 1;
        }
        #[candid_method(query)]
        fn read(&self) -> usize {
            self.counter
        }
    }
    candid::export_service!();
    let expected = "service : { inc : () -> (); read : () -> (nat64) query }";
    assert_eq!(expected, __export_service());
}
