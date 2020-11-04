use super::internal::*;
use super::{CandidType, Compound, Serializer};

macro_rules! primitive_impl {
    ($t:ty, $id:tt, $method:ident $($cast:tt)*) => {
        impl CandidType for $t {
            fn id() -> TypeId { TypeId::of::<$t>() }
            fn _ty() -> Type { Type::$id }
            fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error> where S: Serializer {
                serializer.$method(*self $($cast)*)
            }
        }
    };
}

primitive_impl!(&str, Text, serialize_text);
primitive_impl!((), Null, serialize_null);
primitive_impl!(bool, Bool, serialize_bool);

primitive_impl!(i8, Int8, serialize_int8);
primitive_impl!(i16, Int16, serialize_int16);
primitive_impl!(i32, Int32, serialize_int32);
primitive_impl!(i64, Int64, serialize_int64);

primitive_impl!(u8, Nat8, serialize_nat8);
primitive_impl!(u16, Nat16, serialize_nat16);
primitive_impl!(u32, Nat32, serialize_nat32);
primitive_impl!(u64, Nat64, serialize_nat64);

primitive_impl!(f32, Float32, serialize_float32);
primitive_impl!(f64, Float64, serialize_float64);

// isize, usize always encode to 64bit to ensure the same behavior
// on different platforms. This is consistent with serde's convention
primitive_impl!(isize, Int64, serialize_int64 as i64);
primitive_impl!(usize, Nat64, serialize_nat64 as u64);

impl CandidType for String {
    fn id() -> TypeId {
        TypeId::of::<String>()
    }
    fn _ty() -> Type {
        Type::Text
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_text(self)
    }
}

impl<T: Sized> CandidType for Option<T>
where
    T: CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<Option<T>>()
    }
    fn _ty() -> Type {
        Type::Opt(Box::new(T::ty()))
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_option(self.as_ref())
    }
}

impl<T> CandidType for Vec<T>
where
    T: CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<Vec<T>>()
    }
    fn _ty() -> Type {
        Type::Vec(Box::new(T::ty()))
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        let mut ser = serializer.serialize_vec(self.len())?;
        for e in self.iter() {
            Compound::serialize_element(&mut ser, &e)?;
        }
        Ok(())
    }
}

impl<T> CandidType for [T]
where
    T: CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<[T]>()
    }
    fn _ty() -> Type {
        Type::Vec(Box::new(T::ty()))
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        let mut ser = serializer.serialize_vec(self.len())?;
        for e in self.iter() {
            Compound::serialize_element(&mut ser, &e)?;
        }
        Ok(())
    }
}

macro_rules! array_impls {
    ($($len:tt)+) => {
        $(
            impl<T> CandidType for [T; $len]
            where T: CandidType,
            {
                fn id() -> TypeId { TypeId::of::<[T; $len]>() }
                fn _ty() -> Type { Type::Vec(Box::new(T::ty())) }
                fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
                where S: Serializer,
                {
                    let mut ser = serializer.serialize_vec($len)?;
                    for e in self.iter() {
                        Compound::serialize_element(&mut ser, &e)?;
                    };
                    Ok(())
                }
            }
        )+
    }
}

array_impls! {
     1  2  3  4  5  6  7  8  9 10
    11 12 13 14 15 16 17 18 19 20
    21 22 23 24 25 26 27 28 29 30
    31 32 00
}

impl<T, E> CandidType for Result<T, E>
where
    T: CandidType,
    E: CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<Result<T, E>>()
    }
    fn _ty() -> Type {
        Type::Variant(vec![
            // Make sure the field id is sorted by idl_hash
            Field {
                id: Label::Named("Ok".to_owned()),
                ty: T::ty(),
            },
            Field {
                id: Label::Named("Err".to_owned()),
                ty: E::ty(),
            },
        ])
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        match *self {
            Result::Ok(ref v) => {
                let mut ser = serializer.serialize_variant(0)?;
                Compound::serialize_element(&mut ser, v)
            }
            Result::Err(ref e) => {
                let mut ser = serializer.serialize_variant(1)?;
                Compound::serialize_element(&mut ser, e)
            }
        }
    }
}

impl<T> CandidType for Box<T>
where
    T: ?Sized + CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<Box<T>>()
    }
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        (**self).idl_serialize(serializer)
    }
}

impl<'a, T> CandidType for &'a T
where
    T: 'a + ?Sized + CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<&T>()
    } // ignore lifetime
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        (**self).idl_serialize(serializer)
    }
}

macro_rules! tuple_impls {
    ($($len:expr => ($($n:tt $name:ident)+))+) => {
        $(
            impl<$($name),+> CandidType for ($($name,)+)
            where
                $($name: CandidType,)+
            {
                fn id() -> TypeId { TypeId::of::<($($name,)+)>() }
                fn _ty() -> Type {
                    Type::Record(vec![
                        $(Field{ id: Label::Id($n), ty: $name::ty() },)+
                    ])
                }
                fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
                where S: Serializer,
                {
                    let mut ser = serializer.serialize_struct()?;
                    $(
                        Compound::serialize_element(&mut ser, &self.$n)?;
                    )+
                    Ok(())
                }
            }
        )+
    }
}

tuple_impls! {
    1 => (0 T0)
    2 => (0 T0 1 T1)
    3 => (0 T0 1 T1 2 T2)
    4 => (0 T0 1 T1 2 T2 3 T3)
    5 => (0 T0 1 T1 2 T2 3 T3 4 T4)
    6 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5)
    7 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6)
    8 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7)
    9 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8)
    10 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9)
    11 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10)
    12 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11)
    13 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12)
    14 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13)
    15 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14)
    16 => (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11 12 T12 13 T13 14 T14 15 T15)
}

impl CandidType for std::time::SystemTime {
    fn id() -> TypeId {
        TypeId::of::<std::time::SystemTime>()
    }

    fn _ty() -> Type {
        Type::Record(vec![
            Field {
                id: Label::Named("nanos_since_epoch".to_owned()),
                ty: u32::ty(),
            },
            Field {
                id: Label::Named("secs_since_epoch".to_owned()),
                ty: u64::ty(),
            },
        ])
    }

    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;

        let duration_since_epoch = self
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| S::Error::custom("SystemTime must be later than UNIX_EPOCH"))?;

        let secs: u64 = duration_since_epoch.as_secs();
        let nanos: u32 = duration_since_epoch.subsec_nanos();

        let mut ser = serializer.serialize_struct()?;
        ser.serialize_element(&nanos)?;
        ser.serialize_element(&secs)?;

        Ok(())
    }
}

#[test]
fn test_systemtime() {
    use crate::{Decode, Encode};

    let now = std::time::SystemTime::now();
    let encoded = Encode!(&now).unwrap();
    let decoded = Decode!(&encoded, std::time::SystemTime).unwrap();
    assert_eq!(now, decoded);
}
