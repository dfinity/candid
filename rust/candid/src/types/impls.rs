use super::internal::*;
use super::{CandidType, Compound, Serializer};

macro_rules! primitive_impl {
    ($t:ty, $id:tt, $method:ident $($cast:tt)*) => {
        impl CandidType for $t {
            fn _ty() -> Type { Type::$id }
            fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error> where S: Serializer {
                serializer.$method(*self $($cast)*)
            }
        }
    };
}

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

impl CandidType for i128 {
    fn _ty() -> Type {
        Type::Int
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_int(&crate::Int::from(*self))
    }
}
impl CandidType for u128 {
    fn _ty() -> Type {
        Type::Nat
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_nat(&crate::Nat::from(*self))
    }
}

impl CandidType for String {
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
impl CandidType for str {
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

impl CandidType for std::path::Path {
    fn _ty() -> Type {
        Type::Text
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;
        match self.to_str() {
            Some(s) => s.idl_serialize(serializer),
            None => Err(S::Error::custom("path contains invalid UTF-8 characters")),
        }
    }
}

impl CandidType for std::path::PathBuf {
    fn _ty() -> Type {
        Type::Text
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        self.as_path().idl_serialize(serializer)
    }
}

impl<T: Sized> CandidType for Option<T>
where
    T: CandidType,
{
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

impl<T> CandidType for [T]
where
    T: CandidType,
{
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
impl CandidType for serde_bytes::ByteBuf {
    fn _ty() -> Type {
        Type::Vec(Box::new(Type::Nat8))
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_blob(self.as_slice())
    }
}
impl CandidType for serde_bytes::Bytes {
    fn _ty() -> Type {
        Type::Vec(Box::new(Type::Nat8))
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_blob(self)
    }
}

macro_rules! map_impl {
    ($ty:ident < K $(: $kbound1:ident $(+ $kbound2:ident)*)*, V $(, $typaram:ident : $bound:ident)* >) => {
        impl<K, V $(, $typaram)*> CandidType for $ty<K, V $(, $typaram)*>
        where
            K: CandidType $(+ $kbound1 $(+ $kbound2)*)*,
            V: CandidType,
            $($typaram: $bound,)*
        {
            fn _ty() -> Type {
                let tuple = Type::Record(vec![
                    Field {
                        id: Label::Id(0),
                        ty: K::ty(),
                    },
                    Field {
                        id: Label::Id(1),
                        ty: V::ty(),
                    },
                ]);
                Type::Vec(Box::new(tuple))
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
    }
}
macro_rules! seq_impl {
    ($ty:ident < K $(: $kbound1:ident $(+ $kbound2:ident)*)* $(, $typaram:ident : $bound:ident)* >) => {
        impl<K $(, $typaram)*> CandidType for $ty<K $(, $typaram)*>
        where
            K: CandidType $(+ $kbound1 $(+ $kbound2)*)*,
            $($typaram: $bound,)*
        {
            fn _ty() -> Type {
                Type::Vec(Box::new(K::ty()))
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
    }
}
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::hash::{BuildHasher, Hash};
map_impl!(BTreeMap<K: Ord, V>);
map_impl!(HashMap<K: Eq + Hash, V, H: BuildHasher>);

seq_impl!(Vec<K>);
seq_impl!(VecDeque<K>);
seq_impl!(LinkedList<K>);
seq_impl!(BinaryHeap<K: Ord>);
seq_impl!(BTreeSet<K: Ord>);
seq_impl!(HashSet<K: Eq + Hash, H: BuildHasher>);

macro_rules! array_impls {
    ($($len:tt)+) => {
        $(
            impl<T> CandidType for [T; $len]
            where T: CandidType,
            {
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
    T: ?Sized + CandidType,
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
impl<'a, T> CandidType for &'a mut T
where
    T: ?Sized + CandidType,
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

impl<'a, T> CandidType for std::borrow::Cow<'a, T>
where
    T: ?Sized + CandidType + ToOwned,
{
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

impl<T> CandidType for std::cell::Cell<T>
where
    T: CandidType + Copy,
{
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        self.get().idl_serialize(serializer)
    }
}

impl<T> CandidType for std::cell::RefCell<T>
where
    T: CandidType,
{
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;
        match self.try_borrow() {
            Ok(v) => v.idl_serialize(serializer),
            Err(_) => Err(S::Error::custom("already mutably borrowed")),
        }
    }
}

impl<T> CandidType for std::rc::Rc<T>
where
    T: CandidType,
{
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        self.as_ref().idl_serialize(serializer)
    }
}

impl<T> CandidType for std::sync::Arc<T>
where
    T: CandidType,
{
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        self.as_ref().idl_serialize(serializer)
    }
}

macro_rules! tuple_impls {
    ($($len:expr => ($($n:tt $name:ident)+))+) => {
        $(
            impl<$($name),+> CandidType for ($($name,)+)
            where
                $($name: CandidType,)+
            {
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

impl CandidType for std::time::Duration {
    fn _ty() -> Type {
        Type::Record(vec![
            Field {
                id: Label::Named("secs".to_owned()),
                ty: u64::ty(),
            },
            Field {
                id: Label::Named("nanos".to_owned()),
                ty: u32::ty(),
            },
        ])
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        let secs: u64 = self.as_secs();
        let nanos: u32 = self.subsec_nanos();

        let mut ser = serializer.serialize_struct()?;
        ser.serialize_element(&secs)?;
        ser.serialize_element(&nanos)?;

        Ok(())
    }
}
