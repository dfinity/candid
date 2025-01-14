use super::internal::*;
use super::{CandidType, Compound, Serializer};

macro_rules! primitive_impl {
    ($t:ty, $id:tt, $method:ident $($cast:tt)*) => {
        impl CandidType for $t {
            fn _ty() -> Type { TypeInner::$id.into() }
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
        TypeInner::Int.into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_i128(*self)
    }
}
impl CandidType for u128 {
    fn _ty() -> Type {
        TypeInner::Nat.into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u128(*self)
    }
}

impl CandidType for String {
    fn _ty() -> Type {
        TypeInner::Text.into()
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
        TypeInner::Text.into()
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
        TypeInner::Text.into()
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
        TypeInner::Text.into()
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
        TypeInner::Opt(T::ty()).into()
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
        TypeInner::Vec(T::ty()).into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        let mut ser = serializer.serialize_vec(self.len())?;
        for e in self {
            Compound::serialize_element(&mut ser, &e)?;
        }
        Ok(())
    }
}
#[cfg_attr(docsrs, doc(cfg(feature = "serde_bytes")))]
#[cfg(feature = "serde_bytes")]
impl CandidType for serde_bytes::ByteBuf {
    fn _ty() -> Type {
        TypeInner::Vec(TypeInner::Nat8.into()).into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_blob(self.as_slice())
    }
}
#[cfg_attr(docsrs, doc(cfg(feature = "serde_bytes")))]
#[cfg(feature = "serde_bytes")]
impl CandidType for serde_bytes::Bytes {
    fn _ty() -> Type {
        TypeInner::Vec(TypeInner::Nat8.into()).into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_blob(self)
    }
}
#[cfg_attr(docsrs, doc(cfg(feature = "serde_bytes")))]
#[cfg(feature = "serde_bytes")]
impl<const N: usize> CandidType for serde_bytes::ByteArray<N> {
    fn _ty() -> Type {
        TypeInner::Vec(TypeInner::Nat8.into()).into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_blob(self.as_slice())
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
                let tuple = TypeInner::Record(vec![
                    Field {
                        id: Label::Id(0).into(),
                        ty: K::ty(),
                    },
                    Field {
                        id: Label::Id(1).into(),
                        ty: V::ty(),
                    },
                ]).into();
                TypeInner::Vec(tuple).into()
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
                TypeInner::Vec(K::ty()).into()
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

impl<T: CandidType, const N: usize> CandidType for [T; N] {
    fn _ty() -> Type {
        TypeInner::Vec(T::ty()).into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        let mut ser = serializer.serialize_vec(N)?;
        for e in self {
            Compound::serialize_element(&mut ser, &e)?;
        }
        Ok(())
    }
}

impl<T, E> CandidType for Result<T, E>
where
    T: CandidType,
    E: CandidType,
{
    fn _ty() -> Type {
        TypeInner::Variant(vec![
            // Make sure the field id is sorted by idl_hash
            Field {
                id: Label::Named("Ok".to_owned()).into(),
                ty: T::ty(),
            },
            Field {
                id: Label::Named("Err".to_owned()).into(),
                ty: E::ty(),
            },
        ])
        .into()
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

impl<T> CandidType for std::cmp::Reverse<T>
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
        self.0.idl_serialize(serializer)
    }
}

impl<T> CandidType for &T
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
impl<T> CandidType for &mut T
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

impl<T> CandidType for std::borrow::Cow<'_, T>
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

impl<T> CandidType for std::marker::PhantomData<T>
where
    T: CandidType,
{
    fn _ty() -> Type {
        T::ty()
    }
    fn idl_serialize<S>(&self, _: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;
        Err(S::Error::custom("`PhantomData` cannot be serialized"))
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
                    TypeInner::Record(vec![
                        $(Field{ id: Label::Id($n).into(), ty: $name::ty() },)+
                    ]).into()
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
        TypeInner::Record(vec![
            Field {
                id: Label::Named("nanos_since_epoch".to_owned()).into(),
                ty: u32::ty(),
            },
            Field {
                id: Label::Named("secs_since_epoch".to_owned()).into(),
                ty: u64::ty(),
            },
        ])
        .into()
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
        TypeInner::Record(vec![
            Field {
                id: Label::Named("secs".to_owned()).into(),
                ty: u64::ty(),
            },
            Field {
                id: Label::Named("nanos".to_owned()).into(),
                ty: u32::ty(),
            },
        ])
        .into()
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
