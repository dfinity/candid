use super::internal::*;
use super::{CandidType, CandidTypeCache, CandidTyping, Compound, IdlSerialize, Serializer};

macro_rules! serialize_impl {
    (
        <
            $($l:lifetime),*
            $(,)?
            $($p:ident $(: ($($b:tt)+) )?),*
            $(,)?
            $(;)?
            $(const $c:ident: $ct:ty),*
        > for $t:ty,
        ($self:ident, $serializer:ident) => $cast:expr
    ) => {
        impl<
            $($l,)*
            $($p$(:$($b)+)?,)*
            $(const $c: $ct),*
        > IdlSerialize for $t {
            fn idl_serialize<S: Serializer>(&$self, $serializer: S) -> Result<(), S::Error> {
                $cast
            }
        }
    };

    ($($t:ident)::+ $(<
        $($l:lifetime),*
        $(,)?
        $($p:ident $(:$b:tt)?),*
        $(,)?
        $(;)?
        $(const $c:ident: $ct:ty),*
    >)?, ($self:ident, $serializer:ident) => $cast:expr) => {
        serialize_impl!{
            <$(
                $($l,)*
                $($p$(:$b)?,)*
                $(const $c: $ct),*
            )?> for $($t)::+$(<$($l,)*$($p,)*$(const $c: $ct),*>)?,
            ($self, $serializer) => $cast
        }
    };

    ($t:ty, $method:ident($self:ident => $cast:expr)) => {
        serialize_impl!{
            <> for $t,
            ($self, serializer) => serializer.$method($cast)
        }
    };
    ($t:ty, $method:ident as $cast:ty) => {
        serialize_impl!{$t, $method(self => *self as $cast)}
    };
    ($t:ty, $method:ident) => {
        serialize_impl!{$t, $method(self => *self)}
    };
    ($t:ty, ($self:ident, $serializer:ident) => $cast:expr) => {
        serialize_impl!{<> for $t, ($self, $serializer) => $cast}
    };
}
macro_rules! candid_impl {
    (
        <
            $($l:lifetime),*
            $(,)?
            $($p:ident $(: ($($b:tt)+) )?),*
            $(,)?
            $(;)?
            $(const $c:ident: $ct:ty),*
        > for $t:ty,
        ($C:ident, $cache:ident) => $_ty:expr
    ) => {
        impl<
            $($l,)*
            $($p$(:$($b)+)?,)*
            $(const $c: $ct),*
        > CandidType for $t {
            fn _ty<$C: CandidTypeCache>($cache: &mut $C) -> Type { $_ty }
        }
    };

    (
        $($t:ident)::+ $(<
            $($l:lifetime),*
            $(,)?
            $($p:ident $(:$b:tt)?),*
            $(,)?
            $(;)?
            $(const $c:ident: $ct:ty),*
        >)?,
        ($C:ident, $cache:ident) => $_ty:expr
    ) => {
        candid_impl!{
            <$(
                $($l,)*
                $($p$(:$b)?,)*
                $(const $c: $ct),*
            )?> for $($t)::+$(<$($l,)*$($p,)*$(const $c: $ct),*>)?,
            ($C, $cache) => $_ty
        }
    };

    ($t:ty, ($C:ident, $cache:ident) => $_ty:expr) => {
        candid_impl!{<> for $t, ($C, $cache) => $_ty}
    };
    ($t:ty, $_ty:expr) => {
        candid_impl!{<> for $t, (C, _c) => $_ty}
    };
}

macro_rules! primitive_impl {
    ($t:ty, $id:tt, $($serialize:tt)+) => {
        serialize_impl!{$t, $($serialize)+}
        candid_impl!{$t, Type::$id}
    };
}

macro_rules! iter_serialize_impl {
    ($($t:tt)+) => {
        serialize_impl!{
            $($t)+,
            (self, serializer) => {
                let mut ser = serializer.serialize_vec(self.len())?;
                for e in self.iter() {
                    Compound::serialize_element(&mut ser, &e)?;
                }
                Ok(())
            }
        }
    };
}
macro_rules! map_candid_impl {
    ($($t:tt)+) => {
        candid_impl!{
            $($t)+,
            (C, c) => {
                let tuple = Type::Record(vec![
                    Field {
                        id: Label::Id(0),
                        ty: <K as CandidTyping<C>>::ty_from_cache(c),
                    },
                    Field {
                        id: Label::Id(1),
                        ty: <V as CandidTyping<C>>::ty_from_cache(c),
                    },
                ]);
                Type::Vec(Box::new(tuple))
            }
        }
    };
}
macro_rules! seq_candid_impl {
    ($($t:tt)+) => {
        candid_impl!{$($t)+, (C, c) => Type::Vec(Box::new(<K as CandidTyping<C>>::ty_from_cache(c)))}
    };
}

primitive_impl!((), Null, serialize_null);
primitive_impl!(bool, Bool, serialize_bool);

primitive_impl!(i8, Int8, serialize_int8);
primitive_impl!(i16, Int16, serialize_int16);
primitive_impl!(i32, Int32, serialize_int32);
primitive_impl!(i64, Int64, serialize_int64);
primitive_impl!(i128, Int, serialize_int(self => &crate::Int::from(*self)));

primitive_impl!(u8, Nat8, serialize_nat8);
primitive_impl!(u16, Nat16, serialize_nat16);
primitive_impl!(u32, Nat32, serialize_nat32);
primitive_impl!(u64, Nat64, serialize_nat64);
primitive_impl!(u128, Nat, serialize_nat(self => &crate::Nat::from(*self)));

primitive_impl!(f32, Float32, serialize_float32);
primitive_impl!(f64, Float64, serialize_float64);

// isize, usize always encode to 64bit to ensure the same behavior
// on different platforms. This is consistent with serde's convention
primitive_impl!(isize, Int64, serialize_int64 as i64);
primitive_impl!(usize, Nat64, serialize_nat64 as u64);

primitive_impl!(String, Text, serialize_text(self => &*self));
primitive_impl!(str, Text, serialize_text(self => self));
primitive_impl!(std::path::Path, Text, serialize_text(self => {
    use serde::ser::Error;
    match self.to_str() {
        Some(s) => s,
        None => return Err(S::Error::custom("path contains invalid UTF-8 characters")),
    }
}));
primitive_impl!(std::path::PathBuf, Text, (self, serializer) => {
    self.as_path().idl_serialize(serializer)
});

// Option
serialize_impl! {
    Option<T: (IdlSerialize)>,
    (self, serializer) => serializer.serialize_option(self.as_ref())
}
candid_impl! {Option<T: (CandidType)>, (C, c) => Type::Opt(Box::new(<T as CandidTyping<C>>::ty_from_cache(c)))}

// [T]
iter_serialize_impl! {<T: (IdlSerialize)> for [T]}
candid_impl! {<T: (CandidType)> for [T], (C, c) => Type::Vec(Box::new(<T as CandidTyping<C>>::ty_from_cache(c)))}

serialize_impl! {
    serde_bytes::ByteBuf,
    (self, serializer) => serializer.serialize_blob(self.as_slice())
}
candid_impl! {serde_bytes::ByteBuf, Type::Vec(Box::new(Type::Nat8))}

serialize_impl! {
    serde_bytes::Bytes,
    (self, serializer) => serializer.serialize_blob(self.as_ref())
}
candid_impl! {serde_bytes::Bytes, Type::Vec(Box::new(Type::Nat8))}

use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::hash::{BuildHasher, Hash};
iter_serialize_impl! {BTreeMap<K: (Ord+IdlSerialize), V: (IdlSerialize)>}
map_candid_impl! {BTreeMap<K: (Ord+CandidType), V: (CandidType)>}

iter_serialize_impl! {HashMap<K: (Eq+Hash+IdlSerialize), V: (IdlSerialize), H: (BuildHasher)>}
map_candid_impl! {HashMap<K: (Eq+Hash+CandidType), V: (CandidType), H: (BuildHasher)>}

iter_serialize_impl! {Vec<K: (IdlSerialize)>}
seq_candid_impl! {Vec<K: (CandidType)>}
iter_serialize_impl! {VecDeque<K: (IdlSerialize)>}
seq_candid_impl! {VecDeque<K: (CandidType)>}
iter_serialize_impl! {LinkedList<K: (IdlSerialize)>}
seq_candid_impl! {LinkedList<K: (CandidType)>}
iter_serialize_impl! {BinaryHeap<K: (Ord+IdlSerialize)>}
seq_candid_impl! {BinaryHeap<K: (Ord+CandidType)>}
iter_serialize_impl! {BTreeSet<K: (Ord+IdlSerialize)>}
seq_candid_impl! {BTreeSet<K: (Ord+CandidType)>}
iter_serialize_impl! {HashSet<K: (Eq+Hash+IdlSerialize), H: (BuildHasher)>}
seq_candid_impl! {HashSet<K: (Eq+Hash+CandidType), H: (BuildHasher)>}

iter_serialize_impl! {<T: (IdlSerialize); const N: usize> for [T; N]}
candid_impl! {<T: (CandidType); const N: usize> for [T; N], (C, c) => Type::Vec(Box::new(<T as CandidTyping<C>>::ty_from_cache(c)))}

serialize_impl! {
    Result<T: (IdlSerialize), E: (IdlSerialize)>,
    (self, serializer) => {
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
candid_impl! {Result<T: (CandidType), E: (CandidType)>, (C, c) => Type::Variant(vec![
    // Make sure the field id is sorted by idl_hash
    Field {
        id: Label::Named("Ok".to_owned()),
        ty: <T as CandidTyping<C>>::ty_from_cache(c),
    },
    Field {
        id: Label::Named("Err".to_owned()),
        ty: <E as CandidTyping<C>>::ty_from_cache(c),
    },
])}

serialize_impl! {
    Box<T: (?Sized + IdlSerialize)>,
    (self, serializer) => (**self).idl_serialize(serializer)
}
candid_impl! {Box<T: (?Sized+CandidType)>, (C, c) => <T as CandidTyping<C>>::ty_from_cache(c)}

serialize_impl! {
    <'a, T: (?Sized + IdlSerialize)> for &'a T,
    (self, serializer) => (**self).idl_serialize(serializer)
}
impl<'a, T> CandidType for &'a T
where
    T: ?Sized + CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<&T>() // ignore lifetime
    }
    fn _ty<C: CandidTypeCache>(c: &mut C) -> Type {
        <T as CandidTyping<C>>::ty_from_cache(c)
    }
}

serialize_impl! {
    <'a, T: (?Sized + IdlSerialize)> for &'a mut T,
    (self, serializer) => (**self).idl_serialize(serializer)
}
impl<'a, T> CandidType for &'a mut T
where
    T: ?Sized + CandidType,
{
    fn id() -> TypeId {
        TypeId::of::<&T>() // ignore lifetime
    }
    fn _ty<C: CandidTypeCache>(c: &mut C) -> Type {
        <T as CandidTyping<C>>::ty_from_cache(c)
    }
}

serialize_impl! {
    std::borrow::Cow<'a, T: (?Sized + IdlSerialize + ToOwned)>,
    (self, serializer) => (**self).idl_serialize(serializer)
}
candid_impl! {std::borrow::Cow<'a, T: (?Sized + CandidType + ToOwned)>, (C, c) => <T as CandidTyping<C>>::ty_from_cache(c)}

serialize_impl! {
    std::cell::Cell<T: (IdlSerialize + Copy)>,
    (self, serializer) => self.get().idl_serialize(serializer)
}
candid_impl! {std::cell::Cell<T: (CandidType + Copy)>, (C, c) => <T as CandidTyping<C>>::ty_from_cache(c)}

serialize_impl! {
    std::cell::RefCell<T: (IdlSerialize)>,
    (self, serializer) => {
        use serde::ser::Error;
        match self.try_borrow() {
            Ok(v) => v.idl_serialize(serializer),
            Err(_) => Err(S::Error::custom("already mutably borrowed")),
        }
    }
}
candid_impl! {std::cell::RefCell<T: (CandidType)>, (C, c) => <T as CandidTyping<C>>::ty_from_cache(c)}

macro_rules! tuple_impls {
    ($($len:expr => ($($n:tt $name:ident)+))+) => {
        $(
            serialize_impl!{
                <$($name: (IdlSerialize)),+> for ($($name,)+),
                (self, serializer) => {
                    let mut ser = serializer.serialize_struct()?;
                    $(
                        Compound::serialize_element(&mut ser, &self.$n)?;
                    )+
                    Ok(())
                }
            }

            candid_impl!{
                <$($name: (CandidType)),+> for ($($name,)+),
                (C, c) => Type::Record(vec![
                    $(Field{ id: Label::Id($n), ty: <$name as CandidTyping<C>>::ty_from_cache(c) },)+
                ])
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

serialize_impl! {
    std::time::SystemTime,
    (self, serializer) => {
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

candid_impl! {std::time::SystemTime, (C, c) => Type::Record(vec![
        Field {
            id: Label::Named("nanos_since_epoch".to_owned()),
            ty: <u32 as CandidTyping<C>>::ty_from_cache(c),
        },
        Field {
            id: Label::Named("secs_since_epoch".to_owned()),
            ty: <u64 as CandidTyping<C>>::ty_from_cache(c),
        },
    ])
}

serialize_impl! {
    std::time::Duration,
    (self, serializer) => {
        let secs: u64 = self.as_secs();
        let nanos: u32 = self.subsec_nanos();

        let mut ser = serializer.serialize_struct()?;
        ser.serialize_element(&secs)?;
        ser.serialize_element(&nanos)?;

        Ok(())
    }
}
candid_impl! {std::time::Duration, (C, c) => Type::Record(vec![
        Field {
            id: Label::Named("secs".to_owned()),
            ty: <u64 as CandidTyping<C>>::ty_from_cache(c),
        },
        Field {
            id: Label::Named("nanos".to_owned()),
            ty: <u32 as CandidTyping<C>>::ty_from_cache(c),
        },
    ])
}
