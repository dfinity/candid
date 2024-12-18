use crate::idl_hash;
use std::cell::OnceCell;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::str::FromStr;

#[derive(Clone)]
enum TypeKeyInner {
    Indexed { index: i64, name: OnceCell<String> },
    Named { name: String, hash: u32 },
}

impl TypeKeyInner {
    pub fn as_str(&self) -> &str {
        match self {
            TypeKeyInner::Indexed { index, name } => {
                name.get_or_init(|| TypeKey::name_from_index(*index))
            }
            TypeKeyInner::Named { name, .. } => name,
        }
    }
}

impl Debug for TypeKeyInner {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A `TypeKey` represents a type from a Candid schema. The type can be string-based or index-based.
#[derive(Debug, Clone)]
pub struct TypeKey(TypeKeyInner);

impl TypeKey {
    const INDEXED_PREFIX: &'static str = "table";

    pub fn indexed(idx: i64) -> Self {
        TypeKeyInner::Indexed {
            index: idx,
            name: Default::default(),
        }
        .into()
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    fn name_from_index(i: i64) -> String {
        format!("{}{}", Self::INDEXED_PREFIX, i)
    }

    fn maybe_indexed(value: &str) -> Option<TypeKey> {
        let index = i64::from_str(value.strip_prefix(Self::INDEXED_PREFIX)?).ok()?;
        Some(TypeKey::indexed(index))
    }
}

impl From<TypeKeyInner> for TypeKey {
    fn from(value: TypeKeyInner) -> Self {
        Self(value)
    }
}

impl PartialOrd for TypeKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeKey {
    fn cmp(&self, other: &Self) -> Ordering {
        // If the performance of this function ever becomes too slow, the function can be optimized
        // by specializing comparison of two TypeKeyInner::Indexed objects.
        self.as_str().cmp(other.as_str())
    }
}

impl PartialEq for TypeKey {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (
                TypeKeyInner::Indexed { index: index1, .. },
                TypeKeyInner::Indexed { index: index2, .. },
            ) => *index1 == *index2,
            (
                TypeKeyInner::Named {
                    hash: hash1,
                    name: name1,
                },
                TypeKeyInner::Named {
                    hash: hash2,
                    name: name2,
                },
            ) => *hash1 == *hash2 && name1 == name2,
            _ => false,
        }
    }
}

impl Eq for TypeKey {}

impl Hash for TypeKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            TypeKeyInner::Indexed { index, .. } => index.hash(state),
            TypeKeyInner::Named { hash, .. } => hash.hash(state),
        }
    }
}

impl Display for TypeKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl From<String> for TypeKey {
    fn from(value: String) -> Self {
        Self::maybe_indexed(&value).unwrap_or_else(|| {
            TypeKeyInner::Named {
                hash: idl_hash(&value),
                name: value,
            }
            .into()
        })
    }
}

impl From<&str> for TypeKey {
    fn from(value: &str) -> Self {
        Self::maybe_indexed(value).unwrap_or_else(|| {
            TypeKeyInner::Named {
                hash: idl_hash(value),
                name: value.to_string(),
            }
            .into()
        })
    }
}

impl AsRef<str> for TypeKey {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn type_key_indexed_name() {
        assert_eq!(TypeKey::indexed(42).as_str(), "table42");
    }

    #[test]
    fn type_key_from_string() {
        assert_eq!(TypeKey::from("foobar"), TypeKey::from("foobar".to_string()));
        assert_eq!(TypeKey::from("foobar").as_str(), "foobar");
        assert_eq!(TypeKey::from("table").as_str(), "table");
        // Check that indexed keys with a "broken" index are parsed correctly.
        assert_eq!(TypeKey::from("table3.5").as_str(), "table3.5");
        assert_eq!(TypeKey::from("table-33").as_str(), "table-33");
    }

    #[test]
    fn type_key_indexed() {
        assert_eq!(TypeKey::from("table33"), TypeKey::indexed(33));
    }

    #[test]
    fn type_key_hash() {
        let mut map = HashMap::new();
        map.insert(TypeKey::from("a"), 1);
        map.insert(TypeKey::from("bar".to_string()), 2);
        map.insert(TypeKey::from("table1"), 3);
        map.insert(TypeKey::from("table97"), 4);
        map.insert(TypeKey::indexed(33), 5);

        assert_eq!(map.get(&"a".to_string().into()), Some(&1));
        assert_eq!(map.get(&"bar".into()), Some(&2));
        assert_eq!(map.get(&TypeKey::indexed(1)), Some(&3));
        assert_eq!(map.get(&TypeKey::indexed(97)), Some(&4));
        assert_eq!(map.get(&TypeKey::from("table33")), Some(&5));
    }

    #[test]
    fn type_key_ord() {
        let mut keys = vec![
            TypeKey::indexed(4),
            TypeKey::indexed(24),
            TypeKey::from("table3"),
            TypeKey::from("table"),
            TypeKey::indexed(1),
            TypeKey::from("table23"),
            TypeKey::from("table4.3"),
            TypeKey::from("zzz"),
            TypeKey::from("a"),
        ];

        let expected = vec![
            TypeKey::from("a"),
            TypeKey::from("table"),
            TypeKey::indexed(1),
            TypeKey::from("table23"),
            // Note that even though 3 < 24 and 4 < 24, they're ordered afterward because we use
            // string-based ordering to maintain consistency between named and indexed TypeKeys.
            TypeKey::indexed(24),
            TypeKey::from("table3"),
            TypeKey::indexed(4),
            TypeKey::from("table4.3"),
            TypeKey::from("zzz"),
        ];
        keys.sort_unstable();
        assert_eq!(keys, expected);
    }

    #[test]
    fn type_key_to_string() {
        assert_eq!(TypeKey::indexed(32).to_string(), "table32");
        assert_eq!(TypeKey::from("foo").to_string(), "foo");
        // debug string
        assert_eq!(format!("{:?}", TypeKey::indexed(32)), "TypeKey(table32)");
        assert_eq!(format!("{:?}", TypeKey::from("foo")), "TypeKey(foo)");
    }
}
