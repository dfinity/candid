use candid::types::{Type, TypeInner};
use serde::de::DeserializeOwned;
use toml::Value;

pub struct Configs(Value);

impl Configs {
    pub fn with_method(&self, method: &str) -> Self {
        let path = format!("[{method}]");
        let mut res = self.0.clone();
        if let Value::Table(ref mut map) = res {
            if let Some(Value::Table(subtree)) = map.remove(&path) {
                map.extend(&mut subtree.into_iter());
            }
            Configs(res)
        } else {
            unreachable!()
        }
    }
    fn get_helper(&self, path: &[String]) -> Option<&Value> {
        let mut result = &self.0;
        for elem in path.iter() {
            if let Value::Table(map) = result {
                result = map.get(elem)?;
            } else {
                unreachable!()
            }
        }
        if has_leaf(result) {
            Some(result)
        } else {
            None
        }
    }
    /// Get config that starts somewhere in the path and ends at the end of the path.
    /// The second return bool is whether the matched path appears earlier in the path (inside a recursion).
    /// Empty path returns the top-level config.
    pub fn get<T: DeserializeOwned>(&self, path: &[String]) -> Option<(T, bool)> {
        if path.is_empty() {
            return Some((self.0.clone().try_into::<T>().ok()?, false));
        }
        for i in (0..path.len()).rev() {
            let (_, tail) = path.split_at(i);
            match self.get_helper(tail) {
                Some(v) => {
                    let parsed_config = v.clone().try_into::<T>().ok()?;
                    return Some((parsed_config, is_repeated(path, tail)));
                }
                None => continue,
            }
        }
        None
    }
}
impl std::str::FromStr for Configs {
    type Err = crate::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let v = v.parse::<Value>()?;
        Ok(Configs(v))
    }
}

fn is_repeated(path: &[String], matched: &[String]) -> bool {
    let (test, _) = path.split_at(path.len() - matched.len());
    test.join(".").contains(&matched.join("."))
}

fn has_leaf(v: &Value) -> bool {
    if let Value::Table(map) = v {
        for (_, val) in map.iter() {
            match val {
                Value::Table(_) => continue,
                _ => return true,
            }
        }
        false
    } else {
        false
    }
}

pub fn path_name(t: &Type) -> String {
    match t.as_ref() {
        TypeInner::Null => "null",
        TypeInner::Bool => "bool",
        TypeInner::Nat => "nat",
        TypeInner::Int => "int",
        TypeInner::Nat8 => "nat8",
        TypeInner::Nat16 => "nat16",
        TypeInner::Nat32 => "nat32",
        TypeInner::Nat64 => "nat64",
        TypeInner::Int8 => "int8",
        TypeInner::Int16 => "int16",
        TypeInner::Int32 => "int32",
        TypeInner::Int64 => "int64",
        TypeInner::Float32 => "float32",
        TypeInner::Float64 => "float64",
        TypeInner::Text => "text",
        TypeInner::Reserved => "reserved",
        TypeInner::Empty => "empty",
        TypeInner::Var(id) => id,
        TypeInner::Knot(id) => id.name,
        TypeInner::Principal => "principal",
        TypeInner::Opt(_) => "opt",
        TypeInner::Vec(_) => "vec",
        TypeInner::Record(_) => "record",
        TypeInner::Variant(_) => "variant",
        TypeInner::Func(_) => "func",
        TypeInner::Service(_) => "service",
        TypeInner::Class(..) | TypeInner::Unknown | TypeInner::Future => unreachable!(),
    }
    .to_string()
}
