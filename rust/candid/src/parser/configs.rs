use crate::types::Type;
use serde::de::DeserializeOwned;
use serde_dhall::{from_simple_value, SimpleValue};

pub struct Configs(SimpleValue);

impl Configs {
    pub fn from_dhall(v: SimpleValue) -> Self {
        Configs(v)
    }
    pub fn with_method(&self, method: &str) -> Self {
        let path = format!("[{}]", method);
        let mut res = self.0.clone();
        if let SimpleValue::Record(ref mut map) = res {
            if let Some(SimpleValue::Record(mut subtree)) = map.remove(&path) {
                map.append(&mut subtree);
            }
            Configs(res)
        } else {
            unreachable!()
        }
    }
    /*
    pub fn with_method(&self, method: &str) -> Self {
        let path = [format!("[{}]", method)];
        let res = self.0.clone();
        let subtree = self.get_helper(&path).map(|x| x.clone());
        if let Some(SimpleValue::Record(mut method_map)) = subtree {
            if let SimpleValue::Record(mut map) = res {
                map.append(&mut method_map);
                Configs(SimpleValue::Record(map))
            } else {
                unreachable!()
            }
        } else {
            Configs(res)
        }
    }*/
    fn get_helper(&self, path: &[String]) -> Option<&SimpleValue> {
        let mut result = &self.0;
        for elem in path.iter() {
            if let SimpleValue::Record(map) = result {
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
    pub fn get<T: DeserializeOwned>(&self, path: &[String]) -> Option<(T, bool)> {
        for i in (0..path.len()).rev() {
            let (_, tail) = path.split_at(i);
            match self.get_helper(tail) {
                Some(v) => {
                    let parsed_config = from_simple_value::<T>(v.clone()).ok()?;
                    return Some((parsed_config, is_repeated(path, tail)));
                }
                None => continue,
            }
        }
        None
    }
}

fn is_repeated(path: &[String], matched: &[String]) -> bool {
    let (test, _) = path.split_at(path.len() - matched.len());
    test.join(".").contains(&matched.join("."))
}

fn has_leaf(v: &SimpleValue) -> bool {
    if let SimpleValue::Record(map) = v {
        for (_, val) in map.iter() {
            match val {
                SimpleValue::Record(_) => continue,
                _ => return true,
            }
        }
        false
    } else {
        false
    }
}

pub fn path_name(t: &Type) -> String {
    t.to_string().split(' ').next().unwrap().to_string()
}
