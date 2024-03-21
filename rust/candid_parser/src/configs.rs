use candid::types::Type;
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
    t.to_string().split(' ').next().unwrap().to_string()
}
