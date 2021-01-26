use crate::types::Type;
use serde::de::DeserializeOwned;
use serde_dhall::{from_simple_value, SimpleValue};

pub struct Configs(SimpleValue);

impl Configs {
    pub fn from_dhall(v: SimpleValue) -> Self {
        Configs(v)
    }
    fn get_helper(&self, path: &[String]) -> Option<&SimpleValue> {
        let mut result = &self.0;
        let mut iter = path.iter();
        while let Some(elem) = iter.next() {
            if let SimpleValue::Record(map) = result {
                result = map.get(elem)?;
            } else {
                unreachable!()
            }
        }
        if has_leaf(result) {
            //println!("{:?} {:?}", path, result);
            Some(result)
        } else {
            None
        }
    }
    /// Get config that starts somewhere in the path and ends at the end of the path
    pub fn get<T: DeserializeOwned>(&self, path: &[String]) -> Option<T> {
        for i in (0..path.len()).rev() {
            let (_, tail) = path.split_at(i);
            match self.get_helper(tail) {
                Some(v) => return from_simple_value::<T>(v.clone()).ok(),
                None => continue,
            }
        }
        None
    }
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
