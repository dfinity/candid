use crate::Result;
use serde::de::DeserializeOwned;
use serde_dhall::{from_simple_value, SimpleValue};

pub struct Configs(SimpleValue);

impl Configs {
    pub fn from_dhall(v: SimpleValue) -> Self {
        Configs(v)
    }
    pub fn get<T>(&self, path: &str) -> Result<T>
    where
        T: DeserializeOwned,
    {
        match &self.0 {
            SimpleValue::Record(map) => {
                let conf = map.get(path).unwrap().clone();
                Ok(from_simple_value(conf)?)
            }
            _ => unreachable!(),
        }
    }
}
