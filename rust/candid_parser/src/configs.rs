use anyhow::Result;
use candid::types::{Type, TypeEnv, TypeInner};
use serde::de::DeserializeOwned;
use std::collections::BTreeMap;
use toml::{Table, Value};

pub struct State<'a, T: ConfigState> {
    tree: &'a ConfigTree<T>,
    path: Vec<String>,
    pub config: T,
    pub env: &'a TypeEnv,
}
pub enum StateElem<'a> {
    Type(&'a Type),
    Label(&'a str),
}
impl<'a> std::fmt::Display for StateElem<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            StateElem::Type(t) => write!(f, "{}", path_name(t)),
            StateElem::Label(l) => write!(f, "{}", l),
        }
    }
}
impl<'a, T: ConfigState> State<'a, T> {
    pub fn new(tree: &'a ConfigTree<T>, env: &'a TypeEnv) -> Self {
        let mut config = T::default();
        if let Some(state) = &tree.state {
            config.merge_config(state, false);
        }
        Self {
            tree,
            path: Vec::new(),
            config,
            env,
        }
    }
    /// Update config based on the new elem in the path. Return the old state AFTER `update_state`.
    pub fn push_state(&mut self, elem: &StateElem) -> T {
        self.config.update_state(elem);
        let old_config = self.config.clone();
        self.path.push(elem.to_string());
        if let Some((state, is_recursive)) = self.tree.get_config(&self.path) {
            self.config.merge_config(state, is_recursive);
        }
        old_config
    }
    pub fn pop_state(&mut self, old_config: T, elem: StateElem) {
        self.config = old_config;
        assert_eq!(self.path.pop(), Some(elem.to_string()));
        self.config.restore_state(&elem);
    }
}

pub trait ConfigState: DeserializeOwned + Default + Clone {
    fn merge_config(&mut self, config: &Self, is_recursive: bool);
    fn update_state(&mut self, elem: &StateElem);
    fn restore_state(&mut self, elem: &StateElem);
}
#[derive(Debug)]
pub struct ConfigTree<T: ConfigState> {
    state: Option<T>,
    subtree: BTreeMap<String, ConfigTree<T>>,
    // max_depth is only here to optimize the performance of `get_config`
    max_depth: u8,
}
impl<T: ConfigState> ConfigTree<T> {
    pub fn from_configs(kind: &str, configs: Configs) -> Result<Self> {
        let mut map = configs.0;
        if let Some(v) = map.remove(kind) {
            generate_state_tree(v)
        } else {
            Ok(Self {
                state: None,
                subtree: BTreeMap::new(),
                max_depth: 0,
            })
        }
    }
    /// Return the subtree starting with prefix
    pub fn with_method(&self, prefix: Vec<String>) -> Option<&Self> {
        let mut tree = self;
        for elem in prefix.iter() {
            tree = tree.subtree.get(elem)?;
        }
        Some(tree)
    }
    pub fn get_config(&self, path: &[String]) -> Option<(&T, bool)> {
        let len = path.len();
        let start = len.saturating_sub(self.max_depth as usize);
        for i in (start..len).rev() {
            let tail = &path[i..];
            match self.match_exact_path(tail) {
                Some(v) => return Some((v, is_repeated(path, tail))),
                None => continue,
            }
        }
        None
    }
    fn match_exact_path(&self, path: &[String]) -> Option<&T> {
        let mut result = self;
        for elem in path.iter() {
            result = result.subtree.get(elem)?;
        }
        result.state.as_ref()
    }
}

pub struct Configs(Table);

impl std::str::FromStr for Configs {
    type Err = crate::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let v = v.parse::<Table>()?;
        Ok(Configs(v))
    }
}

fn is_repeated(path: &[String], matched: &[String]) -> bool {
    let iter = path.as_ref().windows(matched.len());
    for slice in iter {
        if slice == matched {
            return true;
        }
    }
    false
    //let (test, _) = path.split_at(path.len() - matched.len());
    //test.join(".").contains(&matched.join("."))
}

fn special_key(key: &str) -> bool {
    key.starts_with('_') || key.starts_with('[')
}

fn generate_state_tree<T: ConfigState>(v: Value) -> Result<ConfigTree<T>> {
    let mut subtree = BTreeMap::new();
    let mut leaves = toml::Table::new();
    let mut depth = 0;
    if let Value::Table(map) = v {
        for (k, v) in map.into_iter() {
            match v {
                Value::Table(_) => {
                    let v = generate_state_tree(v)?;
                    let dep = if special_key(&k) {
                        v.max_depth
                    } else {
                        v.max_depth + 1
                    };
                    depth = std::cmp::max(depth, dep);
                    subtree.insert(k, v);
                }
                v => drop(leaves.insert(k, v)),
            }
        }
        let state = if !leaves.is_empty() {
            Some(leaves.try_into::<T>()?)
        } else {
            None
        };
        Ok(ConfigTree {
            state,
            subtree,
            max_depth: depth,
        })
    } else {
        Err(anyhow::anyhow!("Expected a table"))
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
        TypeInner::Future => "future",
        TypeInner::Class(..) | TypeInner::Unknown => unreachable!(),
    }
    .to_string()
}

#[test]
fn parse() {
    use serde::Deserialize;
    #[derive(Debug, Deserialize, Clone, PartialEq, Default)]
    struct T {
        depth: Option<u32>,
        size: Option<u32>,
        text: Option<String>,
    }
    impl ConfigState for T {
        fn merge_config(&mut self, _config: &Self, _is_recursive: bool) {
            unimplemented!()
        }
        fn update_state(&mut self, _elem: &StateElem) {
            unimplemented!()
        }
        fn restore_state(&mut self, _elem: &StateElem) {
            unimplemented!()
        }
    }
    let toml = r#"
[random]
list = { depth = 20, size = 50 }
val.text = "42"
left.list = { depth = 1 }
vec.nat8.text = "blob"
Vec = { width = 2, size = 10 }
    "#;
    let configs = toml.parse::<Configs>().unwrap();
    let tree: ConfigTree<T> = ConfigTree::from_configs("random", configs).unwrap();
    assert_eq!(tree.state, None);
    assert_eq!(tree.subtree.len(), 5);
    assert_eq!(tree.max_depth, 2);
    assert_eq!(
        tree.get_config(&["list".to_string()]).unwrap().0.depth,
        Some(20)
    );
}
