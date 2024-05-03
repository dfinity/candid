use anyhow::Result;
use candid::types::{Type, TypeEnv, TypeInner};
use serde::de::DeserializeOwned;
use std::collections::BTreeMap;
use toml::{Table, Value};

pub struct State<'a, T: ConfigState> {
    tree: &'a ConfigTree<T>,
    path: Vec<String>,
    open_tree: Option<&'a ConfigTree<T>>,
    open_path: Vec<String>,
    pub config: T,
    pub env: &'a TypeEnv,
}
#[derive(Debug)]
pub enum StateElem<'a> {
    Type(&'a Type),
    TypeStr(&'a str),
    Label(&'a str),
}
#[derive(Debug)]
pub struct Scope<'a> {
    pub method: &'a str,
    pub position: Option<ScopePos>,
}
#[derive(Debug)]
pub enum ScopePos {
    Arg,
    Ret,
}

impl<'a, T: ConfigState> State<'a, T> {
    pub fn new(tree: &'a ConfigTree<T>, env: &'a TypeEnv) -> Self {
        let mut config = T::default();
        if let Some(state) = &tree.state {
            config.merge_config(state, None, false);
        }
        Self {
            tree,
            open_tree: None,
            open_path: Vec::new(),
            path: Vec::new(),
            config,
            env,
        }
    }
    /// Match paths in the scope first. If `scope` is None, clear the scope.
    pub fn with_scope(&mut self, scope: &Option<Scope>, idx: usize) {
        match scope {
            None => {
                self.open_tree = None;
                self.open_path.clear();
            }
            Some(scope) => {
                let mut path = vec![format!("method:{}", scope.method)];
                match self.tree.with_prefix(&path) {
                    Some(tree) => {
                        match scope.position {
                            Some(ScopePos::Arg) => path.push(format!("arg:{}", idx)),
                            Some(ScopePos::Ret) => path.push(format!("ret:{}", idx)),
                            None => (),
                        }
                        match self.tree.with_prefix(&path) {
                            Some(subtree) => {
                                self.open_tree = Some(subtree);
                                self.open_path = path;
                            }
                            None => {
                                self.open_tree = Some(tree);
                                self.open_path = vec![path[0].clone()];
                            }
                        }
                        if let Some(state) = self.open_tree.unwrap().state.as_ref() {
                            self.config.merge_config(state, None, false);
                        }
                    }
                    None => {
                        self.open_tree = None;
                        self.open_path.clear();
                    }
                }
            }
        }
    }
    /// Update config based on the new elem in the path. Return the old state AFTER `update_state`.
    pub fn push_state(&mut self, elem: &StateElem) -> T {
        self.config.update_state(elem);
        let old_config = self.config.clone();
        self.path.push(elem.to_string());
        let new_state = if let Some(subtree) = self.open_tree {
            subtree
                .get_config(&self.path)
                .or_else(|| self.tree.get_config(&self.path))
        } else {
            self.tree.get_config(&self.path)
        };
        if let Some((state, is_recursive)) = new_state {
            self.config.merge_config(state, Some(elem), is_recursive);
            //eprintln!("match path: {:?}, state: {:?}", self.path, self.config);
        } else {
            self.config
                .merge_config(&T::unmatched_config(), Some(elem), false);
            //eprintln!("path: {:?}, state: {:?}", self.path, self.config);
        }
        old_config
    }
    pub fn pop_state(&mut self, old_config: T, elem: StateElem) {
        self.config = old_config;
        assert_eq!(self.path.pop(), Some(elem.to_string()));
        self.config.restore_state(&elem);
    }
}

pub trait ConfigState: DeserializeOwned + Default + Clone + std::fmt::Debug {
    fn merge_config(&mut self, config: &Self, elem: Option<&StateElem>, is_recursive: bool);
    fn update_state(&mut self, elem: &StateElem);
    fn restore_state(&mut self, elem: &StateElem);
    fn unmatched_config() -> Self {
        Self::default()
    }
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
            generate_state_tree(Value::Table(map))
        }
    }
    /// Return the subtree starting with prefix
    pub fn with_prefix(&self, prefix: &[String]) -> Option<&Self> {
        let mut tree = self;
        for elem in prefix.iter() {
            tree = tree.subtree.get(elem)?;
        }
        Some(tree)
    }
    pub fn add_config(&mut self, path: &[String], config: T) {
        let n = path.len();
        let mut tree: &Self = self;
        let mut i = 0;
        while i < n {
            if let Some(subtree) = tree.subtree.get(&path[i]) {
                tree = subtree;
                i += 1;
            } else {
                break;
            }
        }
        let mut node = Self {
            state: Some(config.clone()),
            subtree: BTreeMap::default(),
            max_depth: 0,
        };
        for k in (i + 1..n).rev() {
            node = Self {
                state: None,
                max_depth: node.max_depth + 1,
                subtree: [(path[k].clone(), node)].into_iter().collect(),
            }
        }
        let mut tree = self;
        let mut d = n as u8;
        #[allow(clippy::needless_range_loop)]
        for k in 0..i {
            tree.max_depth = std::cmp::max(d, tree.max_depth);
            tree = tree.subtree.get_mut(&path[k]).unwrap();
            d -= 1;
        }
        if i == n {
            tree.state = Some(config);
        } else {
            tree.subtree.insert(path[i].clone(), node);
            tree.max_depth = std::cmp::max(d, tree.max_depth);
        }
    }
    pub fn get_config(&self, path: &[String]) -> Option<(&T, bool)> {
        let len = path.len();
        assert!(len > 0);
        let start = len.saturating_sub(self.max_depth as usize);
        for i in (start..len).rev() {
            let (path, tail) = path.split_at(i);
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

#[derive(Clone)]
pub struct Configs(Table);

impl std::str::FromStr for Configs {
    type Err = crate::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let v = v.parse::<Table>()?;
        Ok(Configs(v))
    }
}
impl<'a> std::fmt::Display for StateElem<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            StateElem::Type(t) => write!(f, "{}", path_name(t)),
            StateElem::Label(l) => write!(f, "{}", l),
            StateElem::TypeStr(s) => write!(f, "{}", s),
        }
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
}

fn special_key(key: &str) -> bool {
    key.starts_with("method:") || key.starts_with("arg:") || key.starts_with("ret:")
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
        TypeInner::Vec(t) if matches!(t.as_ref(), TypeInner::Nat8) => "blob",
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
        fn merge_config(&mut self, config: &Self, _elem: Option<&StateElem>, is_recursive: bool) {
            *self = config.clone();
            if is_recursive {
                self.size = Some(0);
            }
        }
        fn update_state(&mut self, _elem: &StateElem) {
            self.size = self.size.map(|s| s + 1);
        }
        fn restore_state(&mut self, _elem: &StateElem) {
            self.size = self.size.map(|s| s - 1);
        }
    }
    let toml = r#"
[random]
list = { depth = 20, size = 50 }
val.text = "42"
left.list = { depth = 1 }
vec.nat8.text = "blob"
Vec = { width = 2, size = 10 }
"method:f"."arg:0".list = { depth = 2, size = 20 }
"method:f".list = { depth = 3, size = 30 }
    "#;
    let configs = toml.parse::<Configs>().unwrap();
    let mut tree: ConfigTree<T> = ConfigTree::from_configs("random", configs).unwrap();
    assert_eq!(tree.state, None);
    assert_eq!(tree.subtree.len(), 6);
    assert_eq!(tree.max_depth, 2);
    assert_eq!(
        tree.get_config(&["list".to_string()]).unwrap().0.depth,
        Some(20)
    );
    let t = T {
        text: None,
        depth: Some(100),
        size: None,
    };
    tree.add_config(&[], t.clone());
    assert_eq!(tree.state, Some(t.clone()));
    tree.add_config(&["left".to_string(), "list".to_string()], t.clone());
    assert_eq!(
        tree.match_exact_path(&["left".to_string(), "list".to_string()])
            .unwrap()
            .depth,
        Some(100)
    );
    assert_eq!(
        tree.match_exact_path(&["left".to_string(), "a".to_string()]),
        None
    );
    tree.add_config(&["left".to_string(), "a".to_string()], t.clone());
    assert_eq!(
        tree.match_exact_path(&["left".to_string(), "a".to_string()])
            .unwrap()
            .depth,
        Some(100)
    );
    assert_eq!(tree.max_depth, 2);
    tree.add_config(
        &["a".to_string(), "b".to_string(), "c".to_string()],
        t.clone(),
    );
    assert_eq!(
        tree.match_exact_path(&["a".to_string(), "b".to_string(), "c".to_string()])
            .unwrap()
            .depth,
        Some(100)
    );
    assert_eq!(tree.max_depth, 3);
    tree.add_config(
        &["a".to_string(), "b".to_string(), "d".to_string()],
        t.clone(),
    );
    assert_eq!(tree.max_depth, 3);
    tree.add_config(
        &[
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
        ],
        t.clone(),
    );
    assert_eq!(tree.max_depth, 4);
    let env = TypeEnv::default();
    let mut state = State::new(&tree, &env);
    state.with_scope(
        &Some(Scope {
            method: "f",
            position: Some(ScopePos::Arg),
        }),
        0,
    );
    assert_eq!(state.open_path, vec!["method:f", "arg:0"]);
    let old = state.push_state(&StateElem::Label("list"));
    assert_eq!(state.config.depth, Some(2));
    assert_eq!(state.config.size, Some(20));
    assert_eq!(state.config.text, None);
    assert_eq!(old.size, None);
    state.push_state(&StateElem::Label("val"));
    assert_eq!(state.config.text, Some("42".to_string()));
    state.with_scope(
        &Some(Scope {
            method: "f",
            position: Some(ScopePos::Ret),
        }),
        0,
    );
    assert_eq!(state.open_path, vec!["method:f"]);
    state.push_state(&StateElem::Label("list"));
    assert_eq!(state.config.depth, Some(3));
    assert_eq!(state.config.size, Some(0));
    state.with_scope(&None, 0);
    let old = state.push_state(&StateElem::Label("list"));
    assert_eq!(state.config.depth, Some(20));
    assert_eq!(state.config.size, Some(0));
    assert_eq!(old.size, Some(1));
    state.pop_state(old, StateElem::Label("list"));
    assert_eq!(state.config.size, Some(0));
    assert_eq!(state.config.depth, Some(3));
}
