use anyhow::Result;
use candid::types::{Type, TypeEnv, TypeInner};
use serde::de::DeserializeOwned;
use std::collections::{BTreeMap, BTreeSet};
use toml::{Table, Value};

pub struct State<'a, T: ConfigState> {
    tree: &'a ConfigTree<T>,
    pub path: Vec<String>,
    open_tree: Option<&'a ConfigTree<T>>,
    open_path: Vec<String>,
    pub stats: BTreeMap<Vec<String>, u32>,
    pub config: T,
    pub config_source: BTreeMap<String, Vec<String>>,
    pub env: &'a TypeEnv,
}
pub struct ConfigBackup<T> {
    config: T,
    config_source: BTreeMap<String, Vec<String>>,
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
        let mut config_source = BTreeMap::new();
        if let Some(state) = &tree.state {
            let delta = config.merge_config(state, None);
            for field in delta {
                config_source.insert(field, vec![]);
            }
        }
        Self {
            tree,
            open_tree: None,
            open_path: Vec::new(),
            path: Vec::new(),
            stats: BTreeMap::new(),
            config,
            config_source,
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
                let mut path = vec![format!("func:{}", scope.method)];
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
                            let delta = self.config.merge_config(state, None);
                            let path = self.open_path.clone();
                            self.update_config_source(delta, &path);
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
    pub fn push_state(&mut self, elem: &StateElem) -> ConfigBackup<T> {
        self.config.update_state(elem);
        let old_config = self.to_backup();
        self.path.push(elem.to_string());
        let mut from_open = false;
        let new_state = if let Some(subtree) = self.open_tree {
            from_open = true;
            subtree.get_config(&self.path).or_else(|| {
                from_open = false;
                self.tree.get_config(&self.path)
            })
        } else {
            self.tree.get_config(&self.path)
        };
        if let Some((state, is_recursive, idx)) = new_state {
            let mut matched_path = if from_open {
                self.open_path.clone()
            } else {
                vec![]
            };
            matched_path.extend_from_slice(&self.path[idx..]);
            let ctx = Context { elem, is_recursive };
            let delta = self.config.merge_config(state, Some(ctx));
            self.update_config_source(delta, &matched_path);
        } else {
            let ctx = Context {
                elem,
                is_recursive: false,
            };
            let delta = self.config.merge_config(&T::unmatched_config(), Some(ctx));
            for field in delta {
                self.config_source.remove(&field);
            }
        }
        old_config
    }
    pub fn pop_state(&mut self, old_config: ConfigBackup<T>, elem: StateElem) {
        self.restore_from_backup(old_config);
        assert_eq!(self.path.pop(), Some(elem.to_string()));
        self.config.restore_state(&elem);
    }
    pub fn update_stats(&mut self, key: &str) {
        if let Some(path) = self.config_source.get(key) {
            let mut path = path.clone();
            path.push(key.to_string());
            self.stats.entry(path).and_modify(|v| *v += 1).or_insert(1);
        }
    }
    pub fn report_unused(&self) -> Vec<String> {
        let mut res = BTreeSet::new();
        self.tree.traverse(&mut vec![], &mut res);
        for k in self.stats.keys() {
            res.remove(k);
        }
        res.remove(&vec![]);
        res.into_iter().map(|v| v.join(".")).collect()
    }
    pub fn get_stats(mut self) -> BTreeMap<String, u32> {
        let mut res = BTreeSet::new();
        self.tree.traverse(&mut vec![], &mut res);
        for e in res {
            self.stats.entry(e).or_insert(0);
        }
        self.stats
            .into_iter()
            .map(|(k, v)| (k.join("."), v))
            .collect()
    }
    fn update_config_source(&mut self, delta: Vec<String>, path: &[String]) {
        for field in delta {
            self.config_source.insert(field, path.to_vec());
        }
    }
    fn to_backup(&self) -> ConfigBackup<T> {
        ConfigBackup {
            config: self.config.clone(),
            config_source: self.config_source.clone(),
        }
    }
    fn restore_from_backup(&mut self, bak: ConfigBackup<T>) {
        self.config = bak.config;
        self.config_source = bak.config_source;
    }
}
#[derive(Debug)]
pub struct Context<'a> {
    pub elem: &'a StateElem<'a>,
    pub is_recursive: bool,
}

pub trait ConfigState: DeserializeOwned + Default + Clone + std::fmt::Debug {
    /// Specifies the merging semantics of two configs, returns a vector of updated config fields.
    fn merge_config(&mut self, config: &Self, ctx: Option<Context>) -> Vec<String>;
    fn update_state(&mut self, elem: &StateElem);
    fn restore_state(&mut self, elem: &StateElem);
    /// List the properties in the current config, used for analyzing unused properties.
    fn list_properties(&self) -> Vec<String>;
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
        // TODO: correctly count the depth of scoped paths
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
    /// Returns the config, is_recursive, and the index of the matched path
    pub fn get_config(&self, path: &[String]) -> Option<(&T, bool, usize)> {
        let len = path.len();
        assert!(len > 0);
        let start = len.saturating_sub(self.max_depth as usize);
        for i in (start..len).rev() {
            let (path, tail) = path.split_at(i);
            match self.match_exact_path(tail) {
                Some(v) => return Some((v, is_repeated(path, tail), i)),
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
    pub fn traverse(&self, path: &mut Vec<String>, res: &mut BTreeSet<Vec<String>>) {
        if let Some(state) = &self.state {
            for prop in state.list_properties() {
                let mut path = path.clone();
                path.push(prop);
                res.insert(path);
            }
        }
        for (k, v) in self.subtree.iter() {
            path.push(k.clone());
            v.traverse(path, res);
            path.pop();
        }
    }
}
#[derive(Clone)]
pub struct Configs(pub Table);
impl Configs {
    pub fn get_subtable(&self, path: &[String]) -> Option<&Table> {
        let mut res = &self.0;
        for k in path {
            match res.get(k)? {
                Value::Table(t) => res = t,
                _ => return None,
            }
        }
        Some(res)
    }
}
impl std::str::FromStr for Configs {
    type Err = crate::Error;
    fn from_str(v: &str) -> Result<Self, Self::Err> {
        let v = v.parse::<Table>()?;
        Ok(Configs(v))
    }
}
impl std::fmt::Display for StateElem<'_> {
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
pub fn is_scoped_key(key: &str) -> bool {
    key.starts_with("func:") || key.starts_with("arg:") || key.starts_with("ret:")
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
                    let dep = if is_scoped_key(&k) {
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
fn path_name(t: &Type) -> String {
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
        TypeInner::Class(..) => "func:init",
        TypeInner::Unknown => unreachable!(),
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
        fn merge_config(&mut self, config: &Self, ctx: Option<Context>) -> Vec<String> {
            let mut res = vec!["depth", "text", "size"];
            *self = config.clone();
            if ctx.is_some_and(|c| c.is_recursive) {
                self.size = Some(0);
                res.pop();
            }
            res.into_iter().map(|f| f.to_string()).collect()
        }
        fn update_state(&mut self, _elem: &StateElem) {
            self.size = self.size.map(|s| s + 1);
        }
        fn restore_state(&mut self, _elem: &StateElem) {
            self.size = self.size.map(|s| s - 1);
        }
        fn list_properties(&self) -> Vec<String> {
            let mut res = Vec::new();
            if self.depth.is_some() {
                res.push("depth");
            }
            if self.size.is_some() {
                res.push("size");
            }
            if self.text.is_some() {
                res.push("text");
            }
            res.into_iter().map(|f| f.to_string()).collect()
        }
    }
    let toml = r#"
[random]
list = { depth = 20, size = 50 }
val.text = "42"
left.list = { depth = 1 }
vec.nat8.text = "blob"
Vec = { width = 2, size = 10 }
"func:f"."arg:0".list = { depth = 2, size = 20 }
"func:f".list = { depth = 3, size = 30 }
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
    assert_eq!(state.open_path, vec!["func:f", "arg:0"]);
    let old = state.push_state(&StateElem::Label("list"));
    state.update_stats("depth");
    state.update_stats("size");
    state.update_stats("text");
    assert_eq!(state.config.depth, Some(2));
    assert_eq!(state.config.size, Some(20));
    assert_eq!(state.config.text, None);
    assert_eq!(
        state.config_source.get("depth").unwrap().join("."),
        "func:f.arg:0.list"
    );
    assert_eq!(old.config.size, None);
    state.push_state(&StateElem::Label("val"));
    state.update_stats("text");
    assert_eq!(state.config.text, Some("42".to_string()));
    state.with_scope(
        &Some(Scope {
            method: "f",
            position: Some(ScopePos::Ret),
        }),
        0,
    );
    assert_eq!(state.open_path, vec!["func:f"]);
    state.push_state(&StateElem::Label("list"));
    state.update_stats("depth");
    state.update_stats("size");
    assert_eq!(state.config.depth, Some(3));
    assert_eq!(state.config.size, Some(0));
    assert_eq!(
        state.config_source.get("depth").unwrap().join("."),
        "func:f.list"
    );
    assert_eq!(state.config_source.get("size").unwrap().join("."), "val");
    state.with_scope(&None, 0);
    let old = state.push_state(&StateElem::Label("list"));
    state.update_stats("depth");
    state.update_stats("size");
    assert_eq!(state.config.depth, Some(20));
    assert_eq!(state.config.size, Some(0));
    assert_eq!(state.config_source.get("depth").unwrap().join("."), "list");
    assert_eq!(state.config_source.get("size").unwrap().join("."), "val");
    assert_eq!(old.config.size, Some(1));
    state.pop_state(old, StateElem::Label("list"));
    state.update_stats("size");
    state.update_stats("depth");
    assert_eq!(state.config.size, Some(0));
    assert_eq!(state.config.depth, Some(3));
    let stats = state.report_unused();
    assert_eq!(
        stats.iter().map(|x| x.as_str()).collect::<Vec<&str>>(),
        [
            "Vec.size",
            "a.b.c.d.depth",
            "a.b.c.depth",
            "a.b.d.depth",
            "depth",
            "func:f.list.size",
            "left.a.depth",
            "left.list.depth",
            "list.size",
            "vec.nat8.text"
        ]
    );
}
