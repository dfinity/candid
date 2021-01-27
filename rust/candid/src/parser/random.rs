use super::configs::{path_name, Configs};
use super::typing::TypeEnv;
use super::value::{IDLArgs, IDLField, IDLValue};
use crate::types::{Field, Type};
use crate::Deserialize;
use crate::Result;
use arbitrary::{unstructured::Int, Arbitrary, Unstructured};
use std::collections::HashSet;
use std::convert::TryFrom;

const MAX_DEPTH: usize = 20;

#[derive(Debug, Deserialize, Clone)]
pub struct GenConfig {
    range: Option<(i64, i64)>,
    text: Option<String>, // regex or pattern
    value: Option<IDLValue>,
    depth: Option<isize>,
    size: Option<isize>,
}
impl Default for GenConfig {
    fn default() -> Self {
        GenConfig {
            range: Some((0, 100)),
            text: Some("ascii".to_string()),
            value: None,
            depth: Some(5),
            size: Some(100),
        }
    }
}
impl GenConfig {
    pub fn update(&self, config: GenConfig) -> GenConfig {
        // TODO support removing properties
        let old = self.clone();
        GenConfig {
            range: config.range.or(old.range),
            text: config.text.or(old.text),
            value: config.value.or(old.value),
            depth: config.depth.or(old.depth),
            size: config.size.or(old.size),
        }
    }
}

pub struct GenState<'a> {
    tree: &'a Configs,
    env: &'a TypeEnv,
    // state
    path: Vec<String>,
    config: GenConfig,
    depth: isize,
    size: isize,
}
impl<'a> GenState<'a> {
    fn new(tree: &'a Configs, env: &'a TypeEnv) -> Result<Self> {
        let config = tree.get::<GenConfig>(&["default".to_string()]).unwrap(); //GenConfig::default();
        Ok(GenState {
            depth: config.depth.unwrap_or(5),
            size: config.size.unwrap_or(50),
            tree,
            config,
            env,
            path: Vec::new(),
        })
    }
    // Update state and return the old config state. Label and var type are cost free.
    fn push_state(&mut self, ty: &Type, label: Option<String>) -> GenConfig {
        let elem = if let Some(lab) = label {
            lab
        } else {
            match ty {
                Type::Var(_) => (),
                _ => {
                    self.depth -= 1;
                    self.size -= 1;
                }
            }
            path_name(ty)
        };
        let old_config = self.config.clone();
        self.path.push(elem);
        if let Some(config) = self.tree.get::<GenConfig>(&self.path) {
            self.config = self.config.update(config);
        }
        old_config
    }
    fn pop_state(&mut self, old_config: GenConfig, ty: &Type, is_label: bool) {
        if !is_label {
            match ty {
                Type::Var(_) => (),
                _ => {
                    self.depth += 1;
                }
            }
        }
        self.path.pop();
        self.config = old_config;
    }
    pub fn any(&mut self, u: &mut Unstructured, ty: &Type) -> Result<IDLValue> {
        let old_config = self.push_state(ty, None);
        if let Some(v) = &self.config.value {
            let v = v.clone();
            self.pop_state(old_config, ty, false);
            return Ok(v);
        }
        let res = Ok(match ty {
            Type::Var(id) => {
                let ty = self.env.rec_find_type(id)?;
                self.any(u, &ty)?
            }
            Type::Null => IDLValue::Null,
            Type::Reserved => IDLValue::Reserved,
            Type::Bool => IDLValue::Bool(u.arbitrary()?),
            Type::Int => IDLValue::Int(arbitrary_num::<i128>(u, self.config.range)?.into()),
            Type::Nat => IDLValue::Nat(arbitrary_num::<u128>(u, self.config.range)?.into()),
            Type::Nat8 => IDLValue::Nat8(arbitrary_num(u, self.config.range)?),
            Type::Nat16 => IDLValue::Nat16(arbitrary_num(u, self.config.range)?),
            Type::Nat32 => IDLValue::Nat32(arbitrary_num(u, self.config.range)?),
            Type::Nat64 => IDLValue::Nat64(arbitrary_num(u, self.config.range)?),
            Type::Int8 => IDLValue::Int8(arbitrary_num(u, self.config.range)?),
            Type::Int16 => IDLValue::Int16(arbitrary_num(u, self.config.range)?),
            Type::Int32 => IDLValue::Int32(arbitrary_num(u, self.config.range)?),
            Type::Int64 => IDLValue::Int64(arbitrary_num(u, self.config.range)?),
            Type::Float32 => IDLValue::Float32(u.arbitrary()?),
            Type::Float64 => IDLValue::Float64(u.arbitrary()?),
            Type::Text => IDLValue::Text(u.arbitrary()?),
            Type::Principal => IDLValue::Principal(crate::Principal::anonymous()),
            Type::Opt(t) => {
                let depths = if self.depth <= 0 || self.size <= 0 {
                    [1, 0]
                } else {
                    [1, self.env.size(t).unwrap_or(MAX_DEPTH)]
                };
                let idx = arbitrary_variant(u, &depths)?;
                if idx == 0 {
                    IDLValue::None
                } else {
                    IDLValue::Opt(Box::new(self.any(u, t)?))
                }
            }
            Type::Vec(t) => {
                let elem_size = self.env.size(t).unwrap_or(MAX_DEPTH);
                let max_len = std::cmp::max(0, self.size) as usize / elem_size;
                let len = u.int_in_range(0..=max_len)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    let e = self.any(u, t)?;
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            Type::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    let old_config = self.push_state(ty, Some(id.to_string()));
                    let val = self.any(u, ty)?;
                    self.pop_state(old_config, ty, true);
                    res.push(IDLField {
                        id: id.clone(),
                        val,
                    });
                }
                IDLValue::Record(res)
            }
            Type::Variant(fs) => {
                let choices = fs
                    .iter()
                    .map(|Field { ty, .. }| self.env.size(ty).unwrap_or(MAX_DEPTH));
                let sizes: Vec<_> = if self.depth <= 0 || self.size <= 0 {
                    let min = choices.clone().min().unwrap_or(0);
                    choices.map(|d| if d > min { 0 } else { d }).collect()
                } else {
                    choices.collect()
                };
                let idx = arbitrary_variant(u, &sizes)?;
                let Field { id, ty } = &fs[idx];
                let old_config = self.push_state(ty, Some(id.to_string()));
                let val = self.any(u, ty)?;
                self.pop_state(old_config, ty, true);
                let field = IDLField {
                    id: id.clone(),
                    val,
                };
                IDLValue::Variant(Box::new(field), idx as u64)
            }
            _ => unimplemented!(),
        });
        self.pop_state(old_config, ty, false);
        res
    }
}

impl IDLArgs {
    pub fn any(
        u: &mut Unstructured,
        tree: &Configs,
        env: &TypeEnv,
        types: &[Type],
    ) -> Result<Self> {
        let mut args = Vec::new();
        for t in types.iter() {
            let mut state = GenState::new(tree, env)?;
            let v = state.any(u, t)?;
            args.push(v);
        }
        Ok(IDLArgs { args })
    }
}

impl TypeEnv {
    /// Approxiamte upper bound for IDLValue size of type t. Returns None if infinite.
    fn size_helper(&self, seen: &mut HashSet<String>, t: &Type) -> Option<usize> {
        use Type::*;
        Some(match t {
            Var(id) => {
                if seen.insert(id.to_string()) {
                    let ty = self.rec_find_type(id).unwrap();
                    let res = self.size_helper(seen, &ty)?;
                    seen.remove(id);
                    res
                } else {
                    return None;
                }
            }
            Empty => 0,
            Opt(t) => 1 + self.size_helper(seen, t)?,
            Vec(t) => 1 + self.size_helper(seen, t)? * 2,
            Record(fs) => {
                let mut sum = 0;
                for Field { ty, .. } in fs.iter() {
                    sum += self.size_helper(seen, ty)?;
                }
                1 + sum
            }
            Variant(fs) => {
                let mut max = 0;
                for Field { ty, .. } in fs.iter() {
                    let s = self.size_helper(seen, ty)?;
                    if s > max {
                        max = s;
                    };
                }
                1 + max
            }
            _ => 1,
        })
    }
    fn size(&self, t: &Type) -> Option<usize> {
        let mut seen = HashSet::new();
        self.size_helper(&mut seen, t)
    }
}

fn arbitrary_num<T>(u: &mut Unstructured, range: Option<(i64, i64)>) -> Result<T>
where
    T: num_traits::Bounded + Int + TryFrom<i64> + Arbitrary,
{
    Ok(match range {
        None => u.arbitrary::<T>()?,
        Some((l, r)) => {
            let min = T::min_value();
            let max = T::max_value();
            let l = T::try_from(l).unwrap_or(min);
            let r = T::try_from(r).unwrap_or(max);
            u.int_in_range(l..=r)?
        }
    })
}

fn arbitrary_variant(u: &mut Unstructured, weight: &[usize]) -> Result<usize> {
    // TODO read from end of unstructured to improve stability
    let prefix_sum: Vec<_> = weight
        .iter()
        .scan(0, |sum, i| {
            *sum += i;
            Some(*sum)
        })
        .collect();
    let selected = u.int_in_range(0..=prefix_sum[prefix_sum.len() - 1] - 1)?;
    for (i, e) in prefix_sum.iter().enumerate() {
        if selected < *e {
            return Ok(i);
        }
    }
    Err(crate::Error::msg("empty variant"))
}
