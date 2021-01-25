use super::configs::Configs;
use super::typing::TypeEnv;
use super::value::{IDLArgs, IDLField, IDLValue};
use crate::types::{Field, Type};
use crate::Deserialize;
use crate::Result;
use arbitrary::Unstructured;
use std::collections::HashSet;

const MAX_DEPTH: usize = 20;

#[derive(Debug, Deserialize)]
pub struct GenConfig {
    range: Option<(isize, isize)>,
    text: Option<String>, // regex or pattern
    value: Option<IDLValue>,
    // Only work for global scope
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
pub struct GenState<'a> {
    config: GenConfig,
    tree: Configs,
    env: &'a TypeEnv,
    depth: isize,
    size: isize,
}
impl<'a> GenState<'a> {
    fn new(tree: Configs, env: &'a TypeEnv) -> Result<Self> {
        let config = tree.get::<GenConfig>("default")?; //GenConfig::default();
        Ok(GenState {
            depth: config.depth.unwrap_or(5),
            size: config.size.unwrap_or(50),
            tree,
            config,
            env,
        })
    }
    pub fn any(&mut self, u: &mut Unstructured, ty: &Type) -> Result<IDLValue> {
        self.size -= 1;
        Ok(match ty {
            Type::Var(id) => {
                let ty = self.env.rec_find_type(id)?;
                self.size += 1;
                self.any(u, &ty)?
            }
            Type::Null => IDLValue::Null,
            Type::Reserved => IDLValue::Reserved,
            Type::Bool => IDLValue::Bool(u.arbitrary()?),
            Type::Int => {
                let v =
                    u.int_in_range(self.config.range.unwrap().0..=self.config.range.unwrap().1)?;
                IDLValue::Int(v.into())
            }
            Type::Nat => IDLValue::Nat(u.arbitrary::<u128>()?.into()),
            //Type::Int => IDLValue::Int(u.arbitrary::<i128>()?.into()),
            Type::Nat8 => IDLValue::Nat8(u.arbitrary()?),
            Type::Nat16 => IDLValue::Nat16(u.arbitrary()?),
            Type::Nat32 => IDLValue::Nat32(u.arbitrary()?),
            Type::Nat64 => IDLValue::Nat64(u.arbitrary()?),
            Type::Int8 => IDLValue::Int8(u.arbitrary()?),
            Type::Int16 => IDLValue::Int16(u.arbitrary()?),
            Type::Int32 => IDLValue::Int32(u.arbitrary()?),
            Type::Int64 => IDLValue::Int64(u.arbitrary()?),
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
                    self.depth -= 1;
                    let res = IDLValue::Opt(Box::new(self.any(u, t)?));
                    self.depth += 1;
                    res
                }
            }
            Type::Vec(t) => {
                let elem_size = self.env.size(t).unwrap_or(MAX_DEPTH);
                let max_len = std::cmp::max(0, self.size) as usize / elem_size;
                let len = u.int_in_range(0..=max_len)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    self.depth -= 1;
                    let e = self.any(u, t)?;
                    self.depth += 1;
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            Type::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    self.depth -= 1;
                    let val = self.any(u, ty)?;
                    self.depth += 1;
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
                self.depth -= 1;
                let val = self.any(u, ty)?;
                self.depth += 1;
                let field = IDLField {
                    id: id.clone(),
                    val,
                };
                IDLValue::Variant(Box::new(field), idx as u64)
            }
            _ => unimplemented!(),
        })
    }
}

impl IDLArgs {
    pub fn any(u: &mut Unstructured, tree: Configs, env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut state = GenState::new(tree, env)?;
        let mut args = Vec::new();
        for t in types.iter() {
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
