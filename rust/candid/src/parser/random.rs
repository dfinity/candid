use super::typing::TypeEnv;
use super::value::{IDLArgs, IDLField, IDLValue};
use crate::types::{Field, Type};
use crate::Result;
use arbitrary::Unstructured;
use std::cell::Cell;
use std::collections::HashMap;

const MAX_DEPTH: usize = 20;

pub struct GenConfig {
    range: (usize, usize),
    text: &'static str, // regex or pattern
    depth: Cell<usize>,
    size: Cell<usize>,
}

pub struct GenTable(HashMap<Type, GenConfig>);

impl Default for GenConfig {
    fn default() -> Self {
        GenConfig {
            range: (0, 100),
            text: "ascii",
            depth: Cell::new(10),
            size: Cell::new(100),
        }
    }
}
impl GenConfig {
    fn dec(&self, dsize: usize) {
        let size = self.size.get();
        let depth = self.depth.get();
        if size < dsize {
            self.size.set(0)
        } else {
            self.size.set(size - dsize)
        };
        if depth > 0 {
            self.depth.set(depth - 1);
        }
    }
    fn inc(&self) {
        self.depth.set(self.depth.get() + 1);
    }
}

impl IDLArgs {
    pub fn any(u: &mut Unstructured, env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut args = Vec::new();
        for t in types.iter() {
            let config = GenConfig::default();
            let v = IDLValue::any(u, &config, env, t)?;
            args.push(v);
        }
        Ok(IDLArgs { args })
    }
}

impl TypeEnv {
    /// Return the upper bound of the depth
    fn depth(&self, limit: usize, t: &Type) -> usize {
        // TODO memoize
        use Type::*;
        if limit == 0 {
            return 1;
        }
        match t {
            Var(id) => {
                let ty = self.rec_find_type(id).unwrap();
                self.depth(limit, &ty)
            }
            Empty => 0,
            Opt(t) => 1 + self.depth(limit - 1, t),
            Vec(t) => 1 + self.depth(limit - 1, t),
            Record(fs) | Variant(fs) => {
                1 + fs
                    .iter()
                    .map(|Field { ty, .. }| self.depth(limit - 1, ty))
                    .max()
                    .unwrap_or(0)
            }
            _ => 1,
        }
    }
    /// lower and upper bound for size
    fn size(&self, limit: usize, t: &Type) -> (usize, usize) {
        use Type::*;
        if limit == 0 {
            return (1, 1);
        }
        match t {
            Var(id) => {
                let ty = self.rec_find_type(id).unwrap();
                self.size(limit, &ty)
            }
            Empty => (0, 0),
            Opt(t) => {
                let (_, u) = self.size(limit - 1, t);
                (1, 1 + u)
            }
            Vec(t) => {
                let (_, u) = self.size(limit - 1, t);
                (1, 1 + u * 2)
            }
            Record(fs) => {
                let iter = fs.iter().map(|Field { ty, .. }| self.size(limit - 1, ty));
                let l: usize = iter.clone().map(|e| e.0).sum();
                let r: usize = iter.map(|e| e.1).sum();
                (1 + l, 1 + r)
            }
            Variant(fs) => {
                let iter = fs.iter().map(|Field { ty, .. }| self.size(limit - 1, ty));
                let l = std::cmp::max(1, iter.clone().map(|e| e.0).min().unwrap());
                let r = iter.map(|e| e.1).max().unwrap();
                (1 + l, 1 + r)
            }
            _ => (1, 1),
        }
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

impl IDLValue {
    pub fn any(u: &mut Unstructured, config: &GenConfig, env: &TypeEnv, ty: &Type) -> Result<Self> {
        config.dec(1);
        println!("{} {}", config.depth.get(), config.size.get());
        Ok(match ty {
            Type::Var(id) => {
                let ty = env.rec_find_type(id)?;
                config.inc();
                Self::any(u, config, env, &ty)?
            }
            Type::Null => IDLValue::Null,
            Type::Reserved => IDLValue::Reserved,
            Type::Bool => IDLValue::Bool(u.arbitrary()?),
            Type::Nat => {
                let v = u.int_in_range(config.range.0..=config.range.1)?;
                IDLValue::Nat(v.into())
            }
            //Type::Nat => IDLValue::Nat(u.arbitrary::<u128>()?.into()),
            Type::Int => IDLValue::Int(u.arbitrary::<i128>()?.into()),
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
                let depths = if config.depth.get() == 0 || config.size.get() == 0 {
                    [1, 0]
                } else {
                    [1, env.depth(MAX_DEPTH, t)]
                };
                let idx = arbitrary_variant(u, &depths)?;
                if idx == 0 {
                    IDLValue::None
                } else {
                    let res = IDLValue::Opt(Box::new(Self::any(u, config, env, t)?));
                    config.inc();
                    res
                }
            }
            Type::Vec(t) => {
                let (lower, _) = env.size(MAX_DEPTH, t);
                let max_len = config.size.get() / (lower * 2);
                let len = u.int_in_range(0..=max_len)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    let e = Self::any(u, config, env, t)?;
                    config.inc();
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            Type::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    let val = Self::any(u, config, env, ty)?;
                    config.inc();
                    res.push(IDLField {
                        id: id.clone(),
                        val,
                    });
                }
                IDLValue::Record(res)
            }
            Type::Variant(fs) => {
                let choices = fs.iter().map(|Field { ty, .. }| env.depth(MAX_DEPTH, ty));
                let sizes: Vec<_> = if config.depth.get() == 0 || config.size.get() == 0 {
                    let min = choices.clone().min().unwrap_or(0);
                    choices.map(|d| if d > min { 0 } else { d }).collect()
                } else {
                    choices.collect()
                };
                let idx = arbitrary_variant(u, &sizes)?;
                let Field { id, ty } = &fs[idx];
                let val = Self::any(u, config, env, ty)?;
                config.inc();
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
