use super::typing::TypeEnv;
use super::value::{IDLArgs, IDLField, IDLValue};
use crate::types::{Field, Type};
use crate::Result;
use arbitrary::Unstructured;
use std::collections::HashSet;

const MAX_DEPTH: usize = 20;

pub struct GenConfig {
    range: (isize, isize),
    text: &'static str, // regex or pattern
    depth: isize,
    size: isize,
}

impl Default for GenConfig {
    fn default() -> Self {
        GenConfig {
            range: (0, 100),
            text: "ascii",
            depth: 5,
            size: 100,
        }
    }
}
impl GenConfig {
    pub fn any(&mut self, u: &mut Unstructured, env: &TypeEnv, ty: &Type) -> Result<IDLValue> {
        self.size -= 1;
        Ok(match ty {
            Type::Var(id) => {
                let ty = env.rec_find_type(id)?;
                self.size += 1;
                self.any(u, env, &ty)?
            }
            Type::Null => IDLValue::Null,
            Type::Reserved => IDLValue::Reserved,
            Type::Bool => IDLValue::Bool(u.arbitrary()?),
            Type::Int => {
                let v = u.int_in_range(self.range.0..=self.range.1)?;
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
                    [1, env.size(t).unwrap_or(MAX_DEPTH)]
                };
                let idx = arbitrary_variant(u, &depths)?;
                if idx == 0 {
                    IDLValue::None
                } else {
                    self.depth -= 1;
                    let res = IDLValue::Opt(Box::new(self.any(u, env, t)?));
                    self.depth += 1;
                    res
                }
            }
            Type::Vec(t) => {
                let elem_size = env.size(t).unwrap_or(MAX_DEPTH);
                let max_len = std::cmp::max(0, self.size) as usize / elem_size;
                let len = u.int_in_range(0..=max_len)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    self.depth -= 1;
                    let e = self.any(u, env, t)?;
                    self.depth += 1;
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            Type::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    self.depth -= 1;
                    let val = self.any(u, env, ty)?;
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
                    .map(|Field { ty, .. }| env.size(ty).unwrap_or(MAX_DEPTH));
                let sizes: Vec<_> = if self.depth <= 0 || self.size <= 0 {
                    let min = choices.clone().min().unwrap_or(0);
                    choices.map(|d| if d > min { 0 } else { d }).collect()
                } else {
                    choices.collect()
                };
                let idx = arbitrary_variant(u, &sizes)?;
                let Field { id, ty } = &fs[idx];
                self.depth -= 1;
                let val = self.any(u, env, ty)?;
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
    pub fn any(u: &mut Unstructured, env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut args = Vec::new();
        for t in types.iter() {
            let mut config = GenConfig::default();
            let v = config.any(u, env, t)?;
            args.push(v);
        }
        Ok(IDLArgs { args })
    }
}

impl TypeEnv {
    /// Upper bound of type size. Returns None if infinite.
    fn size_helper(&self, seen: &mut HashSet<String>, t: &Type) -> Option<usize> {
        use Type::*;
        Some(match t {
            Var(id) => {
                if seen.insert(id.to_string()) {
                    let ty = self.rec_find_type(id).unwrap();
                    self.size_helper(seen, &ty)?
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
