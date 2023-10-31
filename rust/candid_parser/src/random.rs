use super::configs::{path_name, Configs};
use crate::{Error, Result};
use arbitrary::{unstructured::Int, Arbitrary, Unstructured};
use candid::types::value::{IDLArgs, IDLField, IDLValue, VariantValue};
use candid::types::{Field, Type, TypeEnv, TypeInner};
use candid::Deserialize;
use std::collections::HashSet;
use std::convert::TryFrom;

const MAX_DEPTH: usize = 20;

#[derive(Debug, Deserialize, Clone)]
pub struct GenConfig {
    range: Option<(i64, i64)>,
    text: Option<String>,
    width: Option<usize>,
    value: Option<Vec<String>>,
    depth: Option<isize>,
    size: Option<isize>,
}
impl Default for GenConfig {
    fn default() -> Self {
        GenConfig {
            range: None,
            text: Some("ascii".to_string()),
            width: Some(10),
            value: None,
            depth: Some(10),
            size: Some(100),
        }
    }
}
impl GenConfig {
    pub fn update(&self, config: GenConfig, recursive: bool) -> GenConfig {
        // TODO support removing properties
        let old = self.clone();
        GenConfig {
            range: config.range.or(old.range),
            text: config.text.or(old.text),
            value: config.value.or(old.value),
            width: config.width.or(old.width),
            // These properties only update when it's not inside a recursion.
            depth: if recursive { None } else { config.depth },
            size: if recursive { None } else { config.size },
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
    fn new(tree: &'a Configs, env: &'a TypeEnv) -> Self {
        let mut config = GenConfig::default();
        if let Some((global_config, _)) = tree.get::<GenConfig>(&[]) {
            config = config.update(global_config, false);
        }
        GenState {
            depth: config.depth.take().unwrap_or(5),
            size: config.size.take().unwrap_or(50),
            tree,
            config,
            env,
            path: Vec::new(),
        }
    }
    // Update state and return the old config state. Label and var type are cost free.
    fn push_state(&mut self, ty: &Type, label: Option<String>) -> GenConfig {
        let elem = if let Some(lab) = label {
            lab
        } else {
            match ty.as_ref() {
                TypeInner::Var(_) => (),
                _ => {
                    self.depth -= 1;
                    self.size -= 1;
                }
            }
            path_name(ty)
        };
        let mut old_config = self.config.clone();
        self.path.push(elem);
        if let Some((config, recursive)) = self.tree.get::<GenConfig>(&self.path) {
            self.config = self.config.update(config, recursive);
        }
        // Current depth and size are stored in old_config for pop_state to restore states.
        old_config.depth = Some(self.depth);
        old_config.size = Some(self.size);
        self.depth = self.config.depth.take().unwrap_or(self.depth);
        self.size = self.config.size.take().unwrap_or(self.size);
        old_config
    }
    fn pop_state(&mut self, old_config: GenConfig, ty: &Type, is_label: bool) {
        if !is_label {
            match ty.as_ref() {
                TypeInner::Var(_) => (),
                _ => {
                    self.depth += 1;
                }
            }
        }
        self.path.pop();
        self.config = old_config;
        self.depth = self.config.depth.take().unwrap();
        self.size = self.config.size.take().unwrap();
    }
    pub fn any(&mut self, u: &mut Unstructured, ty: &Type) -> Result<IDLValue> {
        let old_config = self.push_state(ty, None);
        assert!(self.config.depth.is_none());
        if let Some(vec) = &self.config.value {
            let v = u.choose(vec)?;
            let v: IDLValue = super::parse_idl_value(v)?;
            let v = v.annotate_type(true, self.env, ty)?;
            self.pop_state(old_config, ty, false);
            return Ok(v);
        }
        let res = Ok(match ty.as_ref() {
            TypeInner::Var(id) => {
                let ty = self.env.rec_find_type(id)?;
                self.any(u, ty)?
            }
            TypeInner::Null => IDLValue::Null,
            TypeInner::Reserved => IDLValue::Reserved,
            TypeInner::Bool => IDLValue::Bool(u.arbitrary()?),
            TypeInner::Int => IDLValue::Int(arbitrary_num::<i128>(u, self.config.range)?.into()),
            TypeInner::Nat => IDLValue::Nat(arbitrary_num::<u128>(u, self.config.range)?.into()),
            TypeInner::Nat8 => IDLValue::Nat8(arbitrary_num(u, self.config.range)?),
            TypeInner::Nat16 => IDLValue::Nat16(arbitrary_num(u, self.config.range)?),
            TypeInner::Nat32 => IDLValue::Nat32(arbitrary_num(u, self.config.range)?),
            TypeInner::Nat64 => IDLValue::Nat64(arbitrary_num(u, self.config.range)?),
            TypeInner::Int8 => IDLValue::Int8(arbitrary_num(u, self.config.range)?),
            TypeInner::Int16 => IDLValue::Int16(arbitrary_num(u, self.config.range)?),
            TypeInner::Int32 => IDLValue::Int32(arbitrary_num(u, self.config.range)?),
            TypeInner::Int64 => IDLValue::Int64(arbitrary_num(u, self.config.range)?),
            TypeInner::Float32 => IDLValue::Float32(u.arbitrary()?),
            TypeInner::Float64 => IDLValue::Float64(u.arbitrary()?),
            TypeInner::Text => {
                IDLValue::Text(arbitrary_text(u, &self.config.text, &self.config.width)?)
            }
            TypeInner::Opt(t) => {
                let depths = if self.depth <= 0 || self.size <= 0 {
                    [1, 0]
                } else {
                    [1, size(self.env, t).unwrap_or(MAX_DEPTH)]
                };
                let idx = arbitrary_variant(u, &depths)?;
                if idx == 0 {
                    IDLValue::None
                } else {
                    IDLValue::Opt(Box::new(self.any(u, t)?))
                }
            }
            TypeInner::Vec(t) => {
                let width = self.config.width.or_else(|| {
                    let elem_size = size(self.env, t).unwrap_or(MAX_DEPTH);
                    Some(std::cmp::max(0, self.size) as usize / elem_size)
                });
                let len = arbitrary_len(u, width)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    let e = self.any(u, t)?;
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            TypeInner::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    let old_config = self.push_state(ty, Some(id.to_string()));
                    let val = self.any(u, ty)?;
                    self.pop_state(old_config, ty, true);
                    res.push(IDLField {
                        id: id.as_ref().clone(),
                        val,
                    });
                }
                IDLValue::Record(res)
            }
            TypeInner::Variant(fs) => {
                let choices = fs
                    .iter()
                    .map(|Field { ty, .. }| size(self.env, ty).unwrap_or(MAX_DEPTH));
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
                    id: id.as_ref().clone(),
                    val,
                };
                IDLValue::Variant(VariantValue(Box::new(field), idx as u64))
            }
            TypeInner::Principal => IDLValue::Principal(crate::Principal::arbitrary(u)?),
            TypeInner::Func(_) => IDLValue::Func(
                crate::Principal::arbitrary(u)?,
                arbitrary_text(u, &self.config.text, &self.config.width)?,
            ),
            TypeInner::Service(_) => IDLValue::Service(crate::Principal::arbitrary(u)?),
            _ => unimplemented!(),
        });
        self.pop_state(old_config, ty, false);
        res
    }
}

pub fn any(seed: &[u8], tree: &Configs, env: &TypeEnv, types: &[Type]) -> Result<IDLArgs> {
    let mut u = arbitrary::Unstructured::new(seed);
    let mut args = Vec::new();
    for (i, t) in types.iter().enumerate() {
        let tree = tree.with_method(&i.to_string());
        let mut state = GenState::new(&tree, env);
        let v = state.any(&mut u, t)?;
        args.push(v);
    }
    Ok(IDLArgs { args })
}

fn size_helper(env: &TypeEnv, seen: &mut HashSet<String>, t: &Type) -> Option<usize> {
    use TypeInner::*;
    Some(match t.as_ref() {
        Var(id) => {
            if seen.insert(id.to_string()) {
                let ty = env.rec_find_type(id).unwrap();
                let res = size_helper(env, seen, ty)?;
                seen.remove(id);
                res
            } else {
                return None;
            }
        }
        Empty => 0,
        Opt(t) => 1 + size_helper(env, seen, t)?,
        Vec(t) => 1 + size_helper(env, seen, t)? * 2,
        Record(fs) => {
            let mut sum = 0;
            for Field { ty, .. } in fs.iter() {
                sum += size_helper(env, seen, ty)?;
            }
            1 + sum
        }
        Variant(fs) => {
            let mut max = 0;
            for Field { ty, .. } in fs.iter() {
                let s = size_helper(env, seen, ty)?;
                if s > max {
                    max = s;
                };
            }
            1 + max
        }
        _ => 1,
    })
}

fn size(env: &TypeEnv, t: &Type) -> Option<usize> {
    let mut seen = HashSet::new();
    size_helper(env, &mut seen, t)
}

fn choose_range<T: Int>(u: &mut Unstructured, ranges: &[std::ops::RangeInclusive<T>]) -> Result<T> {
    let range = u.choose(ranges)?.clone();
    Ok(u.int_in_range(range)?)
}

fn arbitrary_text(
    u: &mut Unstructured,
    text: &Option<String>,
    width: &Option<usize>,
) -> Result<String> {
    use fake::{faker::*, Fake};
    use rand::SeedableRng;
    let seed = u.arbitrary::<u64>()?;
    let r = &mut rand::rngs::StdRng::seed_from_u64(seed);
    let kind = text.as_ref().map(|x| x.as_str());
    Ok(match kind {
        Some("name") => name::en::Name().fake_with_rng(r),
        Some("name.cn") => name::zh_cn::Name().fake_with_rng(r),
        Some("path") => filesystem::en::FilePath().fake_with_rng(r),
        Some("country") => address::en::CountryName().fake_with_rng(r),
        Some("company") => company::en::CompanyName().fake_with_rng(r),
        Some("bs") => company::en::Bs().fake_with_rng(r),
        _ => {
            let len = arbitrary_len(u, *width)?;
            let mut res = String::with_capacity(len);
            for _ in 0..len {
                let ch = match kind {
                    Some("emoji") => choose_range(u, &[0x1f300..=0x1f53d, 0x1f5fa..=0x1fa73])?,
                    Some("ascii") => u.int_in_range(0x20..=0x7e)?,
                    None => choose_range(
                        u,
                        &[
                            0x00..=0x7f,
                            0x80..=0x7ff,
                            0x800..=0xffff,
                            0x10000..=0x10ffff,
                        ],
                    )?,
                    _ => return Err(Error::msg(format!("Unknown text config {kind:?}"))),
                };
                if let Some(ch) = std::char::from_u32(ch) {
                    res.push(ch);
                }
            }
            res
        }
    })
}

fn arbitrary_len(u: &mut Unstructured, width: Option<usize>) -> Result<usize> {
    Ok(if let Some(w) = width {
        u.int_in_range(0..=w)?
    } else {
        u.arbitrary_len::<u8>()?
    })
}

fn arbitrary_num<'a, T>(u: &mut Unstructured<'a>, range: Option<(i64, i64)>) -> Result<T>
where
    T: num_traits::Bounded + Int + TryFrom<i64> + Arbitrary<'a>,
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
    Err(Error::msg("empty variant"))
}
