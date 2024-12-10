use super::configs::{ConfigState, Configs, Context, Scope, State, StateElem};
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
impl ConfigState for GenConfig {
    fn merge_config(&mut self, config: &Self, ctx: Option<Context>) -> Vec<String> {
        let mut res = Vec::new();
        if config.range.is_some() {
            self.range = config.range;
            res.push("range");
        }
        if config.text.is_some() {
            self.text.clone_from(&config.text);
            res.push("text");
        }
        if config.width.is_some() {
            self.width = config.width;
            res.push("width");
        }
        if config.value.is_some() {
            self.value.clone_from(&config.value);
            res.push("value");
        }
        if ctx.as_ref().is_some_and(|c| !c.is_recursive) {
            if config.depth.is_some() {
                self.depth = config.depth;
                res.push("depth");
            }
            if config.size.is_some() {
                self.size = config.size;
                res.push("size");
            }
        }
        res.into_iter().map(|s| s.to_string()).collect()
    }
    fn update_state(&mut self, elem: &StateElem) {
        if let StateElem::Type(t) = elem {
            if !matches!(t.as_ref(), TypeInner::Var(_)) {
                self.depth = self.depth.map(|d| d - 1);
                self.size = self.size.map(|s| s - 1);
            }
        }
    }
    fn restore_state(&mut self, elem: &StateElem) {
        if let StateElem::Type(t) = elem {
            if !matches!(t.as_ref(), TypeInner::Var(_)) {
                self.depth = self.depth.map(|d| d + 1);
            }
        }
    }
    fn unmatched_config() -> Self {
        GenConfig {
            range: None,
            text: None,
            width: None,
            value: None,
            depth: None,
            size: None,
        }
    }
    fn list_properties(&self) -> Vec<String> {
        let mut res = Vec::new();
        if self.range.is_some() {
            res.push("range".to_string());
        }
        if self.text.is_some() {
            res.push("text".to_string());
        }
        if self.width.is_some() {
            res.push("width".to_string());
        }
        if self.value.is_some() {
            res.push("value".to_string());
        }
        if self.depth.is_some() {
            res.push("depth".to_string());
        }
        if self.size.is_some() {
            res.push("size".to_string());
        }
        res
    }
}

pub struct RandState<'a>(State<'a, GenConfig>);
impl RandState<'_> {
    pub fn any(&mut self, u: &mut Unstructured, ty: &Type) -> Result<IDLValue> {
        let old_config = self.0.push_state(&StateElem::Type(ty));
        if let Some(vec) = &self.0.config.value {
            let v = u.choose(vec)?;
            let v: IDLValue = super::parse_idl_value(v)?;
            let v = v.annotate_type(true, self.0.env, ty)?;
            self.0.pop_state(old_config, StateElem::Type(ty));
            self.0.update_stats("value");
            return Ok(v);
        }
        let res = Ok(match ty.as_ref() {
            TypeInner::Var(id) => {
                let ty = self.0.env.rec_find_type(id)?;
                self.any(u, ty)?
            }
            TypeInner::Null => IDLValue::Null,
            TypeInner::Reserved => IDLValue::Reserved,
            TypeInner::Bool => IDLValue::Bool(u.arbitrary()?),
            TypeInner::Int => {
                self.0.update_stats("range");
                IDLValue::Int(arbitrary_num::<i128>(u, self.0.config.range)?.into())
            }
            TypeInner::Nat => {
                self.0.update_stats("range");
                IDLValue::Nat(arbitrary_num::<u128>(u, self.0.config.range)?.into())
            }
            TypeInner::Nat8 => {
                self.0.update_stats("range");
                IDLValue::Nat8(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Nat16 => {
                self.0.update_stats("range");
                IDLValue::Nat16(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Nat32 => {
                self.0.update_stats("range");
                IDLValue::Nat32(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Nat64 => {
                self.0.update_stats("range");
                IDLValue::Nat64(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Int8 => {
                self.0.update_stats("range");
                IDLValue::Int8(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Int16 => {
                self.0.update_stats("range");
                IDLValue::Int16(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Int32 => {
                self.0.update_stats("range");
                IDLValue::Int32(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Int64 => {
                self.0.update_stats("range");
                IDLValue::Int64(arbitrary_num(u, self.0.config.range)?)
            }
            TypeInner::Float32 => IDLValue::Float32(u.arbitrary()?),
            TypeInner::Float64 => IDLValue::Float64(u.arbitrary()?),
            TypeInner::Text => {
                self.0.update_stats("text");
                self.0.update_stats("width");
                IDLValue::Text(arbitrary_text(
                    u,
                    &self.0.config.text,
                    &self.0.config.width,
                )?)
            }
            TypeInner::Opt(t) => {
                self.0.update_stats("depth");
                self.0.update_stats("size");
                let depths = if self.0.config.depth.is_some_and(|d| d <= 0)
                    || self.0.config.size.is_some_and(|s| s <= 0)
                {
                    [1, 0]
                } else {
                    [1, size(self.0.env, t).unwrap_or(MAX_DEPTH)]
                };
                let idx = arbitrary_variant(u, &depths)?;
                if idx == 0 {
                    IDLValue::None
                } else {
                    IDLValue::Opt(Box::new(self.any(u, t)?))
                }
            }
            TypeInner::Vec(t) => {
                self.0.update_stats("width");
                let width = self.0.config.width.or_else(|| {
                    let elem_size = size(self.0.env, t).unwrap_or(MAX_DEPTH);
                    self.0.update_stats("size");
                    Some(std::cmp::max(0, self.0.config.size.unwrap_or(0)) as usize / elem_size)
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
                    let lab_str = id.to_string();
                    let elem = StateElem::Label(&lab_str);
                    let old_config = self.0.push_state(&elem);
                    let val = self.any(u, ty)?;
                    self.0.pop_state(old_config, elem);
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
                    .map(|Field { ty, .. }| size(self.0.env, ty).unwrap_or(MAX_DEPTH));
                self.0.update_stats("size");
                self.0.update_stats("depth");
                let sizes: Vec<_> = if self.0.config.depth.is_some_and(|d| d <= 0)
                    || self.0.config.size.is_some_and(|s| s <= 0)
                {
                    let min = choices.clone().min().unwrap_or(0);
                    choices.map(|d| if d > min { 0 } else { d }).collect()
                } else {
                    choices.collect()
                };
                let idx = arbitrary_variant(u, &sizes)?;
                let Field { id, ty } = &fs[idx];
                let lab_str = id.to_string();
                let elem = StateElem::Label(&lab_str);
                let old_config = self.0.push_state(&elem);
                let val = self.any(u, ty)?;
                self.0.pop_state(old_config, elem);
                let field = IDLField {
                    id: id.as_ref().clone(),
                    val,
                };
                IDLValue::Variant(VariantValue(Box::new(field), idx as u64))
            }
            TypeInner::Principal => IDLValue::Principal(crate::Principal::arbitrary(u)?),
            TypeInner::Func(_) => {
                self.0.update_stats("text");
                self.0.update_stats("width");
                IDLValue::Func(
                    crate::Principal::arbitrary(u)?,
                    arbitrary_text(u, &self.0.config.text, &self.0.config.width)?,
                )
            }
            TypeInner::Service(_) => IDLValue::Service(crate::Principal::arbitrary(u)?),
            _ => unimplemented!(),
        });
        self.0.pop_state(old_config, StateElem::Type(ty));
        res
    }
}

pub fn any(
    seed: &[u8],
    configs: Configs,
    env: &TypeEnv,
    types: &[Type],
    scope: &Option<Scope>,
) -> Result<IDLArgs> {
    let mut u = arbitrary::Unstructured::new(seed);
    let tree = super::configs::ConfigTree::from_configs("random", configs)?;
    let mut args = Vec::new();
    for (i, t) in types.iter().enumerate() {
        let mut state = State::new(&tree, env);
        state.with_scope(scope, i);
        let mut state = RandState(state);
        state.0.push_state(&StateElem::Label(&i.to_string()));
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
