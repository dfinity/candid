use super::internal::{find_type, Field, Label, Type, TypeInner};
use crate::types::TypeEnv;
use crate::utils::RecursionDepth;
use crate::{Error, Result};
use anyhow::Context;
use std::collections::{HashMap, HashSet};
use std::fmt;

pub type Gamma = HashSet<(Type, Type)>;

/// Error reporting style for the special opt rule
#[derive(Debug, Copy, Clone)]
pub enum OptReport {
    Silence,
    Warning,
    Error,
}
/// Check if t1 <: t2
pub fn subtype(gamma: &mut Gamma, env: &TypeEnv, t1: &Type, t2: &Type) -> Result<()> {
    subtype_(
        OptReport::Warning,
        gamma,
        env,
        t1,
        t2,
        &RecursionDepth::new(),
    )
}
/// Check if t1 <: t2, and report the special opt rule as `Slience`, `Warning` or `Error`.
pub fn subtype_with_config(
    report: OptReport,
    gamma: &mut Gamma,
    env: &TypeEnv,
    t1: &Type,
    t2: &Type,
) -> Result<()> {
    subtype_(report, gamma, env, t1, t2, &RecursionDepth::new())
}

/// A single incompatibility found during subtype checking.
#[derive(Debug, Clone)]
pub struct Incompatibility {
    /// Path to the incompatible element, from outermost to innermost.
    /// e.g., `["method \"transfer\"", "return type", "record field \"status\""]`
    pub path: Vec<String>,
    /// Description of the specific incompatibility.
    pub message: String,
}

impl fmt::Display for Incompatibility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.path.is_empty() {
            write!(f, "{}", self.message)
        } else {
            for (i, segment) in self.path.iter().enumerate() {
                if i > 0 {
                    write!(f, " > ")?;
                }
                write!(f, "{segment}")?;
            }
            write!(f, ": {}", self.message)
        }
    }
}

/// Format a list of incompatibilities as a grouped, hierarchical report.
///
/// Errors are grouped by their shared path prefixes so that, for example,
/// five errors under `method "transfer"` appear together rather than as
/// five separate top-level items.
///
/// ```text
/// method "transfer":
///   return type:
///     - record field a: text is not a subtype of nat
///     - record field b: nat is not a subtype of bool
///   input type:
///     - missing required field amount (type nat)
///
/// method "get_user":
///   - missing in new interface
/// ```
pub fn format_report(errors: &[Incompatibility]) -> String {
    if errors.is_empty() {
        return String::new();
    }

    // Build a tree: each node is either a branch (has children keyed by path segment)
    // or a leaf (has a message).
    struct Node {
        children: Vec<(String, Node)>,
        messages: Vec<String>,
    }

    impl Node {
        fn new() -> Self {
            Node {
                children: Vec::new(),
                messages: Vec::new(),
            }
        }
        fn child(&mut self, key: &str) -> &mut Node {
            if let Some(pos) = self.children.iter().position(|(k, _)| k == key) {
                &mut self.children[pos].1
            } else {
                self.children.push((key.to_string(), Node::new()));
                let last = self.children.len() - 1;
                &mut self.children[last].1
            }
        }
        fn insert(&mut self, path: &[String], message: &str) {
            if path.is_empty() {
                self.messages.push(message.to_string());
            } else {
                self.child(&path[0]).insert(&path[1..], message);
            }
        }
        fn render(&self, out: &mut String, indent: usize) {
            let pad = "  ".repeat(indent);
            for msg in &self.messages {
                out.push_str(&pad);
                out.push_str("- ");
                out.push_str(msg);
                out.push('\n');
            }
            for (key, child) in &self.children {
                // If the child has exactly one message and no sub-children, inline it.
                if child.children.is_empty() && child.messages.len() == 1 {
                    out.push_str(&pad);
                    out.push_str(key);
                    out.push_str(": ");
                    out.push_str(&child.messages[0]);
                    out.push('\n');
                } else {
                    out.push_str(&pad);
                    out.push_str(key);
                    out.push_str(":\n");
                    child.render(out, indent + 1);
                }
            }
        }
    }

    let mut root = Node::new();
    for e in errors {
        root.insert(&e.path, &e.message);
    }

    let mut out = String::new();
    root.render(&mut out, 0);
    // Remove trailing newline
    if out.ends_with('\n') {
        out.pop();
    }
    out
}

/// Check if `t1 <: t2`, collecting **all** incompatibilities instead of stopping at the first.
///
/// Returns an empty `Vec` when `t1` is indeed a subtype of `t2`.
/// This is intended for upgrade compatibility reports where users need to see
/// every breaking change at once.
pub fn subtype_check_all(
    gamma: &mut Gamma,
    env: &TypeEnv,
    t1: &Type,
    t2: &Type,
) -> Vec<Incompatibility> {
    let mut errors = Vec::new();
    subtype_collect_(
        OptReport::Warning,
        gamma,
        env,
        t1,
        t2,
        &RecursionDepth::new(),
        &mut Vec::new(),
        &mut errors,
        false,
    );
    errors
}

/// Internal collecting variant of `subtype_`. Instead of short-circuiting on
/// the first error, this continues through all fields/methods/args and pushes
/// every incompatibility it finds into `errors`.
#[allow(clippy::too_many_arguments)]
fn subtype_collect_(
    report: OptReport,
    gamma: &mut Gamma,
    env: &TypeEnv,
    t1: &Type,
    t2: &Type,
    depth: &RecursionDepth,
    path: &mut Vec<String>,
    errors: &mut Vec<Incompatibility>,
    is_input: bool,
) {
    let _guard = match depth.guard() {
        Ok(g) => g,
        Err(_) => {
            errors.push(Incompatibility {
                path: path.clone(),
                message: "recursion limit exceeded".to_string(),
            });
            return;
        }
    };
    use TypeInner::*;
    if t1 == t2 {
        return;
    }
    // Handle Var/Knot (type variables / recursive types)
    if matches!(t1.as_ref(), Var(_) | Knot(_)) || matches!(t2.as_ref(), Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return; // co-inductive: assume OK
        }
        let before = errors.len();
        match (t1.as_ref(), t2.as_ref()) {
            (Var(id), _) => subtype_collect_(
                report,
                gamma,
                env,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                t2,
                depth,
                path,
                errors,
                is_input,
            ),
            (_, Var(id)) => subtype_collect_(
                report,
                gamma,
                env,
                t1,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                depth,
                path,
                errors,
                is_input,
            ),
            (Knot(id), _) => subtype_collect_(
                report,
                gamma,
                env,
                &find_type(id).unwrap(),
                t2,
                depth,
                path,
                errors,
                is_input,
            ),
            (_, Knot(id)) => subtype_collect_(
                report,
                gamma,
                env,
                t1,
                &find_type(id).unwrap(),
                depth,
                path,
                errors,
                is_input,
            ),
            (_, _) => unreachable!(),
        };
        if errors.len() > before {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return;
    }
    match (t1.as_ref(), t2.as_ref()) {
        (_, Reserved) => (),
        (Empty, _) => (),
        (Nat, Int) => (),
        (Vec(ty1), Vec(ty2)) => {
            subtype_collect_(report, gamma, env, ty1, ty2, depth, path, errors, is_input);
        }
        (Null, Opt(_)) => (),
        // For opt rules we delegate to the existing subtype_ to test the condition,
        // since these are probes, not things that generate multiple independent errors.
        (Opt(ty1), Opt(ty2)) if subtype_(report, gamma, env, ty1, ty2, depth).is_ok() => {}
        (_, Opt(ty2))
            if subtype_(report, gamma, env, t1, ty2, depth).is_ok()
                && !matches!(
                    env.trace_type_with_depth(ty2, depth)
                        .map(|t| t.as_ref().clone()),
                    Ok(Null | Reserved | Opt(_))
                ) => {}
        (_, Opt(_)) => {
            let msg = format!("WARNING: {t1} <: {t2} due to special subtyping rules involving optional types/fields (see https://github.com/dfinity/candid/blob/c7659ca/spec/Candid.md#upgrading-and-subtyping). This means the two interfaces have diverged, which could cause data loss.");
            match report {
                OptReport::Silence => (),
                OptReport::Warning => eprintln!("{msg}"),
                OptReport::Error => {
                    errors.push(Incompatibility {
                        path: path.clone(),
                        message: msg,
                    });
                }
            };
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty2 } in fs2 {
                match fields.get(id) {
                    Some(ty1) => {
                        path.push(format!("record field {id}"));
                        subtype_collect_(
                            report, gamma, env, ty1, ty2, depth, path, errors, is_input,
                        );
                        path.pop();
                    }
                    None => {
                        let is_optional = env
                            .trace_type_with_depth(ty2, depth)
                            .map(|t| matches!(t.as_ref(), Null | Reserved | Opt(_)))
                            .unwrap_or(false);
                        if !is_optional {
                            errors.push(Incompatibility {
                                path: path.clone(),
                                message: if is_input {
                                    format!(
                                        "new service requires field {id} (type {ty2}), \
                                         which old callers don't provide and is not optional"
                                    )
                                } else {
                                    format!(
                                        "new type is missing required field {id} (type {ty2}), \
                                         which is expected by the old type and is not optional"
                                    )
                                },
                            });
                        }
                    }
                }
            }
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty1 } in fs1 {
                match fields.get(id) {
                    Some(ty2) => {
                        path.push(format!("variant field {id}"));
                        subtype_collect_(
                            report, gamma, env, ty1, ty2, depth, path, errors, is_input,
                        );
                        path.pop();
                    }
                    None => {
                        errors.push(Incompatibility {
                            path: path.clone(),
                            message: if is_input {
                                format!(
                                    "old callers may send variant case {id}, \
                                     which the new service no longer handles"
                                )
                            } else {
                                format!(
                                    "new variant has field {id} that does not exist in the old type"
                                )
                            },
                        });
                    }
                }
            }
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms1.iter().cloned().collect();
            for (name, ty2) in ms2 {
                match meths.get(name) {
                    Some(ty1) => {
                        path.push(format!("method \"{name}\""));
                        subtype_collect_(report, gamma, env, ty1, ty2, depth, path, errors, false);
                        path.pop();
                    }
                    None => {
                        errors.push(Incompatibility {
                            path: path.clone(),
                            message: format!(
                                "method \"{name}\" is expected by the old interface but missing in the new one"
                            ),
                        });
                    }
                }
            }
        }
        (Func(f1), Func(f2)) => {
            if f1.modes != f2.modes {
                errors.push(Incompatibility {
                    path: path.clone(),
                    message: format!(
                        "function annotation changed from {old} to {new}",
                        old = if f2.modes.is_empty() {
                            "update".to_string()
                        } else {
                            pp_modes(&f2.modes)
                        },
                        new = if f1.modes.is_empty() {
                            "update".to_string()
                        } else {
                            pp_modes(&f1.modes)
                        },
                    ),
                });
                // Don't return early - also check arg/ret compatibility
            }
            // Check each argument directly instead of wrapping in a tuple record,
            // so we get clean error paths like "input argument 1" instead of "record field 0".
            check_func_params(
                report, gamma, env, &f2.args, &f1.args, depth, path, errors, "input", true,
            );
            check_func_params(
                report, gamma, env, &f1.rets, &f2.rets, depth, path, errors, "return", false,
            );
        }
        (Class(_, t), _) => {
            subtype_collect_(report, gamma, env, t, t2, depth, path, errors, is_input);
        }
        (_, Class(_, t)) => {
            subtype_collect_(report, gamma, env, t1, t, depth, path, errors, is_input);
        }
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => {
            errors.push(Incompatibility {
                path: path.clone(),
                message: format!("{t1} is not a subtype of {t2}"),
            });
        }
    }
}

/// Check function parameters (args or rets) for subtype compatibility,
/// collecting all errors. Handles the record-tuple wrapping so that single-arg
/// functions don't produce misleading "record field 0" paths.
///
/// For inputs (contravariant): `sub_params` = old args, `sup_params` = new args.
/// For outputs (covariant): `sub_params` = new rets, `sup_params` = old rets.
#[allow(clippy::too_many_arguments)]
fn check_func_params(
    report: OptReport,
    gamma: &mut Gamma,
    env: &TypeEnv,
    sub_params: &[Type],
    sup_params: &[Type],
    depth: &RecursionDepth,
    path: &mut Vec<String>,
    errors: &mut Vec<Incompatibility>,
    label: &str,    // "input" or "return"
    is_input: bool, // affects wording
) {
    // Use the same tuple wrapping as the original subtype_ for correctness,
    // but when there's a single parameter, check it directly to avoid noise.
    if sub_params.len() == 1 && sup_params.len() == 1 {
        path.push(format!("{label} type"));
        subtype_collect_(
            report,
            gamma,
            env,
            &sub_params[0],
            &sup_params[0],
            depth,
            path,
            errors,
            is_input,
        );
        path.pop();
    } else {
        let sub_tuple = to_tuple(sub_params);
        let sup_tuple = to_tuple(sup_params);
        path.push(if sub_params.len() == sup_params.len() {
            format!("{label} types")
        } else if is_input {
            // sub_params = old args, sup_params = new args (contravariant swap)
            format!(
                "{label} types (old has {} arg{}, new has {})",
                sub_params.len(),
                if sub_params.len() == 1 { "" } else { "s" },
                sup_params.len()
            )
        } else {
            format!(
                "{label} types (old has {} value{}, new has {})",
                sup_params.len(),
                if sup_params.len() == 1 { "" } else { "s" },
                sub_params.len()
            )
        });
        subtype_collect_(
            report, gamma, env, &sub_tuple, &sup_tuple, depth, path, errors, is_input,
        );
        path.pop();
    }
}

fn pp_modes(modes: &[super::internal::FuncMode]) -> String {
    if modes.is_empty() {
        return String::new();
    }
    modes
        .iter()
        .map(|m| match m {
            super::internal::FuncMode::Oneway => "oneway",
            super::internal::FuncMode::Query => "query",
            super::internal::FuncMode::CompositeQuery => "composite_query",
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn subtype_(
    report: OptReport,
    gamma: &mut Gamma,
    env: &TypeEnv,
    t1: &Type,
    t2: &Type,
    depth: &RecursionDepth,
) -> Result<()> {
    let _guard = depth.guard()?;
    use TypeInner::*;
    if t1 == t2 {
        return Ok(());
    }
    if matches!(t1.as_ref(), Var(_) | Knot(_)) || matches!(t2.as_ref(), Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return Ok(());
        }
        let res = match (t1.as_ref(), t2.as_ref()) {
            (Var(id), _) => subtype_(
                report,
                gamma,
                env,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                t2,
                depth,
            ),
            (_, Var(id)) => subtype_(
                report,
                gamma,
                env,
                t1,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                depth,
            ),
            (Knot(id), _) => subtype_(report, gamma, env, &find_type(id).unwrap(), t2, depth),
            (_, Knot(id)) => subtype_(report, gamma, env, t1, &find_type(id).unwrap(), depth),
            (_, _) => unreachable!(),
        };
        if res.is_err() {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1.as_ref(), t2.as_ref()) {
        (_, Reserved) => Ok(()),
        (Empty, _) => Ok(()),
        (Nat, Int) => Ok(()),
        (Vec(ty1), Vec(ty2)) => subtype_(report, gamma, env, ty1, ty2, depth),
        (Null, Opt(_)) => Ok(()),
        (Opt(ty1), Opt(ty2)) if subtype_(report, gamma, env, ty1, ty2, depth).is_ok() => Ok(()),
        (_, Opt(ty2))
            if subtype_(report, gamma, env, t1, ty2, depth).is_ok()
                && !matches!(
                    env.trace_type_with_depth(ty2, depth)?.as_ref(),
                    Null | Reserved | Opt(_)
                ) =>
        {
            Ok(())
        }
        (_, Opt(_)) => {
            let msg = format!("WARNING: {t1} <: {t2} due to special subtyping rules involving optional types/fields (see https://github.com/dfinity/candid/blob/c7659ca/spec/Candid.md#upgrading-and-subtyping). This means the two interfaces have diverged, which could cause data loss.");
            match report {
                OptReport::Silence => (),
                OptReport::Warning => eprintln!("{msg}"),
                OptReport::Error => return Err(Error::msg(msg)),
            };
            Ok(())
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty2 } in fs2 {
                match fields.get(id) {
                    Some(ty1) => {
                        subtype_(report, gamma, env, ty1, ty2, depth).with_context(|| {
                            format!("Record field {id}: {ty1} is not a subtype of {ty2}")
                        })?
                    }
                    None => {
                        if !matches!(
                            env.trace_type_with_depth(ty2, depth)?.as_ref(),
                            Null | Reserved | Opt(_)
                        ) {
                            return Err(Error::msg(format!("Record field {id}: {ty2} is only in the expected type and is not of type opt, null or reserved")));
                        }
                    }
                }
            }
            Ok(())
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty1 } in fs1 {
                match fields.get(id) {
                    Some(ty2) => {
                        subtype_(report, gamma, env, ty1, ty2, depth).with_context(|| {
                            format!("Variant field {id}: {ty1} is not a subtype of {ty2}")
                        })?
                    }
                    None => {
                        return Err(Error::msg(format!(
                            "Variant field {id} not found in the expected type"
                        )));
                    }
                }
            }
            Ok(())
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms1.iter().cloned().collect();
            for (name, ty2) in ms2 {
                match meths.get(name) {
                    Some(ty1) => {
                        subtype_(report, gamma, env, ty1, ty2, depth).with_context(|| {
                            format!("Method {name}: {ty1} is not a subtype of {ty2}")
                        })?
                    }
                    None => {
                        return Err(Error::msg(format!(
                            "Method {name} is only in the expected type"
                        )));
                    }
                }
            }
            Ok(())
        }
        (Func(f1), Func(f2)) => {
            if f1.modes != f2.modes {
                return Err(Error::msg("Function mode mismatch"));
            }
            let args1 = to_tuple(&f1.args);
            let args2 = to_tuple(&f2.args);
            let rets1 = to_tuple(&f1.rets);
            let rets2 = to_tuple(&f2.rets);
            subtype_(report, gamma, env, &args2, &args1, depth)
                .context("Subtype fails at function input type")?;
            subtype_(report, gamma, env, &rets1, &rets2, depth)
                .context("Subtype fails at function return type")?;
            Ok(())
        }
        // This only works in the first order case, but service constructor only appears at the top level according to the spec.
        (Class(_, t), _) => subtype_(report, gamma, env, t, t2, depth),
        (_, Class(_, t)) => subtype_(report, gamma, env, t1, t, depth),
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => Err(Error::msg(format!("{t1} is not a subtype of {t2}"))),
    }
}

/// Check if t1 and t2 are structurally equivalent, ignoring the variable naming differences.
/// Note that this is more strict than `t1 <: t2` and `t2 <: t1`, because of the special opt rule.
pub fn equal(gamma: &mut Gamma, env: &TypeEnv, t1: &Type, t2: &Type) -> Result<()> {
    equal_impl(gamma, env, t1, t2, &RecursionDepth::new())
}

fn equal_impl(
    gamma: &mut Gamma,
    env: &TypeEnv,
    t1: &Type,
    t2: &Type,
    depth: &RecursionDepth,
) -> Result<()> {
    let _guard = depth.guard()?;
    use TypeInner::*;
    if t1 == t2 {
        return Ok(());
    }
    if matches!(t1.as_ref(), Var(_) | Knot(_)) || matches!(t2.as_ref(), Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return Ok(());
        }
        let res = match (t1.as_ref(), t2.as_ref()) {
            (Var(id), _) => equal_impl(
                gamma,
                env,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                t2,
                depth,
            ),
            (_, Var(id)) => equal_impl(
                gamma,
                env,
                t1,
                env.rec_find_type_with_depth(id, depth).unwrap(),
                depth,
            ),
            (Knot(id), _) => equal_impl(gamma, env, &find_type(id).unwrap(), t2, depth),
            (_, Knot(id)) => equal_impl(gamma, env, t1, &find_type(id).unwrap(), depth),
            (_, _) => unreachable!(),
        };
        if res.is_err() {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1.as_ref(), t2.as_ref()) {
        (Opt(ty1), Opt(ty2)) => equal_impl(gamma, env, ty1, ty2, depth),
        (Vec(ty1), Vec(ty2)) => equal_impl(gamma, env, ty1, ty2, depth),
        (Record(fs1), Record(fs2)) | (Variant(fs1), Variant(fs2)) => {
            assert_length(fs1, fs2, |x| x.id.clone(), |x| x.to_string())
                .context("Different field length")?;
            for (f1, f2) in fs1.iter().zip(fs2.iter()) {
                if f1.id != f2.id {
                    return Err(Error::msg(format!(
                        "Field name mismatch: {} and {}",
                        f1.id, f2.id
                    )));
                }
                equal_impl(gamma, env, &f1.ty, &f2.ty, depth).context(format!(
                    "Field {} has different types: {} and {}",
                    f1.id, f1.ty, f2.ty
                ))?;
            }
            Ok(())
        }
        (Service(ms1), Service(ms2)) => {
            assert_length(ms1, ms2, |x| x.0.clone(), |x| format!("method {x}"))
                .context("Different method length")?;
            for (m1, m2) in ms1.iter().zip(ms2.iter()) {
                if m1.0 != m2.0 {
                    return Err(Error::msg(format!(
                        "Method name mismatch: {} and {}",
                        m1.0, m2.0
                    )));
                }
                equal_impl(gamma, env, &m1.1, &m2.1, depth).context(format!(
                    "Method {} has different types: {} and {}",
                    m1.0, m1.1, m2.1
                ))?;
            }
            Ok(())
        }
        (Func(f1), Func(f2)) => {
            if f1.modes != f2.modes {
                return Err(Error::msg("Function mode mismatch"));
            }
            let args1 = to_tuple(&f1.args);
            let args2 = to_tuple(&f2.args);
            let rets1 = to_tuple(&f1.rets);
            let rets2 = to_tuple(&f2.rets);
            equal_impl(gamma, env, &args1, &args2, depth)
                .context("Mismatch in function input type")?;
            equal_impl(gamma, env, &rets1, &rets2, depth)
                .context("Mismatch in function return type")?;
            Ok(())
        }
        (Class(init1, ty1), Class(init2, ty2)) => {
            let init_1 = to_tuple(init1);
            let init_2 = to_tuple(init2);
            equal_impl(gamma, env, &init_1, &init_2, depth).context(format!(
                "Mismatch in init args: {} and {}",
                pp_args(init1),
                pp_args(init2)
            ))?;
            equal_impl(gamma, env, ty1, ty2, depth)
        }
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => Err(Error::msg(format!("{t1} is not equal to {t2}"))),
    }
}

fn assert_length<I, F, K, D>(left: &[I], right: &[I], get_key: F, display: D) -> Result<()>
where
    F: Fn(&I) -> K + Clone,
    K: std::hash::Hash + std::cmp::Eq,
    D: Fn(&K) -> String,
{
    let l = left.len();
    let r = right.len();
    if l == r {
        return Ok(());
    }
    let left: HashSet<_> = left.iter().map(get_key.clone()).collect();
    let right: HashSet<_> = right.iter().map(get_key).collect();
    if l < r {
        let mut diff = right.difference(&left);
        Err(Error::msg(format!(
            "Left side is missing {}",
            display(diff.next().unwrap())
        )))
    } else {
        let mut diff = left.difference(&right);
        Err(Error::msg(format!(
            "Right side is missing {}",
            display(diff.next().unwrap())
        )))
    }
}

fn to_tuple(args: &[Type]) -> Type {
    TypeInner::Record(
        args.iter()
            .enumerate()
            .map(|(i, ty)| Field {
                id: Label::Id(i as u32).into(),
                ty: ty.clone(),
            })
            .collect(),
    )
    .into()
}
#[cfg(not(feature = "printer"))]
fn pp_args(args: &[crate::types::Type]) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    write!(&mut s, "(").unwrap();
    for arg in args.iter() {
        write!(&mut s, "{:?}, ", arg).unwrap();
    }
    write!(&mut s, ")").unwrap();
    s
}
#[cfg(feature = "printer")]
fn pp_args(args: &[crate::types::Type]) -> String {
    use crate::pretty::candid::pp_args;
    pp_args(args).pretty(80).to_string()
}
