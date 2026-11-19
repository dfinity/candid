//! Subtyping, decided over two tables. Transcribes `lean/Candid/Subtype.lean`; the
//! reasoning behind each choice is there, and only the Rust-specific choices are here.
//!
//! The rules are those of `lean/Spec/Types.md`, Section 5.1, with the spec's four `opt`
//! rules collapsed into one: any type is a subtype of an option.
//!
//! **A worklist, with assumptions shared by the whole run.** A pair of slots that is not
//! two references is decided outright ([`leaf`]). A pair of references is either assumed
//! already, and dropped, or recorded and replaced by the obligations one step in
//! ([`expand`]). No rule searches, so nothing backtracks, and an assumption recorded on
//! the way to a `false` is discarded with the run. The assumptions are kept per
//! direction, since the function rule's parameter premise swaps the tables: an assumed
//! `A.i <: B.j` says nothing about `B.j <: A.i`.
//!
//! Two departures from the model, neither of which changes an answer:
//!
//! - Assumptions are sets, not lists, and fields and methods are looked up by binary
//!   search, not by a scan. A table may come from untrusted bytes, and a scan per field
//!   is quadratic in a record's width.
//! - A function's parameters and results are matched by position, where the model
//!   labels them `1`, `2`, ... and reuses the record rule. The two are the same rule.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use crate::composite::{Annotation, Composite};
use crate::slot::{Primitive, Slot};
use crate::table::{Root, TypeTable};

/// Whether `subtype <: supertype` (`lean/Spec/Types.md`, Section 5.1).
///
/// The two may be in different tables, as when a type that arrived in a message is
/// compared with the receiver's own. Each is checked against its own table.
///
/// Lean's `decSubtype`. Every step either records a pair of references, of which there
/// are at most the product of the two tables' sizes, or discharges an obligation, so
/// this terminates without a depth limit.
pub fn is_subtype(subtype: Root<'_>, supertype: Root<'_>) -> bool {
    let (a, b) = (subtype.table(), supertype.table());
    let mut assumed = BTreeSet::new();
    let mut assumed_reverse = BTreeSet::new();
    let mut goals = vec![Goal {
        forward: true,
        subtype: subtype.slot(),
        supertype: supertype.slot(),
    }];
    while let Some(goal) = goals.pop() {
        // `forward` says which way round the tables are: the subtype in `a` and the
        // supertype in `b`, or, for a function's parameters, the reverse.
        let (t, u, assumed) = if goal.forward {
            (a, b, &mut assumed)
        } else {
            (b, a, &mut assumed_reverse)
        };
        match (goal.subtype, goal.supertype) {
            // Two references: the only pair that unfolds, and the only place an
            // assumption is recorded.
            (Slot::Ref(i), Slot::Ref(j)) => {
                // Both resolve: the roots do, and in a checked table so does every
                // slot an entry holds.
                let (Some(x), Some(y)) = (t.lookup(i), u.lookup(j)) else {
                    return false;
                };
                if !assumed.insert((i, j)) {
                    continue;
                }
                match expand(t, u, goal.forward, x, y) {
                    // Reversed, so that they are taken in order: the model puts them at
                    // the front of its list, and this pops from the back.
                    Some(next) => goals.extend(next.into_iter().rev()),
                    None => return false,
                }
            }
            (s, v) => {
                if !leaf(t, u, s, v) {
                    return false;
                }
            }
        }
    }
    true
}

/// An obligation `subtype <: supertype`. `forward` says which table each is in; see
/// [`is_subtype`].
#[derive(Clone, Copy, Debug)]
struct Goal {
    forward: bool,
    subtype: Slot,
    supertype: Slot,
}

/// `null <: s`, decided in one step: `null` is a subtype of exactly `null`,
/// `reserved` and the options.
fn accepts_null(table: &TypeTable, s: Slot) -> bool {
    match s {
        Slot::Primitive(p) => matches!(p, Primitive::Null | Primitive::Reserved),
        Slot::Ref(r) => matches!(table.lookup(r), Some(Composite::Opt(_))),
    }
}

/// A pair of slots that needs no unfolding, decided in tables `t` (the subtype's) and
/// `u` (the supertype's): any pair but two references, which [`is_subtype`] unfolds.
fn leaf(t: &TypeTable, u: &TypeTable, s: Slot, v: Slot) -> bool {
    use Primitive::{Empty, Int, Nat, Principal, Reserved};
    match (s, v) {
        // The top and bottom types.
        (_, Slot::Primitive(Reserved)) | (Slot::Primitive(Empty), _) => true,
        // Each primitive is a subtype of itself, and `nat <: int`.
        (Slot::Primitive(p), Slot::Primitive(q)) => p == q || (p == Nat && q == Int),
        // A primitive against a composite: only the `opt` rule can apply.
        (Slot::Primitive(_), Slot::Ref(j)) => matches!(u.lookup(j), Some(Composite::Opt(_))),
        // A composite against a primitive: only `service {...} <: principal`.
        (Slot::Ref(i), Slot::Primitive(q)) => {
            q == Principal && matches!(t.lookup(i), Some(Composite::Service(_)))
        }
        // Not reached: `is_subtype` unfolds these.
        (Slot::Ref(_), Slot::Ref(_)) => false,
    }
}

/// The obligations one step in, for the composites a pair of references names: `x` in
/// `t`, the subtype's table, and `y` in `u`, the supertype's. `None` if the pair fails
/// outright.
fn expand(
    t: &TypeTable,
    u: &TypeTable,
    forward: bool,
    x: &Composite,
    y: &Composite,
) -> Option<Vec<Goal>> {
    let goal = |subtype, supertype| Goal {
        forward,
        subtype,
        supertype,
    };
    match (x, y) {
        // Any type is a subtype of an option.
        (_, Composite::Opt(_)) => Some(Vec::new()),

        (Composite::Vec(x), Composite::Vec(y)) => Some(vec![goal(*x, *y)]),

        // A record may specialise a field or add one, and may omit one the supertype
        // has if that field accepts `null`.
        (Composite::Record(fs), Composite::Record(gs)) => {
            let fs = Sorted::new(fs.iter().copied());
            let mut goals = Vec::new();
            for &(id, g) in gs {
                match fs.get(&id) {
                    Some(f) => goals.push(goal(f, g)),
                    None if accepts_null(u, g) => {}
                    None => return None,
                }
            }
            Some(goals)
        }

        // A variant may specialise a case or drop one; every case it has, the supertype
        // has too.
        (Composite::Variant(fs), Composite::Variant(gs)) => {
            let gs = Sorted::new(gs.iter().copied());
            fs.iter()
                .map(|&(id, f)| gs.get(&id).map(|g| goal(f, g)))
                .collect()
        }

        // Parameters generalise and results specialise, each like a tuple: parameters
        // may be dropped and results added. The parameter premise swaps the tables, so
        // its obligations face the other way, and a parameter the subtype adds must
        // accept `null` in `t`, which is now the supertype's table.
        (
            Composite::Func {
                parameters: ps,
                results: rs,
                annotations: ns,
            },
            Composite::Func {
                parameters: qs,
                results: ss,
                annotations: ms,
            },
        ) => {
            if !annotations_agree(ns, ms) {
                return None;
            }
            let mut goals = positional(t, !forward, qs, ps)?;
            goals.extend(positional(u, forward, rs, ss)?);
            Some(goals)
        }

        // A service may specialise a method or add one.
        (Composite::Service(ms), Composite::Service(ns)) => {
            let ms = Sorted::new(ms.iter().map(|(name, s)| (name.as_str(), *s)));
            ns.iter()
                .map(|(name, g)| ms.get(&name.as_str()).map(|f| goal(f, *g)))
                .collect()
        }

        // A future type is a subtype of itself, and otherwise only of `reserved` and of
        // the options, which are decided elsewhere.
        (
            Composite::Future { opcode, data },
            Composite::Future {
                opcode: opcode_other,
                data: data_other,
            },
        ) => (opcode == opcode_other && data == data_other).then(Vec::new),

        _ => None,
    }
}

/// The record rule over positions: each of `supertypes` is either matched by the
/// subtype at the same position -- an obligation -- or absent there, which it may be only
/// if it accepts `null` in `table`, the supertype's.
fn positional(
    table: &TypeTable,
    forward: bool,
    subtypes: &[Slot],
    supertypes: &[Slot],
) -> Option<Vec<Goal>> {
    let mut goals = Vec::new();
    for (k, &supertype) in supertypes.iter().enumerate() {
        match subtypes.get(k) {
            Some(&subtype) => goals.push(Goal {
                forward,
                subtype,
                supertype,
            }),
            None if accepts_null(table, supertype) => {}
            None => return None,
        }
    }
    Some(goals)
}

/// Annotations agree as sets: the spec compares them without regard to order
/// (`lean/Spec/Types.md`, Section 3.4), and a checked table repeats none.
fn annotations_agree(xs: &[Annotation], ys: &[Annotation]) -> bool {
    xs.iter().all(|x| ys.contains(x)) && ys.iter().all(|y| xs.contains(y))
}

/// Fields or methods, sorted by key, for lookup by binary search. A checked table has no
/// two with the same key, so a lookup finds at most one.
struct Sorted<K>(Vec<(K, Slot)>);

impl<K: Ord> Sorted<K> {
    fn new(entries: impl Iterator<Item = (K, Slot)>) -> Self {
        let mut entries: Vec<_> = entries.collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        Sorted(entries)
    }

    fn get(&self, key: &K) -> Option<Slot> {
        let i = self.0.binary_search_by(|(k, _)| k.cmp(key)).ok()?;
        Some(self.0[i].1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::FieldId;
    use crate::slot::TypeRef;
    use crate::table::RawTypeTable;

    fn decide(a: &TypeTable, s: Slot, b: &TypeTable, v: Slot) -> bool {
        is_subtype(a.root(s).unwrap(), b.root(v).unwrap())
    }

    fn checked(raw: RawTypeTable) -> TypeTable {
        raw.check().unwrap()
    }

    fn func(parameters: Vec<Slot>, results: Vec<Slot>) -> Composite {
        Composite::Func {
            parameters,
            results,
            annotations: Vec::new(),
        }
    }

    #[test]
    fn primitives() {
        let empty = checked(RawTypeTable::new());
        let p = |s, v| decide(&empty, s, &empty, v);
        assert!(p(Slot::NAT, Slot::INT));
        assert!(!p(Slot::INT, Slot::NAT));
        assert!(p(Slot::EMPTY, Slot::TEXT));
        assert!(p(Slot::TEXT, Slot::RESERVED));
        assert!(!p(Slot::RESERVED, Slot::TEXT));
    }

    #[test]
    fn anything_is_a_subtype_of_an_option() {
        let mut raw = RawTypeTable::new();
        let opt_nat = raw.intern(Composite::Opt(Slot::NAT));
        let table = checked(raw);
        assert!(decide(&table, Slot::TEXT, &table, opt_nat));
        assert!(!decide(&table, opt_nat, &table, Slot::NAT));
    }

    #[test]
    fn records_across_tables() {
        // record { head : nat; tail : list } against record { head : int }, each
        // recursive through its own table.
        let mut a = RawTypeTable::new();
        let list = a.intern(Composite::Opt(Slot::Ref(TypeRef::new(1))));
        a.intern(Composite::record_of([("head", Slot::NAT), ("tail", list)]));
        let a = checked(a);

        let mut b = RawTypeTable::new();
        let shorter = b.intern(Composite::Opt(Slot::Ref(TypeRef::new(1))));
        b.intern(Composite::record_of([
            ("head", Slot::INT),
            ("tail", shorter),
        ]));
        let b = checked(b);
        assert!(decide(&a, list, &b, shorter));
        assert!(!decide(&b, shorter, &a, Slot::Ref(TypeRef::new(1))));

        // A field the supertype has and the subtype lacks must accept `null`.
        let mut c = RawTypeTable::new();
        let needs_text = c.intern(Composite::record_of([("extra", Slot::TEXT)]));
        let optional = c.intern(Composite::record_of([("extra", Slot::NULL)]));
        let none = c.intern(Composite::Record(Vec::new()));
        let c = checked(c);
        assert!(!decide(&c, none, &c, needs_text));
        assert!(decide(&c, none, &c, optional));
    }

    #[test]
    fn assumptions_keep_their_direction() {
        // `func (A) -> (nat) <: func (B) -> (int)`, each taking itself. The parameter
        // premise asks `B <: A`, which the assumed `A <: B` must not answer: the
        // converse fails at the results, `int <: nat`.
        let a = checked(RawTypeTable::from(vec![func(
            vec![Slot::Ref(TypeRef::new(0))],
            vec![Slot::NAT],
        )]));
        let b = checked(RawTypeTable::from(vec![func(
            vec![Slot::Ref(TypeRef::new(0))],
            vec![Slot::INT],
        )]));
        let root = Slot::Ref(TypeRef::new(0));
        assert!(!decide(&a, root, &b, root));
    }

    #[test]
    fn shared_structure_is_compared_once() {
        // Entry k is `record { 0 : k+1; 1 : k+1 }`. Scoping assumptions to a path would
        // compare 2^41 - 1 pairs.
        let n = 41;
        let entries = (0..n)
            .map(|k| {
                let next = if k + 1 == n {
                    Slot::NAT
                } else {
                    Slot::Ref(TypeRef::new(k + 1))
                };
                Composite::Record(vec![(FieldId::new(0), next), (FieldId::new(1), next)])
            })
            .collect();
        let table = checked(RawTypeTable::from_entries(entries));
        let root = Slot::Ref(TypeRef::new(0));
        assert!(decide(&table, root, &table, root));
    }

    #[test]
    fn annotations_must_agree() {
        let query = Composite::Func {
            parameters: Vec::new(),
            results: Vec::new(),
            annotations: vec![Annotation::Query],
        };
        let table = checked(RawTypeTable::from(vec![
            query,
            func(Vec::new(), Vec::new()),
        ]));
        let (q, update) = (Slot::Ref(TypeRef::new(0)), Slot::Ref(TypeRef::new(1)));
        assert!(!decide(&table, q, &table, update));
        assert!(decide(&table, q, &table, q));
    }
}
