//! `candid_binary` held to the Lean model, case by case.
//!
//! `conformance/differential/cases.json` is written by `lake exe oracle differential`
//! (`conformance/README.md`, "Exact answers"): random messages, often damaged, each read at
//! receiver's types that are the sender's, a variation of them, or unrelated, within a
//! limit on the values decoded -- with the answer `decodeAt` gives. A conformance vector
//! asks only whether a message is rejected. `candid_binary` transcribes `decodeAt`, so it
//! is asked for exactly the same answer: the same values, the same failure or undefined
//! coercion, and for a rejected message the same rejection at the same byte, a count that
//! runs out at the same value included.
//!
//! The model's answer is `Value`'s, which reads every field and a `vec nat8` as a blob. A
//! receiver may read in other ways, which must not change the bytes read, the rejections
//! or the count: so each case is read again, a few times, by a [`Wayward`] receiver, which
//! leaves out fields, reads a `vec nat8` byte by byte, or gives up, and gets the answer
//! that follows from `Value`'s.
//!
//! The committed cases are few. For a longer run, write more with another seed and point
//! `CANDID_DIFFERENTIAL` at them, as the `differential` workflow does:
//!
//! ```text
//! lake exe oracle differential /tmp/cases.json 1 40000   # in lean/
//! CANDID_DIFFERENTIAL=/tmp/cases.json cargo test --test differential
//! ```
//!
//! The decoder runs with every limit but `values` out of the way: the header and the
//! depth are limits Lean does not have. A message can nest as deep as its values, so the
//! cases run on a thread with a stack for that.

use std::path::{Path, PathBuf};

use candid_binary::{Decode, DecodeError, Decoder, Limits, Rejection, ValueReader};
use candid_types::{Composite, Slot};
use candid_value::Record;
use serde_json::Value;

mod common;

use common::*;

/// An answer, as the corpus writes it.
#[derive(Debug, PartialEq)]
enum Answer {
    Values(Vec<candid_value::Value>),
    Failure,
    Undefined,
    Rejected { rejection: String, position: usize },
}

#[test]
fn differential() {
    let path = match std::env::var_os("CANDID_DIFFERENTIAL") {
        Some(path) => PathBuf::from(path),
        None => {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../conformance/differential/cases.json")
        }
    };
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let cases: Vec<Value> = serde_json::from_str(&text).expect("the corpus is JSON");
    let failures = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut failures = Vec::new();
            let mut declined = 0;
            for (i, case) in cases.iter().enumerate() {
                match check(i, case) {
                    Ok(Verdict::Agrees) => {}
                    Ok(Verdict::Declined) => declined += 1,
                    Err(why) => failures.push(format!("case {i}: {why}")),
                }
            }
            (cases.len(), declined, failures)
        })
        .unwrap()
        .join()
        .unwrap();
    let (total, declined, failures) = failures;
    for f in failures.iter().take(30) {
        eprintln!("FAIL  {f}");
    }
    if declined > 0 {
        eprintln!("{declined} of {total} cases declined for a resource limit the model has not");
    }
    assert!(
        failures.is_empty(),
        "{} of {total} differential cases disagree with the model",
        failures.len()
    );
}

/// How a case went, if not against the model.
enum Verdict {
    Agrees,
    /// Rejected for a resource limit of `candid_binary`'s alone, where the model reads on:
    /// allowed (`lean/Spec/Binary.md`, Section 9), and counted.
    Declined,
}

fn check(i: usize, case: &Value) -> Result<Verdict, String> {
    let c = obj(case, &["message", "receiver", "limit", "answer"]);
    let bytes = hex(c["message"].as_str().ok_or("message")?)?;
    let receiver = read_header(&c["receiver"])?;
    let limit = c["limit"].as_u64().ok_or("limit")?;
    let want = read_answer(&c["answer"])?;
    let mut limits = Limits::default();
    limits.values = limit;
    limits.header_bytes = usize::MAX;
    limits.depth = usize::MAX;
    limits.received = u64::MAX;
    limits.subtype_steps = u64::MAX;
    let got = match decode(&bytes, &receiver, limits, &mut Reading::Value) {
        Ok(got) => got,
        // A future type's opcode past an `i64`: a resource limit of this decoder alone,
        // allowed wherever the model has not already rejected the message. A malformed
        // table is not found until the whole table is read, so it may point before the
        // opcode and still come after it.
        Err(e) if *e.rejection() == Rejection::OpcodeOutOfRange => {
            return match want {
                Answer::Rejected {
                    rejection,
                    position,
                } if position <= e.position() && rejection != "malformedTable" => Err(format!(
                    "{}: declined at {} for an opcode, the model rejects it at {position}",
                    to_hex(&bytes),
                    e.position()
                )),
                _ => Ok(Verdict::Declined),
            };
        }
        Err(e) => rejected(&e),
    };
    agree(got == want, || {
        format!(
            "{} at {} within {limit}: got {got:?}, the model says {want:?}",
            to_hex(&bytes),
            c["receiver"]
        )
    })?;
    // Read again, as a receiver that reads in its own way: what it may change of the
    // answer follows from the one above.
    for variation in 0..VARIATIONS {
        let mut wayward = Wayward::new(i as u64 * VARIATIONS + variation);
        let reading = decode(
            &bytes,
            &receiver,
            limits,
            &mut Reading::Wayward(&mut wayward),
        );
        let mine = match reading {
            Ok(mine) => mine,
            Err(e) => rejected(&e),
        };
        agree(wayward.allows(&want, &mine), || {
            format!(
                "{} at {} within {limit}, read {wayward:?}: got {mine:?}, the model says {want:?}",
                to_hex(&bytes),
                c["receiver"]
            )
        })?;
    }
    Ok(Verdict::Agrees)
}

/// How many times each case is read by a [`Wayward`] receiver.
const VARIATIONS: u64 = 4;

/// A [`Wayward`] receiver that gives up does so within this many places.
const GIVE_UP_WITHIN: u64 = 32;

/// How a test reads the receiver's arguments.
enum Reading<'w> {
    /// As `candid_value::Value`, whose answer is the model's.
    Value,
    Wayward(&'w mut Wayward),
}

/// A receiver that reads at the receiver's types in its own way, at random: one that
/// does not ask for every field, or reads a `vec nat8` byte by byte, or one that gives
/// up. None of that may change the bytes read, the rejections, or the count of values:
/// only the values it keeps, and, where it gives up, a failure in place of the answer.
///
/// It skips fields or gives up, not both: a field it skips is still read, and could be
/// where the message is undefined, before it gives up.
#[derive(Debug)]
struct Wayward {
    random: u64,
    /// How many more places to read at before giving up, if it gives up.
    give_up_in: Option<u64>,
    /// How many `opt`s it is under. It does not give up under one: that is `null`, which
    /// the decoder cannot tell from a value under it that fails, as `Value`'s do.
    under_opt: usize,
    gave_up: bool,
}

impl Wayward {
    fn new(seed: u64) -> Wayward {
        let mut w = Wayward {
            // xorshift needs a state other than zero.
            random: seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1,
            give_up_in: None,
            under_opt: 0,
            gave_up: false,
        };
        if w.chance(2) {
            w.give_up_in = Some(w.below(GIVE_UP_WITHIN));
        }
        w
    }

    /// A number below `n`.
    fn below(&mut self, n: u64) -> u64 {
        self.random ^= self.random << 13;
        self.random ^= self.random >> 7;
        self.random ^= self.random << 17;
        self.random % n
    }

    /// True one time in `n`.
    fn chance(&mut self, n: u64) -> bool {
        self.below(n) == 0
    }

    /// Whether to give up on the value here: at the place chosen, counting those outside
    /// every `opt`.
    fn gives_up(&mut self) -> bool {
        if self.under_opt == 0 {
            match &mut self.give_up_in {
                Some(0) => self.gave_up = true,
                Some(n) => *n -= 1,
                None => {}
            }
        }
        self.gave_up
    }

    /// Whether not to ask for a field.
    fn skips(&mut self) -> bool {
        self.give_up_in.is_none() && self.chance(3)
    }

    fn read(&mut self, r: ValueReader<'_, '_>) -> Result<Option<candid_value::Value>, DecodeError> {
        use candid_value::Value;
        if self.gives_up() {
            return Ok(None);
        }
        let expected = r.expected();
        match expected.composite() {
            Some(Composite::Opt(_)) => {
                self.under_opt += 1;
                let v = r.opt(|r| self.read(r));
                self.under_opt -= 1;
                // An `opt` is never a failure: `None` is undefined.
                let Some(v) = v? else {
                    return Ok(None);
                };
                Ok(Some(v.map_or(Value::Null, |v| Value::Opt(Box::new(v)))))
            }
            Some(&Composite::Vec(t)) if t != Slot::NAT8 || self.chance(2) => {
                Ok(r.vec(|r| self.read(r))?.map(Value::Vec))
            }
            Some(Composite::Record(fields)) => r.record(|record| {
                let mut kept = Vec::new();
                for &(id, _) in fields {
                    if self.gives_up() {
                        return Ok(None);
                    }
                    if self.skips() {
                        continue;
                    }
                    match record.field(id, |r| self.read(r))? {
                        Some(v) => kept.push((id, v)),
                        None => return Ok(None),
                    }
                }
                Ok(Some(Value::Record(Record::from_fields(kept).unwrap())))
            }),
            Some(Composite::Variant(_)) => {
                r.variant(|id, r| Ok(self.read(r)?.map(|v| Value::Variant(id, Box::new(v)))))
            }
            _ => Value::try_decode(r),
        }
    }

    /// Whether `mine` is an answer this reading may give, where `Value` gave the model's,
    /// `want`. Giving up is a failure, unless the message is rejected: a value that is
    /// undefined comes after it, since an undefined one ends the argument, and is not read.
    fn allows(&self, want: &Answer, mine: &Answer) -> bool {
        match (want, mine) {
            (Answer::Rejected { .. }, _) => mine == want,
            _ if self.gave_up => *mine == Answer::Failure,
            (Answer::Values(all), Answer::Values(kept)) => {
                all.len() == kept.len() && all.iter().zip(kept).all(|(a, k)| covers(a, k))
            }
            _ => mine == want,
        }
    }
}

/// Whether `kept` is `all` but for fields left out of records.
fn covers(all: &candid_value::Value, kept: &candid_value::Value) -> bool {
    use candid_value::Value;
    match (all, kept) {
        (Value::Record(all), Value::Record(kept)) => kept
            .fields()
            .iter()
            .all(|(id, k)| all.get(*id).is_some_and(|a| covers(a, k))),
        (Value::Opt(a), Value::Opt(k)) => covers(a, k),
        (Value::Vec(a), Value::Vec(k)) => {
            a.len() == k.len() && a.iter().zip(k).all(|(a, k)| covers(a, k))
        }
        (Value::Variant(i, a), Value::Variant(j, k)) => i == j && covers(a, k),
        _ => all == kept,
    }
}

/// Read every argument the receiver expects as a `Value`, then finish: the answer, or
/// the error that is the message's.
fn decode(
    bytes: &[u8],
    receiver: &candid_binary::Header,
    limits: Limits,
    reading: &mut Reading<'_>,
) -> Result<Answer, DecodeError> {
    let mut decoder = Decoder::with_limits(bytes, limits)?;
    let mut values = Vec::new();
    let mut failed = false;
    for &t in receiver.types() {
        let expected = receiver.table().root(t).expect("a header's types resolve");
        let value = match reading {
            Reading::Value => decoder.argument(expected)?,
            Reading::Wayward(w) => decoder.argument_with(expected, |r| w.read(r))?,
        };
        match value {
            Some(v) => values.push(v),
            None => failed = true,
        }
    }
    decoder.finish()?;
    Ok(if failed {
        Answer::Failure
    } else {
        Answer::Values(values)
    })
}

fn rejected(e: &DecodeError) -> Answer {
    if *e.rejection() == Rejection::InfiniteOption {
        return Answer::Undefined;
    }
    Answer::Rejected {
        rejection: name(e.rejection()),
        position: e.position(),
    }
}

/// The name the model gives a rejection, `Rejection.name` in
/// `lean/Oracle/Differential.lean`. One the model cannot give keeps its Rust name, and
/// so never agrees.
fn name(r: &Rejection) -> String {
    use Rejection::*;
    let name = match r {
        EndOfInput => "endOfInput",
        MissingMagicNumber => "missingMagicNumber",
        NotATypeReference => "notATypeReference",
        NotAType => "notAType",
        PrimitiveInTable(_) => "primitiveInTable",
        FieldIdTooLarge => "fieldIdTooLarge",
        FieldsOutOfOrder => "fieldsOutOfOrder",
        MethodsOutOfOrder => "methodsOutOfOrder",
        UnknownAnnotation(_) => "unknownAnnotation",
        TextNotUtf8 => "textNotUtf8",
        MalformedTable(_) => "malformedTable",
        UnresolvedArgument(_) => "unresolvedArgument",
        NotABool(_) => "notABool",
        NotAnOptTag(_) => "notAnOptTag",
        NotAReferenceFlag(_) => "notAReferenceFlag",
        OpaqueReference => "opaqueReference",
        PrincipalTooLong => "principalTooLong",
        VariantIndexOutOfRange => "variantIndexOutOfRange",
        ValueOfEmpty => "valueOfEmpty",
        RecordWithoutValue => "recordWithoutValue",
        BytesAfterValues => "bytesAfterValues",
        TooManyValues => "tooManyValues",
        other => return format!("{other:?}"),
    };
    name.to_string()
}

fn read_answer(a: &Value) -> Result<Answer, String> {
    match a {
        Value::String(s) if s == "failure" => Ok(Answer::Failure),
        Value::String(s) if s == "undefined" => Ok(Answer::Undefined),
        Value::Object(o) if o.contains_key("values") => {
            Ok(Answer::Values(read_values(&obj(a, &["values"])["values"])?))
        }
        Value::Object(_) => {
            let o = obj(a, &["rejection", "position"]);
            Ok(Answer::Rejected {
                rejection: o["rejection"].as_str().ok_or("rejection")?.to_string(),
                position: o["position"].as_u64().ok_or("position")? as usize,
            })
        }
        _ => Err(format!("not an answer: {a}")),
    }
}

#[test]
fn an_opcode_limit_may_come_before_a_malformed_table() {
    // A `vec` of an entry that is not there, then a future type's opcode below -2^63.
    let case = serde_json::json!({
        "message": "4449444c026d02808080808080808080807e0000",
        "receiver": { "roots": [], "table": [] },
        "limit": 10000,
        "answer": { "rejection": "malformedTable", "position": 5 },
    });
    assert!(matches!(check(0, &case), Ok(Verdict::Declined)));
}
