//! `candid_binary` held to the Lean model, case by case.
//!
//! `differential.json` is written by `lake exe oracle differential`
//! (`lean/Oracle/Differential.lean`): random messages, often damaged, each read at
//! receiver's types that are the sender's, a variation of them, or unrelated, within a
//! limit on the values decoded -- with the answer `decodeAt` gives. A conformance vector
//! asks only whether a message is rejected. `candid_binary` transcribes `decodeAt`, so it
//! is asked for exactly the same answer: the same values, the same failure or undefined
//! coercion, and for a rejected message the same rejection at the same byte, a count that
//! runs out at the same value included.
//!
//! The committed corpus is small. For a longer run, write more cases with another seed
//! and point `CANDID_DIFFERENTIAL` at them:
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

use candid_binary::{DecodeError, Decoder, Limits, Rejection};
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
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/differential.json"),
    };
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let cases: Vec<Value> = serde_json::from_str(&text).expect("the corpus is JSON");
    let failures = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut failures = Vec::new();
            for (i, case) in cases.iter().enumerate() {
                if let Err(why) = check(case) {
                    failures.push(format!("case {i}: {why}"));
                }
            }
            (cases.len(), failures)
        })
        .unwrap()
        .join()
        .unwrap();
    let (total, failures) = failures;
    for f in failures.iter().take(30) {
        eprintln!("FAIL  {f}");
    }
    assert!(
        failures.is_empty(),
        "{} of {total} differential cases disagree with the model",
        failures.len()
    );
}

fn check(case: &Value) -> Result<(), String> {
    let c = obj(case, &["message", "receiver", "limit", "answer"]);
    let bytes = hex(c["message"].as_str().ok_or("message")?)?;
    let receiver = read_header(&c["receiver"])?;
    let limit = c["limit"].as_u64().ok_or("limit")?;
    let want = read_answer(&c["answer"])?;
    let mut limits = Limits::default();
    limits.values = limit;
    limits.header_bytes = usize::MAX;
    limits.depth = usize::MAX;
    let got = match decode(&bytes, &receiver, limits) {
        Ok(got) => got,
        // A future type's opcode past an `i64`: a resource limit of this decoder alone,
        // which the spec allows wherever the model accepts.
        Err(e) if *e.rejection() == Rejection::OpcodeOutOfRange => return Ok(()),
        Err(e) => rejected(&e),
    };
    agree(got == want, || {
        format!(
            "{} at {} within {limit}: got {got:?}, the model says {want:?}",
            to_hex(&bytes),
            c["receiver"]
        )
    })
}

/// Read every argument the receiver expects as a `Value`, then finish: the answer, or
/// the error that is the message's.
fn decode(
    bytes: &[u8],
    receiver: &candid_binary::Header,
    limits: Limits,
) -> Result<Answer, DecodeError> {
    let mut decoder = Decoder::with_limits(bytes, limits)?;
    let mut values = Vec::new();
    let mut failed = false;
    for &t in receiver.types() {
        let expected = receiver.table().root(t).expect("a header's types resolve");
        match decoder.argument(expected)? {
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
