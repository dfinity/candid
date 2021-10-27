use super::value::{IDLArgs, IDLField, IDLValue};
use crate::pretty::*;
use crate::types::number::pp_num_str;
use std::fmt;

use ::pretty::RcDoc;

pub use crate::bindings::candid::pp_label;

const MAX_ELEMENTS_FOR_PRETTY_PRINT: usize = 10;

impl fmt::Display for IDLArgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", pp_args(self).pretty(80))
    }
}

impl fmt::Display for IDLValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            pp_value(MAX_ELEMENTS_FOR_PRETTY_PRINT, self).pretty(80)
        )
    }
}

impl fmt::Debug for IDLArgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.len() == 1 {
            write!(f, "({:?})", self.args[0])
        } else {
            let mut tup = f.debug_tuple("");
            for arg in self.args.iter() {
                tup.field(arg);
            }
            tup.finish()
        }
    }
}
fn has_type_annotation(v: &IDLValue) -> bool {
    use IDLValue::*;
    matches!(
        v,
        Int(_)
            | Nat(_)
            | Nat8(_)
            | Nat16(_)
            | Nat32(_)
            | Nat64(_)
            | Int8(_)
            | Int16(_)
            | Int32(_)
            | Int64(_)
            | Float32(_)
            | Float64(_)
            | Null
            | Reserved
    )
}
pub fn number_to_string(v: &IDLValue) -> String {
    use IDLValue::*;
    match v {
        Number(n) => n.to_string(),
        Int(n) => n.to_string(),
        Nat(n) => n.to_string(),
        Nat8(n) => n.to_string(),
        Nat16(n) => n.to_string(),
        Nat32(n) => n.to_string(),
        Nat64(n) => n.to_string(),
        Int8(n) => n.to_string(),
        Int16(n) => n.to_string(),
        Int32(n) => n.to_string(),
        Int64(n) => n.to_string(),
        Float32(f) => f.to_string(),
        Float64(f) => f.to_string(),
        _ => unreachable!(),
    }
}
impl fmt::Debug for IDLValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use IDLValue::*;
        match self {
            Null => write!(f, "null : null"),
            Bool(b) => write!(f, "{}", b),
            Number(n) => write!(f, "{}", n),
            Int(i) => write!(f, "{} : int", i),
            Nat(n) => write!(f, "{} : nat", n),
            Nat8(n) => write!(f, "{} : nat8", n),
            Nat16(n) => write!(f, "{} : nat16", pp_num_str(&n.to_string())),
            Nat32(n) => write!(f, "{} : nat32", pp_num_str(&n.to_string())),
            Nat64(n) => write!(f, "{} : nat64", pp_num_str(&n.to_string())),
            Int8(n) => write!(f, "{} : int8", n),
            Int16(n) => write!(f, "{} : int16", pp_num_str(&n.to_string())),
            Int32(n) => write!(f, "{} : int32", pp_num_str(&n.to_string())),
            Int64(n) => write!(f, "{} : int64", pp_num_str(&n.to_string())),
            Float32(n) => write!(f, "{} : float32", n),
            Float64(n) => write!(f, "{} : float64", n),
            Text(s) => write!(f, "{:?}", s),
            None => write!(f, "null"),
            Reserved => write!(f, "null : reserved"),
            Principal(id) => write!(f, "principal \"{}\"", id),
            Service(id) => write!(f, "service \"{}\"", id),
            Func(id, meth) => write!(
                f,
                "func \"{}\".{}",
                id,
                crate::bindings::candid::ident_string(meth)
            ),
            Opt(v) if has_type_annotation(v) => write!(f, "opt ({:?})", v),
            Opt(v) => write!(f, "opt {:?}", v),
            Vec(vs) => {
                if let Some(Nat8(_)) = vs.first() {
                    write!(f, "blob \"")?;
                    for v in vs.iter() {
                        match v {
                            Nat8(v) => write!(f, "{}", &pp_char(*v))?,
                            _ => unreachable!(),
                        }
                    }
                    write!(f, "\"")
                } else {
                    write!(f, "vec {{")?;
                    for v in vs.iter() {
                        write!(f, " {:?};", v)?
                    }
                    write!(f, "}}")
                }
            }
            Record(fs) => {
                write!(f, "record {{")?;
                for (i, e) in fs.iter().enumerate() {
                    if e.id.get_id() == i as u32 {
                        write!(f, " {:?};", e.val)?;
                    } else {
                        write!(f, " {:?};", e)?;
                    }
                }
                write!(f, "}}")
            }
            Variant(v) => {
                write!(f, "variant {{ ")?;
                if v.0.val == Null {
                    write!(f, "{}", v.0.id)?;
                } else {
                    write!(f, "{:?}", v.0)?;
                }
                write!(f, " }}")
            }
        }
    }
}
impl fmt::Debug for IDLField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {:?}", self.id, self.val)
    }
}

// The definition of tuple is language specific.
fn is_tuple(t: &IDLValue) -> bool {
    match t {
        IDLValue::Record(ref fs) => {
            for (i, field) in fs.iter().enumerate() {
                if field.id.get_id() != (i as u32) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

fn pp_field(depth: usize, field: &IDLField, is_variant: bool) -> RcDoc {
    let val_doc = if is_variant && field.val == IDLValue::Null {
        RcDoc::nil()
    } else {
        kwd(" =").append(pp_value(depth - 1, &field.val))
    };
    pp_label(&field.id).append(val_doc)
}

fn pp_fields(depth: usize, fields: &[IDLField]) -> RcDoc {
    let fs = concat(fields.iter().map(|f| pp_field(depth, f, false)), ";");
    enclose_space("{", fs, "}")
}

pub fn pp_char(v: u8) -> String {
    if (0x20..=0x7e).contains(&v) && v != 0x22 && v != 0x27 && v != 0x60 && v != 0x5c {
        std::char::from_u32(v as u32).unwrap().to_string()
    } else {
        format!("\\{:02x}", v)
    }
}

pub fn pp_value(depth: usize, v: &IDLValue) -> RcDoc {
    use IDLValue::*;
    if depth == 0 {
        return RcDoc::as_string(format!("{:?}", v));
    }
    match v {
        Text(ref s) => RcDoc::as_string(format!("\"{}\"", s.escape_debug())),
        Opt(v) if has_type_annotation(v) => {
            kwd("opt").append(enclose("(", pp_value(depth - 1, v), ")"))
        }
        Opt(v) => kwd("opt").append(pp_value(depth - 1, v)),
        Vec(vs) => {
            if matches!(vs.first(), Some(Nat8(_))) || vs.len() > MAX_ELEMENTS_FOR_PRETTY_PRINT {
                RcDoc::as_string(format!("{:?}", v))
            } else {
                let body = concat(vs.iter().map(|v| pp_value(depth - 1, v)), ";");
                kwd("vec").append(enclose_space("{", body, "}"))
            }
        }
        Record(fields) => {
            if is_tuple(v) {
                let tuple = concat(fields.iter().map(|f| pp_value(depth - 1, &f.val)), ";");
                kwd("record").append(enclose_space("{", tuple, "}"))
            } else {
                kwd("record").append(pp_fields(depth, fields))
            }
        }
        Variant(v) => kwd("variant").append(enclose_space("{", pp_field(depth, &v.0, true), "}")),
        _ => RcDoc::as_string(format!("{:?}", v)),
    }
}

pub fn pp_args(args: &IDLArgs) -> RcDoc {
    let body = concat(
        args.args
            .iter()
            .map(|v| pp_value(MAX_ELEMENTS_FOR_PRETTY_PRINT, v)),
        ",",
    );
    enclose("(", body, ")")
}
