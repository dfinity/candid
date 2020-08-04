// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

use std::rc::Rc;

pub use ::candid::parser::value::IDLValue as Value;
pub use ::candid::types::{Field, Label, Type};
pub use ::candid::Nat;

#[derive(Debug, PartialEq, Clone)]
pub enum VecEdit<R> {
    /// insert into position, shifting the following (backward)
    InsertValue(Nat, Value),
    /// edit value at position, leaving others in place
    EditValue(Nat, R),
    /// remove at given position, shifting the following (forward)
    RemoveValue(Nat),
}

#[derive(Debug, PartialEq, Clone)]
pub struct RcVecEdit(pub Rc<VecEdit<RcValueEdit>>);

/// edit a record's fields: edit some fields' values, drop others
#[derive(Debug, PartialEq, Clone)]
pub enum RecordEdit<R> {
    EditValue(Label, R),
    DropValue(Label),
}

#[derive(Debug, PartialEq, Clone)]
pub enum ValueEdit<R> {
    /// empty change
    Skip,
    /// full change: overwrite with new value.
    Put(Value),
    /// edit the sub-value (ignore unchanged Opt label).
    Opt(R),
    /// edit the vector, in a sequence of vector edits.
    Vec(Vec<VecEdit<R>>),
    /// edit the record, field-wise; ignore unchanged fields.
    Record(Vec<RecordEdit<R>>),
    /// edit the variant payload (ignore unchanged label).
    Variant(R),
}

#[derive(Debug, PartialEq, Clone)]
pub struct RcValueEdit(pub Rc<ValueEdit<RcValueEdit>>);
pub type ValueEditRc = ValueEdit<RcValueEdit>;

pub mod pretty {
    use super::*;
    use ::pretty::RcDoc;
    use candid::parser::value::pretty::*;
    use candid::pretty::*;

    pub fn value_edit(edit: &RcValueEdit) -> RcDoc {
        use ValueEdit::*;
        match &*edit.0 {
            Skip => str("skip"),
            Put(v) => kwd("put").append(enclose_space("{", pp_value(&v), "}")),
            Opt(ve) => kwd("opt").append(enclose_space("{", value_edit(&ve), "}")),
            Vec(edits) => kwd("vec").append(enclose_space("{", vec_edits(&edits), "}")),
            Record(edits) => kwd("record").append(enclose_space("{", record_edits(&edits), "}")),
            Variant(ve) => kwd("variant").append(enclose_space("{", value_edit(&ve), "}")),
        }
    }

    pub fn vec_edit(edit: &VecEdit<RcValueEdit>) -> RcDoc {
        use VecEdit::*;
        match edit {
            InsertValue(n, v) => kwd("insert").append(enclose_space(
                "{",
                RcDoc::as_string(n)
                    .append(RcDoc::space())
                    .append(pp_value(v)),
                "}",
            )),
            EditValue(n, v) => kwd("edit").append(enclose_space(
                "{",
                RcDoc::as_string(n)
                    .append(RcDoc::space())
                    .append(value_edit(v)),
                "}",
            )),
            RemoveValue(n) => kwd("remove").append(enclose_space("{", RcDoc::as_string(n), "}")),
        }
    }

    pub fn vec_edits(edits: &Vec<VecEdit<RcValueEdit>>) -> RcDoc {
        let mut body = RcDoc::nil();
        let mut is_first = true;
        for edit in edits.iter() {
            if is_first {
                is_first = false;
                body = vec_edit(edit).append(str(";"))
            } else {
                body = body.append(RcDoc::line());
                body = body.append(vec_edit(edit)).append(str(";"));
            };
        }
        body
    }

    pub fn record_edit(edit: &RecordEdit<RcValueEdit>) -> RcDoc {
        use RecordEdit::*;
        match edit {
            EditValue(l, v) => kwd("edit").append(enclose_space(
                "{",
                pp_label(l)
                    .append(RcDoc::space())
                    .append(value_edit(v)),
                "}",
            )),
            DropValue(l) => kwd("drop").append(pp_label(l))
        }
    }

    pub fn record_edits(edits: &Vec<RecordEdit<RcValueEdit>>) -> RcDoc {
        let mut body = RcDoc::nil();
        let mut is_first = true;
        for edit in edits.iter() {
            if is_first {
                is_first = false;
                body = record_edit(edit).append(str(";"))
            } else {
                body = body.append(RcDoc::line());
                body = body.append(record_edit(edit)).append(str(";"));
            };
        }
        body
    }
}

/// Compare the values, with optional (common) type.
pub fn value_diff(v1: &Value, v2: &Value, t: &Option<Type>) -> RcValueEdit {
    RcValueEdit(Rc::new(value_diff_rec(v1, v2, t)))
}

/// Simple algorithm for computing a naive edit
///
/// Limitations:
///  - No alignment; over-uses in-place edits.
///  - No removal edits used within the output (yet).
///  - All insertions at the end (if any).
///
pub fn vec_diff_simple(
    v1: &Vec<Value>,
    v2: &Vec<Value>,
    ty: &Option<Type>,
) -> Vec<VecEdit<RcValueEdit>> {
    let mut edits = vec![];
    let prefix_len = v1.len().min(v2.len());
    let ty = match ty {
        None => None,
        Some(Type::Vec(t)) => Some((**t).clone()),
        _ => {
            error!("invalid type");
            None
        }
    };
    for i in 0..prefix_len {
        let edit = value_diff(&v1[i], &v2[i], &ty);
        if !value_edit_is_skip(&edit) {
            edits.push(VecEdit::EditValue(Nat::from(i), edit))
        }
    }
    if v1.len() > v2.len() {
        for i in prefix_len..v1.len() {
            edits.push(VecEdit::InsertValue(Nat::from(i), v1[i].clone()))
        }
    } else if v2.len() > v1.len() {
        for i in prefix_len..v2.len() {
            edits.push(VecEdit::InsertValue(Nat::from(i), v2[i].clone()))
        }
    }
    edits
}

/// Compare the values, with optional (common) type.
pub fn value_diff_rec(v1: &Value, v2: &Value, _t: &Option<Type>) -> ValueEdit<RcValueEdit> {
    use Value::*;
    use ValueEdit::{Put, Skip};

    match (v1, v2) {
        (Opt(x), Opt(y)) => {
            ValueEdit::Opt(value_diff(
                &**x,
                &**y,
                // to do
                &Option::None,
            ))
        }
        (Vec(x), Vec(y)) => {
            let edits = vec_diff_simple(x, y, &Option::None);
            if edits.len() > 0 {
                ValueEdit::Vec(edits)
            } else {
                Skip
            }
        }
        (Opt(_x), _) => Put(v2.clone()),
        (Bool(b1), Bool(b2)) => {
            if b1 == b2 {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Null, Null) => Skip,
        (Text(x), Text(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Number(x), Number(y)) => {
            // to do -- double-check this case
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Int(x), Int(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Nat(x), Nat(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Nat8(x), Nat8(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Nat16(x), Nat16(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Nat32(x), Nat32(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Nat64(x), Nat64(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Int8(x), Int8(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Int16(x), Int16(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Int32(x), Int32(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Int64(x), Int64(y)) => {
            if x == y {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        _ => Put(v2.clone()),
    }
}

pub fn value_edit_is_skip(edit: &RcValueEdit) -> bool {
    match *edit.0 {
        ValueEdit::Skip => true,
        _ => false,
    }
}
