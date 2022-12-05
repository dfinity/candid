use log::error;

use std::rc::Rc;

pub use ::candid::parser::value::IDLField as Field;
pub use ::candid::parser::value::IDLValue as Value;

pub use ::candid::types::{Field as TypeField, Label, Type};
pub use ::candid::Nat;

#[derive(Debug, PartialEq, Clone)]
pub enum VecEdit<R> {
    /// insert into position, shifting the following (backward)
    InsertValue(usize, Value),
    /// edit value at position, leaving others in place
    EditValue(usize, R),
    /// remove at given position, shifting the following (forward)
    RemoveValue(usize),
}

#[derive(Debug, PartialEq, Clone)]
pub struct RcVecEdit(pub Rc<VecEdit<RcValueEdit>>);

/// edit a record's fields: edit some fields' values, drop others
#[derive(Debug, PartialEq, Eq, Clone)]
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
    use candid::parser::pretty::*;
    use candid::pretty::*;

    pub fn value_edit(edit: &RcValueEdit) -> RcDoc {
        use ValueEdit::*;
        match &*edit.0 {
            Skip => str("skip"),
            Put(v) => kwd("put").append(enclose_space("{", pp_value(20, v), "}")),
            Opt(ve) => kwd("opt").append(enclose_space("{", value_edit(ve), "}")),
            Vec(edits) => kwd("vec").append(enclose_space("{", vec_edits(edits), "}")),
            Record(edits) => kwd("record").append(enclose_space("{", record_edits(edits), "}")),
            Variant(ve) => kwd("variant").append(enclose_space("{", value_edit(ve), "}")),
        }
    }

    pub fn vec_edit(edit: &VecEdit<RcValueEdit>) -> RcDoc {
        use VecEdit::*;
        match edit {
            InsertValue(n, v) => kwd("insert").append(enclose_space(
                "{",
                RcDoc::as_string(n)
                    .append(RcDoc::space())
                    .append(pp_value(20, v)),
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

    pub fn vec_edits(edits: &[VecEdit<RcValueEdit>]) -> RcDoc {
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
                pp_label(l).append(RcDoc::space()).append(value_edit(v)),
                "}",
            )),
            DropValue(l) => kwd("drop").append(pp_label(l)),
        }
    }

    pub fn record_edits(edits: &[RecordEdit<RcValueEdit>]) -> RcDoc {
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

pub fn record_diff(
    fs1: &[Field],
    fs2: &[Field],
    _fts: Option<&[TypeField]>,
) -> Vec<RecordEdit<RcValueEdit>> {
    let mut edits = vec![];
    for f1 in fs1.iter() {
        let mut found_f1 = false;
        for f2 in fs2.iter() {
            if f1.id == f2.id {
                found_f1 = true;
                let edit_f12 = value_diff(&f1.val, &f2.val, &Option::None); // to do -- give field type
                if !value_edit_is_skip(&edit_f12) {
                    edits.push(RecordEdit::EditValue(f1.id.clone(), edit_f12));
                }
                break;
            }
        }
        if !found_f1 {
            edits.push(RecordEdit::DropValue(f1.id.clone()))
        }
    }
    for f2 in fs2.iter() {
        let mut found_f2 = false;
        for f1 in fs1.iter() {
            if f1.id == f2.id {
                found_f2 = true;
                break;
            }
        }
        if !found_f2 {
            edits.push(RecordEdit::EditValue(
                f2.id.clone(),
                RcValueEdit(Rc::new(ValueEdit::Put(f2.val.clone()))),
            ))
        }
    }
    edits
}

/// Simple algorithm for computing a naive edit
///
/// Limitations:
///  - No alignment; over-uses in-place edits.
///  - No removal edits used within the output (yet).
///  - All insertions at the end (if any).
///
pub fn vec_diff_simple(v1: &[Value], v2: &[Value], ty: &Option<Type>) -> Vec<VecEdit<RcValueEdit>> {
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
            edits.push(VecEdit::EditValue(i, edit))
        }
    }
    if v1.len() > v2.len() {
        for (i, v1i) in v1.iter().enumerate().skip(prefix_len) {
            edits.push(VecEdit::InsertValue(i, v1i.clone()))
        }
    } else {
        for (i, v2i) in v2.iter().enumerate().skip(prefix_len) {
            edits.push(VecEdit::InsertValue(i, v2i.clone()))
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
            let d = value_diff(
                x,
                y,
                // to do
                &Option::None,
            );
            if value_edit_is_skip(&d) {
                Skip
            } else {
                ValueEdit::Opt(d)
            }
        }
        (Variant(f1), Variant(f2)) => {
            if f1.0.id == f2.0.id {
                let edit = value_diff(&f1.0.val, &f2.0.val, &Option::None);
                if value_edit_is_skip(&edit) {
                    Skip
                } else {
                    ValueEdit::Variant(edit)
                }
            } else {
                Put(v2.clone())
            }
        }
        (Record(fs1), Record(fs2)) => {
            let edits = record_diff(fs1, fs2, Option::None); // to do -- give field types
            if edits.is_empty() {
                Skip
            } else {
                ValueEdit::Record(edits)
            }
        }
        (Vec(x), Vec(y)) => {
            let edits = vec_diff_simple(x, y, &Option::None); // to do -- give type
            if edits.is_empty() {
                Skip
            } else {
                ValueEdit::Vec(edits)
            }
        }
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
    matches!(*edit.0, ValueEdit::Skip)
}
