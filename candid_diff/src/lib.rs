// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

use std::rc::Rc;

pub use ::candid::Nat;
pub use ::candid::types::{Type, Label, Field};
pub use ::candid::parser::value::IDLValue as Value;

/// Represents editing an "input type" into an "output type".
///
/// only handle first-order types for now (no functions/services yet)
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeEdit<R> {
    /// empty change.
    Skip,
    /// full change: ignore "input type" and use given type.
    Put(Type),
    /// encountered an Unknown type.
    Unknown,
    /// edit param to an Opt type (no effect o/w)
    Opt(R),
    /// edit param to Vec type
    Vec(R),
    /// edit fields of record
    Record(FieldsEdit<R>),
    /// edit fields of variant
    Variant(FieldsEdit<R>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RcTypeEdit ( pub Rc<TypeEdit<RcTypeEdit>> );

/// edit a field set: put some fields' types, drop others
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FieldsEdit<R> {
    edit: Vec<(Label, TypeEdit<R>)>,
    drop: Vec<Label>,
}

pub type FieldsEditRc = FieldsEdit<RcTypeEdit>;

pub fn fields_diff(fs1: &Vec<Field>, fs2: &Vec<Field>) -> FieldsEditRc {
    // to do -- point-wise diff on common field names; drop field names that go away in the second set
    drop((fs1, fs2));
    unimplemented!()
}

pub fn rc_type_diff(t1: &Box<Type>, t2: &Box<Type>) -> RcTypeEdit {
    RcTypeEdit(Rc::new(type_diff(&*t1, &*t2)))
}

pub fn type_diff(t1: &Type, t2: &Type) -> TypeEdit<RcTypeEdit> {
    use candid::types::Type::*;
    match (t1, t2) {
        (Null, Null) => TypeEdit::Skip,
        (Bool, Bool) => TypeEdit::Skip,
        (Nat, Nat) => TypeEdit::Skip,
        (Principal, Principal) => TypeEdit::Skip,
        (Unknown, _) => TypeEdit::Unknown,
        (_, Unknown) => TypeEdit::Unknown,
/* to do -- reflexive cases: TypeEdit::Skip,
        Int,
        Nat8,
        Nat16,
        Nat32,
        Nat64,
        Int8,
        Int16,
        Int32,
        Int64,
        Float32,
        Float64,
        Text,
        Reserved,
        Empty,
*/
        (&Var(ref x), &Var(ref y)) => {
            if x == y {
                TypeEdit::Skip
            } else {
                TypeEdit::Put(Var(y.clone()))
            }
        },
        (&Opt(ref t1), &Opt(ref t2)) => {
            let r = rc_type_diff(&t1, &t2);
            TypeEdit::Opt(r)
        },
        (&Vec(ref t1), &Vec(ref t2)) => {
            let r = rc_type_diff(&t1, &t2);
            TypeEdit::Vec(r)
        },
        (&Record(ref fs1), &Record(ref fs2)) => {
            TypeEdit::Record(fields_diff(&fs1, &fs2))
        },
        (&Variant(ref fs1), &Variant(ref fs2)) => {
            TypeEdit::Variant(fields_diff(&fs1, &fs2))
        },
        (Func(_), _) => unimplemented!(),
        (_, Func(_)) => unimplemented!(),
        (Service(_), _) => unimplemented!(),
        (_, Service(_)) => unimplemented!(),
        (_, _) => {
            // by default, do the least incremental edit:
            TypeEdit::Put(t2.clone())
        }
    }
}

#[test]
fn test_type_diff() {
    use TypeEdit::*;
    use Type::*;
    assert_eq!(type_diff(&Principal, &Principal), Skip);
    assert_eq!(type_diff(&Bool, &Bool), Skip);
}

#[derive(Debug, PartialEq, Clone)]
pub enum VecEdit<R> {
    /// insert into position, shifting the following (backward)
    InsertValue(Nat, Value),
    /// edit value at position, leaving others in place
    EditValue(Nat, R),
    /// remove at given position, shifting the following (forward)
    RemoveValue(Nat),
}

/// edit a record's fields: edit some fields' values, drop others
#[derive(Debug, PartialEq, Clone)]
pub struct RecordEdits<R> {
    edit: Vec<(Label, R)>,
    drop: Vec<Label>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct RcValueEdit ( pub Rc<ValueEdit<RcValueEdit>> );

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
    Record(RecordEdits<R>),
    /// edit the variant payload (ignore unchanged label).
    Variant(R),
}

/// Compare the values, with optional (common) type.
pub fn value_diff(v1: &Value, v2: &Value, t: Option<Type>) -> RcValueEdit {
    RcValueEdit(Rc::new(value_diff_rec(v1, v2, t)))
}

/// Compare the values, with optional (common) type.
pub fn value_diff_rec(v1: &Value, v2: &Value, _t: Option<Type>) -> ValueEdit<RcValueEdit> {
    use Value::*;
    use ValueEdit::{Put, Skip};

    match (v1, v2) {
        (Opt(x), Opt(y)) => {
            ValueEdit::Opt(value_diff(&**x, &**y, Option::None))
        }
        (Opt(_x), _) => {
            Put(v2.clone())
        }
        (Bool(b1), Bool(b2)) => {
            if b1 == b2 {
                Skip
            } else {
                Put(v2.clone())
            }
        }
        (Null, Null) => Skip,
        (Text(x), Text(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Number(x), Number(y)) => {
            // to do -- double-check this case
            if x == y { Skip } else { trace!("x"); Put(v2.clone()) }
        }
        (Int(x), Int(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Nat(x), Nat(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Nat8(x), Nat8(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Nat16(x), Nat16(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Nat32(x), Nat32(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Nat64(x), Nat64(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Int8(x), Int8(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Int16(x), Int16(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Int32(x), Int32(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        (Int64(x), Int64(y)) =>
            if x == y { Skip } else { Put(v2.clone()) }
        _ => {
            Put(v2.clone())
        }
    }
}

pub fn value_edit_is_skip(edit:&RcValueEdit) -> bool {
    match *edit.0 {
        ValueEdit::Skip => true,
        _ => false,
    }
}
