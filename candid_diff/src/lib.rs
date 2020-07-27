extern crate candid;

use std::rc::Rc;

pub type Type = candid::types::Type;
//pub type Label = candid::types::Label;
//pub type Field = candid::types::TypeField;

pub type Value = candid::parser::value::IDLValue;

/// Represents editing an "input type" into an "output type".
///
/// only handle first-order types for now (no functions/services yet)
pub enum TypeEdit<R> {
    /// use "input type"
    Skip,
    /// ignore "input type" and use given type
    Put(Type),
    /// edit param to an Opt type (no effect o/w)
    Opt(R),
    /// edit param to Vec type
    Vec(R),
    /// edit fields of record
    Record(FieldsEdit<R>),
    /// edit fields of variant
    Variant(FieldsEdit<R>),
}

pub struct RcTypeEdit ( Rc<TypeEdit<RcTypeEdit>> );

/// edit a field set: put some fields' types, drop others
pub struct FieldsEdit<R> {
    put: Vec<(Label, TypeEdit<R>)>,
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
    use candid::parser::types::IDLType::*;
    match (t1, t2) {
        (&PrincipalT, &PrincipalT) => {
            TypeEdit::Skip
        },
        (&PrimT(ref p1), &PrimT(ref p2)) => {
            if p1 == p2 {
                TypeEdit::Skip
            }
            else {
                TypeEdit::Put(t2.clone())
            }
        },
        (&VarT(ref x), &VarT(ref y)) => {
            if x == y {
                TypeEdit::Skip
            } else {
                TypeEdit::Put(VarT(y.clone()))
            }
        },
        (&OptT(ref t1), &OptT(ref t2)) => {
            let r = rc_type_diff(&t1, &t2);
            TypeEdit::Opt(r)
        },
        (&VecT(ref t1), &VecT(ref t2)) => {
            let r = rc_type_diff(&t1, &t2);
            TypeEdit::Vec(r)
        },
        (&RecordT(ref fs1), &RecordT(ref fs2)) => {
            TypeEdit::Record(fields_diff(&fs1, &fs2))
        },
        (&VariantT(ref fs1), &VariantT(ref fs2)) => {
            TypeEdit::Variant(fields_diff(&fs1, &fs2))
        },
        (_, _) => {
            // by default, do the least incremental edit:
            TypeEdit::Put(t2.clone())
        }
    }
}

#[test]
fn test_type_diff() {
    assset_equal!(type_diff(&PrincipalT, &PrincipalT), Skip);
    assset_equal!(type_diff(&PrimT, &PrimT), Skip);
}


pub struct ValueEdit {
    // to do -- something similar to TypeEdit, but for values (not types)
}


pub fn value_diff(v1: &Value, v2: &Value, t: Type) -> ValueEdit {
    // to do
    drop((v1, v2, t));
    unimplemented!()
}
