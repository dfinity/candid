use std::rc::Rc;

pub use ::candid::types::{Type, Label, Field};
pub use ::candid::parser::value::IDLValue as Value;

/// Represents editing an "input type" into an "output type".
///
/// only handle first-order types for now (no functions/services yet)
pub enum TypeEdit<R> {
    /// use "input type"
    Skip,
    /// Encountered an Unknown type.
    Unknown,
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
