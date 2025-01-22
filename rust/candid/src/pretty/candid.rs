use crate::pretty::utils::*;
use crate::types::{Field, FuncMode, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

static KEYWORDS: [&str; 30] = [
    "import",
    "service",
    "func",
    "type",
    "opt",
    "vec",
    "record",
    "variant",
    "blob",
    "principal",
    "nat",
    "nat8",
    "nat16",
    "nat32",
    "nat64",
    "int",
    "int8",
    "int16",
    "int32",
    "int64",
    "float32",
    "float64",
    "bool",
    "text",
    "null",
    "reserved",
    "empty",
    "oneway",
    "query",
    "composite_query",
];

fn is_keyword(id: &str) -> bool {
    KEYWORDS.contains(&id)
}

pub fn is_valid_as_id(id: &str) -> bool {
    if id.is_empty() || !id.is_ascii() {
        return false;
    }
    for (i, c) in id.char_indices() {
        if i == 0 {
            if !c.is_ascii_alphabetic() && c != '_' {
                return false;
            }
        } else if !c.is_ascii_alphanumeric() && c != '_' {
            return false;
        }
    }
    true
}

fn needs_quote(id: &str) -> bool {
    !is_valid_as_id(id) || is_keyword(id)
}

pub(crate) fn ident_string(id: &str) -> String {
    if needs_quote(id) {
        format!("\"{}\"", id.escape_debug())
    } else {
        id.to_string()
    }
}

pub(crate) fn pp_text(id: &str) -> RcDoc {
    RcDoc::text(ident_string(id))
}

pub fn pp_ty(ty: &Type) -> RcDoc {
    pp_ty_inner(ty.as_ref())
}

pub fn pp_ty_inner(ty: &TypeInner) -> RcDoc {
    use TypeInner::*;
    match ty {
        Null => str("null"),
        Bool => str("bool"),
        Nat => str("nat"),
        Int => str("int"),
        Nat8 => str("nat8"),
        Nat16 => str("nat16"),
        Nat32 => str("nat32"),
        Nat64 => str("nat64"),
        Int8 => str("int8"),
        Int16 => str("int16"),
        Int32 => str("int32"),
        Int64 => str("int64"),
        Float32 => str("float32"),
        Float64 => str("float64"),
        Text => str("text"),
        Reserved => str("reserved"),
        Empty => str("empty"),
        Var(ref s) => str(s),
        Principal => str("principal"),
        Opt(ref t) => kwd("opt").append(pp_ty(t)),
        Vec(ref t) if matches!(t.as_ref(), Nat8) => str("blob"),
        Vec(ref t) => kwd("vec").append(pp_ty(t)),
        Record(ref fs) => {
            let t = Type(ty.clone().into());
            if t.is_tuple() {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ";");
                kwd("record").append(enclose_space("{", tuple, "}"))
            } else {
                kwd("record").append(pp_fields(fs, false))
            }
        }
        Variant(ref fs) => kwd("variant").append(pp_fields(fs, true)),
        Func(ref func) => kwd("func").append(pp_function(func)),
        Service(ref serv) => kwd("service").append(pp_service(serv)),
        Class(ref args, ref t) => {
            let doc = pp_args(args).append(" ->").append(RcDoc::space());
            match t.as_ref() {
                Service(ref serv) => doc.append(pp_service(serv)),
                Var(ref s) => doc.append(s),
                _ => unreachable!(),
            }
        }
        Knot(ref id) => RcDoc::text(format!("{id}")),
        Unknown => str("unknown"),
        Future => str("future"),
    }
}

pub fn pp_label(id: &SharedLabel) -> RcDoc {
    match &**id {
        Label::Named(id) => pp_text(id),
        Label::Id(_) | Label::Unnamed(_) => RcDoc::as_string(id),
    }
}

pub(crate) fn pp_field(field: &Field, is_variant: bool) -> RcDoc {
    let ty_doc = if is_variant && *field.ty == TypeInner::Null {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty(&field.ty))
    };
    pp_label(&field.id).append(ty_doc)
}

fn pp_fields(fs: &[Field], is_variant: bool) -> RcDoc {
    let fields = concat(fs.iter().map(|f| pp_field(f, is_variant)), ";");
    enclose_space("{", fields, "}")
}

pub fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .append(RcDoc::space())
        .append(rets.append(modes))
        .nest(INDENT_SPACE)
}

pub fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("(", doc, ")")
}
pub fn pp_mode(mode: &FuncMode) -> RcDoc {
    match mode {
        FuncMode::Oneway => RcDoc::text("oneway"),
        FuncMode::Query => RcDoc::text("query"),
        FuncMode::CompositeQuery => RcDoc::text("composite_query"),
    }
}
pub fn pp_modes(modes: &[FuncMode]) -> RcDoc {
    RcDoc::concat(modes.iter().map(|m| RcDoc::space().append(pp_mode(m))))
}

fn pp_service(serv: &[(String, Type)]) -> RcDoc {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func_doc = match func.as_ref() {
                TypeInner::Func(ref f) => pp_function(f),
                TypeInner::Var(_) => pp_ty(func),
                _ => unreachable!(),
            };
            pp_text(id).append(kwd(" :")).append(func_doc)
        }),
        ";",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs(env: &TypeEnv) -> RcDoc {
    lines(env.0.iter().map(|(id, ty)| {
        kwd("type")
            .append(ident(id))
            .append(kwd("="))
            .append(pp_ty(ty))
            .append(";")
    }))
}

fn pp_actor(ty: &Type) -> RcDoc {
    match ty.as_ref() {
        TypeInner::Service(ref serv) => pp_service(serv),
        TypeInner::Var(_) | TypeInner::Class(_, _) => pp_ty(ty),
        _ => unreachable!(),
    }
}

pub fn pp_init_args<'a>(env: &'a TypeEnv, args: &'a [Type]) -> RcDoc<'a> {
    pp_defs(env).append(pp_args(args))
}
pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => pp_defs(env).pretty(LINE_WIDTH).to_string(),
        Some(actor) => {
            let defs = pp_defs(env);
            let actor = kwd("service :").append(pp_actor(actor));
            let doc = defs.append(actor);
            doc.pretty(LINE_WIDTH).to_string()
        }
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "value")))]
#[cfg(feature = "value")]
pub mod value {
    use super::{ident_string, pp_text};
    use crate::pretty::utils::*;
    use crate::types::value::{IDLArgs, IDLField, IDLValue};
    use crate::types::Label;
    use crate::utils::pp_num_str;
    use std::fmt;

    use ::pretty::RcDoc;

    // TODO config this
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
            Nat16(n) => pp_num_str(&n.to_string()),
            Nat32(n) => pp_num_str(&n.to_string()),
            Nat64(n) => pp_num_str(&n.to_string()),
            Int8(n) => n.to_string(),
            Int16(n) => pp_num_str(&n.to_string()),
            Int32(n) => pp_num_str(&n.to_string()),
            Int64(n) => pp_num_str(&n.to_string()),
            Float32(f) => {
                if f.is_finite() && f.trunc() == *f {
                    format!("{f}.0")
                } else {
                    f.to_string()
                }
            }
            Float64(f) => {
                if f.is_finite() && f.trunc() == *f {
                    format!("{f}.0")
                } else {
                    f.to_string()
                }
            }
            _ => unreachable!(),
        }
    }
    impl fmt::Debug for IDLValue {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            use IDLValue::*;
            match self {
                Null => write!(f, "null : null"),
                Bool(b) => write!(f, "{b}"),
                Number(n) => write!(f, "{n}"),
                Int(i) => write!(f, "{i} : int"),
                Nat(n) => write!(f, "{n} : nat"),
                Nat8(n) => write!(f, "{n} : nat8"),
                Nat16(n) => write!(f, "{} : nat16", pp_num_str(&n.to_string())),
                Nat32(n) => write!(f, "{} : nat32", pp_num_str(&n.to_string())),
                Nat64(n) => write!(f, "{} : nat64", pp_num_str(&n.to_string())),
                Int8(n) => write!(f, "{n} : int8"),
                Int16(n) => write!(f, "{} : int16", pp_num_str(&n.to_string())),
                Int32(n) => write!(f, "{} : int32", pp_num_str(&n.to_string())),
                Int64(n) => write!(f, "{} : int64", pp_num_str(&n.to_string())),
                Float32(_) => write!(f, "{} : float32", number_to_string(self)),
                Float64(_) => write!(f, "{} : float64", number_to_string(self)),
                Text(s) => write!(f, "{s:?}"),
                None => write!(f, "null"),
                Reserved => write!(f, "null : reserved"),
                Principal(id) => write!(f, "principal \"{id}\""),
                Service(id) => write!(f, "service \"{id}\""),
                Func(id, meth) => write!(f, "func \"{}\".{}", id, ident_string(meth)),
                Opt(v) if has_type_annotation(v) => write!(f, "opt ({v:?})"),
                Opt(v) => write!(f, "opt {v:?}"),
                Blob(b) => {
                    write!(f, "blob \"")?;
                    let is_ascii = b
                        .iter()
                        .all(|c| (0x20u8..=0x7eu8).contains(c) || [0x09, 0x0a, 0x0d].contains(c));
                    if is_ascii {
                        for v in b.iter() {
                            write!(f, "{}", pp_char(*v))?;
                        }
                    } else {
                        for v in b.iter() {
                            write!(f, "\\{v:02x}")?;
                        }
                    }
                    write!(f, "\"")
                }
                Vec(vs) => {
                    if let Some(Nat8(_)) = vs.first() {
                        write!(f, "blob \"")?;
                        for v in vs.iter() {
                            match v {
                                // only here for completeness. The deserializer should generate IDLValue::Blob instead.
                                Nat8(v) => write!(f, "{}", &pp_char(*v))?,
                                _ => unreachable!(),
                            }
                        }
                        write!(f, "\"")
                    } else {
                        write!(f, "vec {{")?;
                        for v in vs.iter() {
                            write!(f, " {v:?};")?
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
                            write!(f, " {e:?};")?;
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
            let lab = match &self.id {
                Label::Named(id) => ident_string(id),
                id => id.to_string(),
            };
            write!(f, "{} = {:?}", lab, self.val)
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

    fn pp_label(id: &Label) -> RcDoc {
        match id {
            Label::Named(id) => pp_text(id),
            Label::Id(_) | Label::Unnamed(_) => RcDoc::as_string(id),
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
        let is_ascii = (0x20u8..=0x7eu8).contains(&v);
        if is_ascii && v != 0x22 && v != 0x27 && v != 0x60 && v != 0x5c {
            std::char::from_u32(v as u32).unwrap().to_string()
        } else {
            format!("\\{v:02x}")
        }
    }
    pub fn pp_value(depth: usize, v: &IDLValue) -> RcDoc {
        use IDLValue::*;
        if depth == 0 {
            return RcDoc::as_string(format!("{v:?}"));
        }
        match v {
            Text(ref s) => RcDoc::as_string(format!("\"{}\"", s.escape_debug())),
            Opt(v) if has_type_annotation(v) => {
                kwd("opt").append(enclose("(", pp_value(depth - 1, v), ")"))
            }
            Opt(v) => kwd("opt").append(pp_value(depth - 1, v)),
            Vec(vs) => {
                if matches!(vs.first(), Some(Nat8(_))) || vs.len() > MAX_ELEMENTS_FOR_PRETTY_PRINT {
                    RcDoc::as_string(format!("{v:?}"))
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
            Variant(v) => {
                kwd("variant").append(enclose_space("{", pp_field(depth, &v.0, true), "}"))
            }
            _ => RcDoc::as_string(format!("{v:?}")),
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
}
