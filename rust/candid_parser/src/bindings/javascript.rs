use super::analysis::{chase_actor, chase_types, infer_rec};
use candid::pretty::candid::pp_mode;
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;
use std::collections::BTreeSet;

// The definition of tuple is language specific.
fn is_tuple(t: &Type) -> bool {
    match t.as_ref() {
        TypeInner::Record(ref fs) => is_tuple_fields(fs),
        _ => false,
    }
}

pub(crate) fn is_tuple_fields(fs: &[Field]) -> bool {
    if fs.is_empty() {
        return false;
    }
    for (i, field) in fs.iter().enumerate() {
        if field.id.get_id() != (i as u32) {
            return false;
        }
    }
    true
}

static KEYWORDS: [&str; 64] = [
    "abstract",
    "arguments",
    "await",
    "boolean",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "double",
    "else",
    "enum",
    "eval",
    "export",
    "extends",
    "false",
    "final",
    "finally",
    "float",
    "for",
    "function",
    "goto",
    "if",
    "implements",
    "import",
    "in",
    "instanceof",
    "int",
    "interface",
    "let",
    "long",
    "native",
    "new",
    "null",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "short",
    "static",
    "super",
    "switch",
    "synchronized",
    "this",
    "throw",
    "throws",
    "transient",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "volatile",
    "while",
    "with",
    "yield",
];
pub(crate) fn ident(id: &str) -> RcDoc {
    if KEYWORDS.contains(&id) {
        str(id).append("_")
    } else {
        str(id)
    }
}

fn pp_ty(ty: &Type) -> RcDoc {
    use TypeInner::*;
    match ty.as_ref() {
        Null => str("IDL.Null"),
        Bool => str("IDL.Bool"),
        Nat => str("IDL.Nat"),
        Int => str("IDL.Int"),
        Nat8 => str("IDL.Nat8"),
        Nat16 => str("IDL.Nat16"),
        Nat32 => str("IDL.Nat32"),
        Nat64 => str("IDL.Nat64"),
        Int8 => str("IDL.Int8"),
        Int16 => str("IDL.Int16"),
        Int32 => str("IDL.Int32"),
        Int64 => str("IDL.Int64"),
        Float32 => str("IDL.Float32"),
        Float64 => str("IDL.Float64"),
        Text => str("IDL.Text"),
        Reserved => str("IDL.Reserved"),
        Empty => str("IDL.Empty"),
        Var(ref s) => ident(s),
        Principal => str("IDL.Principal"),
        Opt(ref t) => str("IDL.Opt").append(enclose("(", pp_ty(t), ")")),
        Vec(ref t) => str("IDL.Vec").append(enclose("(", pp_ty(t), ")")),
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ",");
                str("IDL.Tuple").append(enclose("(", tuple, ")"))
            } else {
                str("IDL.Record").append(pp_fields(fs))
            }
        }
        Variant(ref fs) => str("IDL.Variant").append(pp_fields(fs)),
        Func(ref func) => str("IDL.Func").append(pp_function(func)),
        Service(ref serv) => str("IDL.Service").append(pp_service(serv)),
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown | Future => unreachable!(),
    }
}

fn pp_label(id: &SharedLabel) -> RcDoc {
    match &**id {
        Label::Named(str) => quote_ident(str),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field(field: &Field) -> RcDoc {
    pp_label(&field.id)
        .append(kwd(":"))
        .append(pp_ty(&field.ty))
}

fn pp_fields(fs: &[Field]) -> RcDoc {
    let fields = concat(fs.iter().map(pp_field), ",");
    enclose_space("({", fields, "})")
}

fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_rets(&func.rets);
    let modes = pp_modes(&func.modes);
    let doc = concat([args, rets, modes].into_iter(), ",");
    enclose("(", doc, ")").nest(INDENT_SPACE)
}

fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("[", doc, "]")
}

fn pp_rets(args: &[Type]) -> RcDoc {
    pp_args(args)
}

fn pp_modes(modes: &[candid::types::FuncMode]) -> RcDoc {
    let doc = concat(
        modes
            .iter()
            .map(|m| str("'").append(pp_mode(m)).append("'")),
        ",",
    );
    enclose("[", doc, "]")
}

fn pp_service(serv: &[(String, Type)]) -> RcDoc {
    let doc = concat(
        serv.iter()
            .map(|(id, func)| quote_ident(id).append(kwd(":")).append(pp_ty(func))),
        ",",
    );
    enclose_space("({", doc, "})")
}

fn pp_defs<'a>(
    env: &'a TypeEnv,
    def_list: &'a [&'a str],
    recs: &'a BTreeSet<&'a str>,
    export: bool,
) -> RcDoc<'a> {
    let export_prefix = if export { str("export ") } else { RcDoc::nil() };

    let recs_doc = lines(recs.iter().map(|id| {
        export_prefix
            .clone()
            .append(kwd("const"))
            .append(ident(id))
            .append(" = IDL.Rec();")
    }));
    let defs = lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        if recs.contains(id) {
            ident(id)
                .append(".fill")
                .append(enclose("(", pp_ty(ty), ");"))
        } else {
            export_prefix
                .clone()
                .append(kwd("const"))
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(ty))
                .append(";")
        }
    }));
    recs_doc.append(defs)
}

fn pp_actor<'a>(ty: &'a Type, recs: &'a BTreeSet<&'a str>) -> RcDoc<'a> {
    match ty.as_ref() {
        TypeInner::Service(_) => pp_ty(ty),
        TypeInner::Var(id) => {
            if recs.contains(&*id.clone()) {
                str(id).append(".getType()")
            } else {
                str(id)
            }
        }
        TypeInner::Class(_, t) => pp_actor(t, recs),
        _ => unreachable!(),
    }
}

fn pp_deprecation_comment<'a>() -> RcDoc<'a> {
    str("/**").append(RcDoc::hardline())
        .append(" * @deprecated Import IDL types directly from this module instead of using this factory function.")
        .append(RcDoc::hardline())
        .append(" */")
        .append(RcDoc::hardline())
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => {
            let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
            let recs = infer_rec(env, &def_list).unwrap();
            let import_doc = str("import { IDL } from '@dfinity/candid';");
            let doc = pp_defs(env, &def_list, &recs, true);
            let result = import_doc
                .append(RcDoc::hardline())
                .append(RcDoc::hardline())
                .append(doc)
                .pretty(LINE_WIDTH)
                .to_string();

            result
        }
        Some(actor) => {
            let def_list = chase_actor(env, actor).unwrap();
            let recs = infer_rec(env, &def_list).unwrap();
            let init = if let TypeInner::Class(ref args, _) = actor.as_ref() {
                args.as_slice()
            } else {
                &[][..]
            };

            let import_doc = str("import { IDL } from '@dfinity/candid';");
            let defs = pp_defs(env, &def_list, &recs, true);
            let actor = pp_actor(actor, &recs);

            let idl_service = str("export const idlService = ")
                .append(actor.clone())
                .append(";");

            let idl_init_args = str("export const idlInitArgs = ")
                .append(pp_rets(init))
                .append(";");

            let idl_factory_return = kwd("return").append(actor).append(";");
            let idl_factory_body = pp_defs(env, &def_list, &recs, false).append(idl_factory_return);
            let idl_factory_doc = pp_deprecation_comment()
                .append(str("export const idlFactory = ({ IDL }) => "))
                .append(enclose_space("{", idl_factory_body, "};"));

            let init_defs = chase_types(env, init).unwrap();
            let init_recs = infer_rec(env, &init_defs).unwrap();
            let init_defs_doc = pp_defs(env, &init_defs, &init_recs, false);
            let init_doc = kwd("return").append(pp_rets(init)).append(";");
            let init_doc = init_defs_doc.append(init_doc);
            let init_doc = pp_deprecation_comment()
                .append(str("export const init = ({ IDL }) => "))
                .append(enclose_space("{", init_doc, "};"));
            let init_doc = init_doc.pretty(LINE_WIDTH).to_string();

            let result = import_doc
                .append(RcDoc::hardline())
                .append(RcDoc::hardline())
                .append(defs)
                .append(RcDoc::hardline())
                .append(idl_service)
                .append(RcDoc::hardline())
                .append(RcDoc::hardline())
                .append(idl_init_args)
                .append(RcDoc::hardline())
                .append(RcDoc::hardline())
                .append(idl_factory_doc)
                .append(RcDoc::hardline())
                .append(RcDoc::hardline())
                .append(init_doc);

            result.pretty(LINE_WIDTH).to_string()
        }
    }
}

pub mod value {
    use candid::pretty::candid::value::number_to_string;
    use candid::pretty::utils::*;
    use candid::types::value::{IDLArgs, IDLField, IDLValue};
    use candid::types::Label;
    use pretty::RcDoc;

    fn is_tuple(v: &IDLValue) -> bool {
        match v {
            IDLValue::Record(ref fs) => {
                if fs.is_empty() {
                    return false;
                }
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
            Label::Named(str) => quote_ident(str),
            Label::Id(n) | Label::Unnamed(n) => str("_")
                .append(RcDoc::as_string(n))
                .append("_")
                .append(RcDoc::space()),
        }
    }
    fn pp_field(field: &IDLField) -> RcDoc {
        pp_label(&field.id)
            .append(": ")
            .append(pp_value(&field.val))
    }

    fn pp_fields(fields: &[IDLField]) -> RcDoc {
        concat(fields.iter().map(pp_field), ",")
    }

    pub fn pp_value(v: &IDLValue) -> RcDoc {
        use IDLValue::*;
        match v {
            Number(_) | Int(_) | Nat(_) | Int64(_) | Nat64(_) => {
                RcDoc::text(format!("BigInt({})", number_to_string(v)))
            }
            Int8(_) | Int16(_) | Int32(_) | Nat8(_) | Nat16(_) | Nat32(_) | Float32(_)
            | Float64(_) => RcDoc::text(number_to_string(v)),
            Bool(_) => RcDoc::as_string(v),
            Null => RcDoc::text("null"),
            Reserved => RcDoc::text("null"),
            Principal(id) => RcDoc::text(format!("Principal.fromText('{id}')")),
            Service(id) => RcDoc::text(format!("Principal.fromText('{id}')")),
            Func(id, meth) => {
                let id = RcDoc::text(format!("Principal.fromText('{id}')"));
                let meth = RcDoc::text(meth);
                RcDoc::text("[")
                    .append(id)
                    .append(", ")
                    .append(meth)
                    .append("]")
            }
            Text(s) => RcDoc::text(format!("'{}'", s.escape_debug())),
            None => RcDoc::text("[]"),
            Opt(v) => enclose_space("[", pp_value(v), "]"),
            Blob(blob) => {
                let body = concat(blob.iter().map(RcDoc::as_string), ",");
                enclose_space("[", body, "]")
            }
            Vec(vs) => {
                let body = concat(vs.iter().map(pp_value), ",");
                enclose_space("[", body, "]")
            }
            Record(fields) => {
                if is_tuple(v) {
                    let tuple = concat(fields.iter().map(|f| pp_value(&f.val)), ",");
                    enclose_space("[", tuple, "]")
                } else {
                    enclose_space("{", pp_fields(fields), "}")
                }
            }
            Variant(v) => enclose_space("{", pp_field(&v.0), "}"),
        }
    }

    pub fn pp_args(args: &IDLArgs) -> RcDoc {
        let body = concat(args.args.iter().map(pp_value), ",");
        enclose("[", body, "]")
    }
}
