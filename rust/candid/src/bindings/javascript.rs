use super::analysis::{chase_actor, chase_types, infer_rec};
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;
use std::collections::BTreeSet;

// The definition of tuple is language specific.
pub(crate) fn is_tuple(t: &Type) -> bool {
    match t {
        Type::Record(ref fs) => {
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
    use Type::*;
    match *ty {
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
        Knot(_) | Unknown => unreachable!(),
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
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    let items = [args, rets, modes];
    let doc = concat(items.iter().cloned(), ",");
    enclose("(", doc, ")").nest(INDENT_SPACE)
}

fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("[", doc, "]")
}

fn pp_modes(modes: &[crate::parser::types::FuncMode]) -> RcDoc {
    let doc = concat(
        modes
            .iter()
            .map(|m| str("'").append(m.to_doc()).append("'")),
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
) -> RcDoc<'a> {
    let recs_doc = lines(
        recs.iter()
            .map(|id| kwd("const").append(ident(id)).append(" = IDL.Rec();")),
    );
    let defs = lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        if recs.contains(id) {
            ident(id)
                .append(".fill")
                .append(enclose("(", pp_ty(ty), ");"))
        } else {
            kwd("const")
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(ty))
                .append(";")
        }
    }));
    recs_doc.append(defs)
}

fn pp_actor<'a>(ty: &'a Type, recs: &'a BTreeSet<&'a str>) -> RcDoc<'a> {
    match ty {
        Type::Service(_) => pp_ty(ty),
        Type::Var(id) => {
            if recs.contains(&*id.clone()) {
                str(id).append(".getType()")
            } else {
                str(id)
            }
        }
        Type::Class(_, t) => pp_actor(t, recs),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => {
            let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
            let recs = infer_rec(env, &def_list).unwrap();
            let doc = pp_defs(env, &def_list, &recs);
            doc.pretty(LINE_WIDTH).to_string()
        }
        Some(actor) => {
            let def_list = chase_actor(env, actor).unwrap();
            let recs = infer_rec(env, &def_list).unwrap();
            let defs = pp_defs(env, &def_list, &recs);
            let init = if let Type::Class(ref args, _) = actor {
                args.as_slice()
            } else {
                &[][..]
            };
            let actor = kwd("return").append(pp_actor(actor, &recs)).append(";");
            let body = defs.append(actor);
            let doc = str("export const idlFactory = ({ IDL }) => ")
                .append(enclose_space("{", body, "};"));
            // export init args
            let init_defs = chase_types(env, init).unwrap();
            let init_recs = infer_rec(env, &init_defs).unwrap();
            let init_defs_doc = pp_defs(env, &init_defs, &init_recs);
            let init_doc = kwd("return").append(pp_args(init)).append(";");
            let init_doc = init_defs_doc.append(init_doc);
            let init_doc =
                str("export const init = ({ IDL }) => ").append(enclose_space("{", init_doc, "};"));
            let init_doc = init_doc.pretty(LINE_WIDTH).to_string();
            let doc = doc.append(RcDoc::hardline()).append(init_doc);
            doc.pretty(LINE_WIDTH).to_string()
        }
    }
}

pub mod value {
    use super::pp_label;
    use crate::parser::pretty::number_to_string;
    use crate::parser::value::{IDLArgs, IDLField, IDLValue};
    use crate::pretty::*;
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
            Principal(id) => RcDoc::text(format!("Principal.fromText('{}')", id)),
            Service(id) => RcDoc::text(format!("Principal.fromText('{}')", id)),
            Func(id, meth) => {
                let id = RcDoc::text(format!("Principal.fromText('{}')", id));
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

pub mod test {
    use super::value;
    use crate::parser::test::{HostAssert, HostTest, Test};
    use crate::pretty::*;
    use crate::TypeEnv;
    use pretty::RcDoc;

    fn pp_hex(bytes: &[u8]) -> RcDoc {
        str("Buffer.from('")
            .append(RcDoc::as_string(hex::encode(bytes)))
            .append("', 'hex')")
    }
    fn pp_encode<'a>(args: &'a crate::IDLArgs, tys: &'a [crate::types::Type]) -> RcDoc<'a> {
        let vals = value::pp_args(args);
        let tys = super::pp_args(tys);
        let items = [tys, vals];
        let params = concat(items.iter().cloned(), ",");
        str("IDL.encode").append(enclose("(", params, ")"))
    }

    fn pp_decode<'a>(bytes: &'a [u8], tys: &'a [crate::types::Type]) -> RcDoc<'a> {
        let hex = pp_hex(bytes);
        let tys = super::pp_args(tys);
        let items = [tys, hex];
        let params = concat(items.iter().cloned(), ",");
        str("IDL.decode").append(enclose("(", params, ")"))
    }

    pub fn test_generate(test: Test) -> String {
        let header = r#"// AUTO-GENERATED. DO NOT EDIT.
// tslint:disable
import * as IDL from './idl';
import { Buffer } from 'buffer/';
import { Principal } from './principal';
"#;
        let mut res = header.to_string();
        let mut env = TypeEnv::new();
        crate::check_prog(
            &mut env,
            &crate::IDLProg {
                decs: test.defs,
                actor: None,
            },
        )
        .unwrap();
        res += &super::compile(&env, &None);
        for (i, assert) in test.asserts.iter().enumerate() {
            let mut types = Vec::new();
            for ty in assert.typ.iter() {
                types.push(env.ast_to_type(ty).unwrap());
            }
            let host = HostTest::from_assert(assert, &env, &types);
            let mut expects = Vec::new();
            for cmd in host.asserts.iter() {
                use HostAssert::*;
                let test_func = match cmd {
                    Encode(args, tys, _, _) | NotEncode(args, tys) => {
                        let items = [super::pp_args(tys), pp_encode(args, tys)];
                        let params = concat(items.iter().cloned(), ",");
                        str("IDL.decode").append(enclose("(", params, ")"))
                    }
                    Decode(bytes, tys, _, _) | NotDecode(bytes, tys) => pp_decode(bytes, tys),
                };
                let (test_func, predicate) = match cmd {
                    Encode(_, _, true, _) | Decode(_, _, true, _) => (test_func, str(".toEqual")),
                    Encode(_, _, false, _) | Decode(_, _, false, _) => {
                        (test_func, str(".not.toEqual"))
                    }
                    NotEncode(_, _) | NotDecode(_, _) => {
                        (str("() => ").append(test_func), str(".toThrow"))
                    }
                };
                let expected = match cmd {
                    Encode(_, tys, _, bytes) => pp_decode(bytes, tys),
                    Decode(_, _, _, vals) => value::pp_args(vals),
                    NotEncode(_, _) | NotDecode(_, _) => RcDoc::nil(),
                };
                let expect = enclose("expect(", test_func, ")")
                    .append(predicate)
                    .append(enclose("(", expected, ");"));
                expects.push(expect);
            }
            let body = RcDoc::intersperse(expects.iter().cloned(), RcDoc::hardline());
            let body = str("test('")
                .append(format!("{} {}", i + 1, host.desc))
                .append("', () => ")
                .append(enclose_space("{", body, "});"))
                .append(RcDoc::hardline());
            res += &body.pretty(LINE_WIDTH).to_string();
        }
        res
    }
}
