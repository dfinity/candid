use std::any::Any;
use super::analysis::{chase_actor, chase_types, infer_rec};
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;
use std::collections::BTreeSet;
use std::process::id;
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::null;
use lazy_static::lazy_static; // 1.4.0
use std::sync::Mutex;

lazy_static! {
    static ref PRIVILEGES2: Mutex<HashMap<String, Vec<String>>> = Mutex::new(HashMap::new());
}

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
        match PRIVILEGES2.lock().unwrap().get(id) {
            None => {
                str(id)
            }
            Some(it) => {
                RcDoc::text(it.get(1).unwrap().to_owned())
            }
        }
    }
}

pub(crate) fn ident_for_var(id: &str) -> RcDoc {
    if KEYWORDS.contains(&id) {
        str(id).append("_")
    } else {
        match PRIVILEGES2.lock().unwrap().get(id) {
            None => {
                str(id).append(".idl")
            }
            Some(it) => {
                RcDoc::text(it.get(0).unwrap().to_owned())
            }
        }
    }
}

fn pp_ty_init_individual<'a>(id:&'a str, type_str: RcDoc<'a>, dart_type:String) ->RcDoc<'a>{
    PRIVILEGES2.lock().unwrap().insert(id.to_string(), vec![type_str.pretty(LINE_WIDTH).to_string(), dart_type]);
    kwd("final").append(id).append("=").append(type_str).append(";")
}

fn pp_ty_init<'a>(ty: &'a Type, id:&'a str) -> RcDoc<'a> {
    use Type::*;
    match *ty {
        Null => pp_ty_init_individual(id, str("IDL.Null"), String::from("dynamic")),
        Bool => pp_ty_init_individual(id, str("IDL.Bool"), String::from("bool")),
        Nat => pp_ty_init_individual(id, str("IDL.Nat"), String::from("BigInt")),
        Int => pp_ty_init_individual(id, str("IDL.Int"), String::from("int")),
        Nat8 => pp_ty_init_individual(id, str("IDL.Nat8"), String::from("int")),
        Nat16 => pp_ty_init_individual(id, str("IDL.Nat16"), String::from("int")),
        Nat32 => pp_ty_init_individual(id, str("IDL.Nat32"), String::from("int")),
        Nat64 => pp_ty_init_individual(id, str("IDL.Nat64"), String::from("int")),
        Int8 => pp_ty_init_individual(id, str("IDL.Int8"), String::from("int")),
        Int16 => pp_ty_init_individual(id, str("IDL.Int16"), String::from("int")),
        Int32 => pp_ty_init_individual(id, str("IDL.Int32"), String::from("int")),
        Int64 => pp_ty_init_individual(id, str("IDL.Int64"), String::from("int")),
        Float32 => pp_ty_init_individual(id, str("IDL.Float32"), String::from("double")),
        Float64 => pp_ty_init_individual(id, str("IDL.Float64"), String::from("double")),
        Text => pp_ty_init_individual(id, str("IDL.Text"), String::from("String")),
        Reserved => pp_ty_init_individual(id, str("IDL.Reserved"), String::from("IDL.Reserved")),
        Empty => pp_ty_init_individual(id, str("IDL.Empty"), String::from("IDL.Empty")),
        Var(ref s) => ident_for_var(s),
        Principal => str("IDL.Principal"),
        Opt(ref t) => pp_ty_init_individual(id, str("IDL.Opt").append(enclose("(", pp_ty_raw(t), ")")),
                                            pp_ty_for_field(ty).pretty(LINE_WIDTH).to_string()),
        Vec(ref t) => {
            pp_ty_init_individual(id, str("IDL.Vec").append(enclose("(", pp_ty_raw(t), ")")),
                                  pp_ty_for_field(ty).pretty(LINE_WIDTH).to_string())
        },
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ",");
                str("IDL.Tuple").append(enclose("(", tuple, ")"))
            } else {
                kwd("class")
                    .append(str(id))
                    .append(enclose("{",
                                    str("").append(pp_fields(fs))
                                        .append(RcDoc::hardline())
                                        .append(pp_fields_constructor(fs,id))
                                        .append(RcDoc::hardline())
                                        .append(pp_factory(fs,id))
                                        .append(RcDoc::hardline())
                                        .append(pp_to_json(fs))
                                        .append(RcDoc::hardline())
                                        .append(pp_create_static_idl(fs))
                                    ,"};"))

                // str("IDL.Record").append(pp_fields(fs))
            }
        }
        Variant(ref fs) => {
            str("IDL.Variant").append(pp_fields(fs))
        },
        Func(ref func) => {
            str("IDL.Func").append(pp_function(func))
        },
        Service(ref serv) => {
            str("IDL.Service").append(pp_service(serv))
        },
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}


fn pp_ty_for_field<'a>(ty: &'a Type) -> RcDoc<'a> {
    use Type::*;
    match *ty {
        Null => str("dynamic"),
        Bool => str("bool"),
        Nat => str("BigInt"),
        Int => str("int"),
        Nat8 => str("int"),
        Nat16 => str("int"),
        Nat32 => str("int"),
        Nat64 => str("int"),
        Int8 => str("int"),
        Int16 => str("int"),
        Int32 => str("int"),
        Int64 => str("int"),
        Float32 => str("double"),
        Float64 => str("double"),
        Text => str("String"),
        Reserved => str("IDL.Reserved"),
        Empty => str("IDL.Empty"),
        Var(ref s) => ident(s),
        Principal => str("Principal"),
        Opt(ref t) => {
            pp_ty_for_field(t).append("?")
        },
        Vec(ref t) => {
            str("List").append(enclose("<", pp_ty_for_field(t), ">"))
        },
        Record(ref fs) => unreachable!(),
        Variant(ref fs) => {
            str("IDL.Variant").append(pp_fields(fs))
        },
        Func(ref func) => {
            str("IDL.Func").append(pp_function(func))
        },
        Service(ref serv) => {
            str("IDL.Service").append(pp_service(serv))
        },
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}
fn pp_ty<'a>(ty: &'a Type) -> RcDoc<'a> {
    use Type::*;
    match *ty {
        Null => str("IDL.Null"),
        Bool => str("IDL.Bool"),
        Nat => str("BigInt"),
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
        Text => str("String"),
        Reserved => str("IDL.Reserved"),
        Empty => str("IDL.Empty"),
        Var(ref s) => ident_for_var(s),
        Principal => str("IDL.Principal"),
        Opt(ref t) => {
            str("IDL.Opt").append(enclose("(", pp_ty(t), ")"))
        },
        Vec(ref t) => {
            str("IDL.Vec").append(enclose("(", pp_ty(t ), ")"))
        },
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ",");
                str("IDL.Tuple").append(enclose("(", tuple, ")"))
            } else {
                str("IDL.Record").append(pp_fields(fs))
            }
        }
        Variant(ref fs) => {
            str("IDL.Variant").append(pp_fields(fs ))
        },
        Func(ref func) => {
            str("IDL.Func").append(pp_function(func ))
        },
        Service(ref serv) => {
            str("IDL.Service").append(pp_service(serv ))
        },
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}

fn pp_ty_raw<'a>(ty: &'a Type) -> RcDoc<'a> {
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
        Var(ref s) => ident_for_var(s),
        Principal => str("IDL.Principal"),
        Opt(ref t) => {
            str("IDL.Opt").append(enclose("(", pp_ty_raw(t), ")"))
        },
        Vec(ref t) => {
            str("IDL.Vec").append(enclose("(", pp_ty_raw(t ), ")"))
        },
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty_raw(&f.ty)), ",");
                str("IDL.Tuple").append(enclose("(", tuple, ")"))
            } else {
                str("IDL.Record").append(pp_fields(fs))
            }
        }
        Variant(ref fs) => {
            str("IDL.Variant").append(pp_fields(fs ))
        },
        Func(ref func) => {
            str("IDL.Func").append(pp_function(func ))
        },
        Service(ref serv) => {
            str("IDL.Service").append(pp_service(serv ))
        },
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}

fn pp_ty_for_function<'a>(ty: &'a Type) -> RcDoc<'a> {
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
        Var(ref s) => ident_for_var(s),
        Principal => str("IDL.Principal"),
        Opt(ref t) => {
            str("IDL.Opt").append(enclose("(", pp_ty(t), ")"))
        },
        Vec(ref t) => {
            str("IDL.Vec").append(enclose("(", pp_ty(t), ")"))
        },
        Record(ref fs) => unreachable!(),
        Variant(ref fs) => {
            str("IDL.Variant").append(pp_fields(fs))
        },
        Func(ref func) => {
            str("IDL.Func").append(pp_function(func))
        },
        Service(ref serv) => {
            str("IDL.Service").append(pp_service(serv))
        },
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(name) => str(name),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_"),
    }
}


fn pp_field<'a>(field: &'a Field) -> RcDoc<'a> {
    let lable = pp_label(&field.id);
    str("").append(pp_ty_for_field(&field.ty)).append(" ").append(lable)
}

fn pp_fields<'a>(fs: &'a [Field]) -> RcDoc<'a> {
    concat(fs.iter().map(pp_field), ";")
}


fn pp_fields_constructor<'a>(fs: &'a [Field],class_name:&'a str) -> RcDoc<'a> {
    str(class_name).append(enclose("({",concat(fs.iter().map(pp_field_in_constructor), ","),"})"))
}

fn pp_factory<'a>(fs: &'a [Field],class_name:&'a str) -> RcDoc<'a> {
    kwd("factory")
        .append(class_name)
        .append(".fromMap(Map map)")
        .append(enclose("({",
                        kwd("return").append(class_name).append(
                                enclose("(",
                                        concat(fs.iter().map(pp_field_in_factory), ","),
                                        ")"))
                            ,"});"))
}

fn pp_create_static_idl<'a>(fs: &'a [Field]) -> RcDoc<'a> {
    str("static Record idl = IDL.Record").append(enclose("({",concat(fs.iter().map(pp_field_in_static_idl), ","),"});"))
}

fn pp_to_json(fs: &[Field]) -> RcDoc {
    //todo fix class name
    str("Map<String,dynamic> toJson()=>")
        .append(enclose("{",
                        str("").append(concat(fs.iter().map(pp_field_in_to_json), ","))
                        ,"}..removeWhere((dynamic key,dynamic value)=> key==null||value==null);"))
}

fn pp_field_in_factory(field: &Field) -> RcDoc {
    pp_label(&field.id).append(":").append(
        enclose("map[\"",pp_label(&field.id),"\"]"))
}

fn pp_field_in_static_idl<'a>(field: &'a Field) -> RcDoc<'a> {
    enclose("\"",pp_label(&field.id),"\"").append(":").append(pp_ty_raw(&field.ty))
}

fn pp_field_in_to_json(field: &Field) -> RcDoc {
    enclose("\"",pp_label(&field.id),"\"").append(":").append(pp_label(&field.id))
}

fn pp_field_in_constructor(field: &Field) -> RcDoc {
    str("").append("this.").append(pp_label(&field.id))
}

fn pp_function<'a>(func: &'a Function) -> RcDoc<'a> {
    let args = pp_args_for_function(&func.args);
    let rets = pp_args_for_function(&func.rets);
    let modes = pp_modes(&func.modes);
    let items = [args, rets, modes];
    let doc = concat(items.iter().cloned(), ",");
    enclose("(", doc, ")").nest(INDENT_SPACE)
}

// fn pp_args(args: &[Type]) -> RcDoc {
//     let doc = concat(args.iter().map(pp_ty), ",");
//     enclose("[", doc, "]")
// }

fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("[", doc, "]")
}

fn pp_args_for_function<'a>(args: &'a [Type]) -> RcDoc<'a> {
    enclose("[", concat(args.iter().map(pp_ty_for_function), ","), "]")
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

fn pp_service<'a>(serv: &'a [(String, Type)]) -> RcDoc<'a> {
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
    recs: &'a BTreeSet<&'a str>
) -> RcDoc<'a> {
    let recs_doc = str("");
    lines(def_list.iter().map(|id| unsafe {
        let ty = env.find_type(id).unwrap();
            pp_ty_init(ty,id)
    }));

    let defs = lines(def_list.iter().rev().map(|id| unsafe {
        let ty = env.find_type(id).unwrap();
        pp_ty_init(ty,id)
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
            // println!("AAAAA {}",PRIVILEGES2.lock().unwrap().get("TextField").unwrap().get(1).unwrap().to_owned());
            doc.pretty(LINE_WIDTH).to_string()
        }
        Some(actor) => {
            let def_list = chase_actor(env, actor).unwrap();
            let recs = infer_rec(env, &def_list).unwrap();

            // 处理定义
            let defs = pp_defs(env, &def_list, &recs);

            //处理actor
            let pp = pp_actor(actor, &recs );

            //整合定义和actor
            let actor = kwd("Service _Service = ").append(pp).append(";");
            let body = defs.append(actor);
            return body.pretty(LINE_WIDTH).to_string();
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
        concat(fields.iter().map(|f| pp_field(f)), ",")
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
                let body = concat(vs.iter().map(|v| pp_value(v)), ",");
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
