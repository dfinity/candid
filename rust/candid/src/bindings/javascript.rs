use super::analysis::{chase_actor, infer_rec};
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;
use std::collections::BTreeSet;

// The definition of tuple is language specific.
fn is_tuple(t: &Type) -> bool {
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
        Var(ref s) => str(s),
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
        _ => unreachable!(),
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
            .map(|id| kwd("const").append(ident(id)).append("= IDL.Rec();")),
    );
    let defs = lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        if recs.contains(id) {
            str(id)
                .append(".fill")
                .append(enclose("(", pp_ty(ty), ");"))
        } else {
            kwd("const")
                .append(ident(id))
                .append(kwd("="))
                .append(pp_ty(ty))
                .append(";")
        }
    }));
    recs_doc.append(defs)
}

fn pp_actor<'a>(ty: &'a Type, recs: &'a BTreeSet<&'a str>) -> RcDoc<'a> {
    let doc = match ty {
        Type::Service(_) => pp_ty(ty),
        Type::Var(id) => {
            if recs.contains(&*id.clone()) {
                str(id).append(".getType()")
            } else {
                str(id)
            }
        }
        _ => unreachable!(),
    };
    kwd("return").append(doc).append(";")
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => "".to_string(),
        Some(actor) => {
            let def_list = chase_actor(env, actor).unwrap();
            let recs = infer_rec(env, &def_list).unwrap();
            let defs = pp_defs(env, &def_list, &recs);
            let actor = pp_actor(actor, &recs);
            let body = defs.append(actor);
            let doc = str("export default ({ IDL }) => ").append(enclose_space("{", body, "};"));
            doc.pretty(LINE_WIDTH).to_string()
        }
    }
}

use crate::parser::test::{Input, Test};

impl Input {
    fn js_parse<'a>(&self, ty: RcDoc<'a>) -> RcDoc<'a> {
        match self {
            Input::Blob(bytes) => {
                let hex = str("Buffer.from('")
                    .append(RcDoc::as_string(hex::encode(&bytes)))
                    .append("', 'hex')");
                let items = [ty, hex];
                let params = concat(items.iter().cloned(), ",");
                str("IDL.decode").append(enclose("(", params, ")"))
            }
            _ => RcDoc::nil(),
        }
    }
}

pub fn test_generate(test: Test) -> String {
    let mut res = String::new();
    let env = TypeEnv::new();
    let mut types = Vec::new();
    for (i, assert) in test.asserts.iter().enumerate() {
        let desc = match &assert.desc {
            Some(desc) => format!("{}:{}", i + 1, desc),
            None => format!("{}", i + 1),
        };
        let desc = RcDoc::text(desc);
        types.clear();
        for ty in assert.typ.iter() {
            types.push(env.ast_to_type(ty).unwrap());
        }
        let ty = pp_args(&types);
        let test_func = assert.left.js_parse(ty);
        let body = if assert.pass {
            enclose("expect(", test_func, ")").append(".toEqual(expect.anything());")
        } else {
            enclose("expect(", str("() => ").append(test_func), ")").append(".toThrow();")
        };
        let doc = str("test('")
            .append(desc)
            .append("', () => ")
            .append(enclose_space("{", body, "}"));
        res = res + &doc.pretty(LINE_WIDTH).to_string() + "\n";
    }
    res
}
