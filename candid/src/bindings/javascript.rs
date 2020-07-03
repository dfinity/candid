use crate::parser::types::IDLProg;
use crate::parser::typing::{ActorEnv, TypeEnv};
use crate::types::{Field, Function, Type};
use pretty::RcDoc;

fn enclose<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    RcDoc::text(left)
        .append(RcDoc::line_())
        .append(doc)
        .nest(2)
        .append(RcDoc::line_())
        .append(right)
        .group()
}

fn concat<'a, D>(docs: D, sep: &'a str) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::intersperse(
        docs,
        if sep != " " {
            RcDoc::text(sep).append(RcDoc::line())
        } else {
            RcDoc::space()
        },
    )
}

fn kwd<U: std::fmt::Display + ?Sized>(str: &U) -> RcDoc {
    RcDoc::as_string(str).append(RcDoc::space())
}
fn str(str: &str) -> RcDoc {
    RcDoc::text(str)
}
fn ident(id: &str) -> RcDoc {
    kwd(id)
}
fn quote_ident(id: &str) -> RcDoc {
    str("'").append(id).append("'").append(RcDoc::space())
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
        Record(ref fs) => str("IDL.Record").append(pp_fields(fs)),
        Variant(ref fs) => str("IDL.Variant").append(pp_fields(fs)),
        Func(ref func) => str("IDL.Func").append(pp_function(func)),
        Service(ref serv) => str("IDL.Service").append(pp_service(serv)),
        _ => unreachable!(),
    }
}

fn pp_field(field: &Field) -> RcDoc {
    let name = if field.is_named() {
        quote_ident(&field.id)
    } else {
        str("_").append(&field.id).append("_")
    };
    name.append(kwd(":")).append(pp_ty(&field.ty))
}

fn pp_fields(fs: &[Field]) -> RcDoc {
    let fields = concat(fs.iter().map(pp_field), ",");
    enclose("({", fields, "})")
}

fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    let items = [args, rets, modes];
    let doc = concat(items.iter().map(|e| e.clone()), ",");
    enclose("(", doc, ")")
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

fn pp_service(serv: &[(String, Function)]) -> RcDoc {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func_doc = str("IDL.Func").append(pp_function(func));
            quote_ident(id).append(kwd(":")).append(func_doc)
        }),
        ",",
    );
    enclose("({", doc, "})")
}

fn pp_env(env: &TypeEnv) -> RcDoc {
    RcDoc::concat(env.0.iter().map(|(id, ty)| {
        kwd("const")
            .append(ident(id))
            .append(kwd("="))
            .append(pp_ty(ty))
            .append(";")
            .append(RcDoc::hardline())
    }))
}

fn pp_actor(actor: &ActorEnv) -> RcDoc {
    let doc = concat(
        actor.iter().map(|(id, func)| {
            let func_doc = str("IDL.Func").append(pp_function(func));
            quote_ident(id).append(kwd(":")).append(func_doc)
        }),
        ",",
    );
    kwd("return")
        .append("IDL.Service")
        .append(enclose("({", doc, "});"))
}

pub fn to_doc<'a>(te: &'a TypeEnv, actor: &'a ActorEnv, _prog: &'a IDLProg) -> RcDoc<'a> {
    let defs = pp_env(te);
    let actor = pp_actor(actor);
    let doc = defs.append(actor);
    str("({ IDL }) => ").append(enclose("{", doc, "}"))
}
