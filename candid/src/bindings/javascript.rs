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

fn pp_ty(ty: &Type) -> RcDoc {
    use Type::*;
    match *ty {
        Null => str("Null"),
        Bool => str("Bool"),
        Nat => str("Nat"),
        Int => str("Int"),
        Nat8 => str("Nat8"),
        Nat16 => str("Nat16"),
        Nat32 => str("Nat32"),
        Nat64 => str("Nat64"),
        Int8 => str("Int8"),
        Int16 => str("Int16"),
        Int32 => str("Int32"),
        Int64 => str("Int64"),
        Float32 => str("Float32"),
        Float64 => str("Float64"),
        Text => str("Text"),
        Reserved => str("Reserved"),
        Empty => str("Empty"),
        Var(ref s) => str(s),
        Principal => str("Principal"),
        Opt(ref t) => str("Opt").append(enclose("(", pp_ty(t), ")")),
        Vec(ref t) => str("Vec").append(enclose("(", pp_ty(t), ")")),
        Record(ref fs) => str("Record").append(pp_fields(fs)),
        Variant(ref fs) => str("Variant").append(pp_fields(fs)),
        Func(ref func) => str("Func").append(pp_function(func)),
        Service(ref serv) => str("Service").append(pp_service(serv)),
        _ => unreachable!(),
    }
}

fn pp_field(field: &Field) -> RcDoc {
    ident(&field.id).append(kwd(":")).append(pp_ty(&field.ty))
}

fn pp_fields(fs: &[Field]) -> RcDoc {
    let fields = concat(fs.iter().map(pp_field), ",");
    enclose("({", fields, "})")
}

fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    let doc = args
        .append(kwd(","))
        .append(rets)
        .append(kwd(","))
        .append(modes);
    enclose("(", doc, ")")
}

fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("[", doc, "]")
}

fn pp_modes(modes: &[crate::parser::types::FuncMode]) -> RcDoc {
    let doc = concat(modes.iter().map(|m| m.to_doc()), ",");
    enclose("[", doc, "]")
}

fn pp_service(serv: &[(String, Function)]) -> RcDoc {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func_doc = str("Func").append(pp_function(func));
            ident(id).append(kwd(":")).append(func_doc)
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
            let func_doc = str("Func").append(pp_function(func));
            ident(id).append(kwd(":")).append(func_doc)
        }),
        ",",
    );
    kwd("return")
        .append("Service")
        .append(enclose("({", doc, "})"))
}

pub fn to_doc<'a>(te: &'a TypeEnv, actor: &'a ActorEnv, _prog: &'a IDLProg) -> RcDoc<'a> {
    let defs = pp_env(te);
    let actor = pp_actor(actor);
    let doc = defs.append(actor);
    str("({ IDL }) => ").append(enclose("{", doc, "}"))
}
