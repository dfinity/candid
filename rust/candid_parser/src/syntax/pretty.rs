use pretty::RcDoc;

use crate::{
    pretty::{
        candid::{pp_docs, pp_label_raw, pp_modes, pp_text},
        utils::{ident, kwd, lines, sep_enclose, sep_enclose_space, str, INDENT_SPACE, LINE_WIDTH},
    },
    syntax::{Binding, FuncType, IDLActorType, IDLMergedProg, IDLType, PrimType, TypeField},
};

fn pp_ty(ty: &IDLType) -> RcDoc {
    use IDLType::*;
    match ty {
        PrimT(PrimType::Null) => str("null"),
        PrimT(PrimType::Bool) => str("bool"),
        PrimT(PrimType::Nat) => str("nat"),
        PrimT(PrimType::Int) => str("int"),
        PrimT(PrimType::Nat8) => str("nat8"),
        PrimT(PrimType::Nat16) => str("nat16"),
        PrimT(PrimType::Nat32) => str("nat32"),
        PrimT(PrimType::Nat64) => str("nat64"),
        PrimT(PrimType::Int8) => str("int8"),
        PrimT(PrimType::Int16) => str("int16"),
        PrimT(PrimType::Int32) => str("int32"),
        PrimT(PrimType::Int64) => str("int64"),
        PrimT(PrimType::Float32) => str("float32"),
        PrimT(PrimType::Float64) => str("float64"),
        PrimT(PrimType::Text) => str("text"),
        PrimT(PrimType::Reserved) => str("reserved"),
        PrimT(PrimType::Empty) => str("empty"),
        VarT(ref s) => str(s),
        PrincipalT => str("principal"),
        OptT(ref t) => pp_opt(t),
        VecT(ref t) => pp_vec(t),
        RecordT(ref fs) => pp_record(fs, ty.is_tuple()),
        VariantT(ref fs) => pp_variant(fs),
        FuncT(ref func) => pp_function(func),
        ServT(ref serv) => pp_service(serv),
        ClassT(ref args, ref t) => pp_class(args, t),
    }
}

fn pp_field(field: &TypeField, is_variant: bool) -> RcDoc {
    let docs = pp_docs(&field.docs);
    let ty_doc = if is_variant && field.typ == IDLType::PrimT(PrimType::Null) {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty(&field.typ))
    };
    docs.append(pp_label_raw(&field.label)).append(ty_doc)
}

fn pp_fields(fs: &[TypeField], is_variant: bool) -> RcDoc {
    let fields = fs.iter().map(|f| pp_field(f, is_variant));
    sep_enclose_space(fields, ";", "{", "}")
}

fn pp_opt(ty: &IDLType) -> RcDoc {
    kwd("opt").append(pp_ty(ty))
}

fn pp_vec(ty: &IDLType) -> RcDoc {
    if matches!(ty, IDLType::PrimT(PrimType::Nat8)) {
        str("blob")
    } else {
        kwd("vec").append(pp_ty(ty))
    }
}

fn pp_record(fs: &[TypeField], is_tuple: bool) -> RcDoc {
    if is_tuple {
        let fs = fs.iter().map(|f| pp_ty(&f.typ));
        kwd("record").append(sep_enclose_space(fs, ";", "{", "}"))
    } else {
        kwd("record").append(pp_fields(fs, false))
    }
}

fn pp_variant(fs: &[TypeField]) -> RcDoc {
    kwd("variant").append(pp_fields(fs, true))
}

fn pp_function(func: &FuncType) -> RcDoc {
    kwd("func").append(pp_method(func))
}

fn pp_method(func: &FuncType) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_rets(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .append(RcDoc::space())
        .append(rets.append(modes))
        .nest(INDENT_SPACE)
}

fn pp_args(args: &[IDLType]) -> RcDoc {
    sep_enclose(args.iter().map(pp_ty), ",", "(", ")")
}

fn pp_rets(rets: &[IDLType]) -> RcDoc {
    pp_args(rets)
}

fn pp_service(methods: &[Binding]) -> RcDoc {
    kwd("service").append(pp_service_methods(methods))
}

fn pp_service_methods(methods: &[Binding]) -> RcDoc {
    let methods = methods.iter().map(|b| {
        let docs = pp_docs(&b.docs);
        let func_doc = match b.typ {
            IDLType::FuncT(ref f) => pp_method(f),
            IDLType::VarT(_) => pp_ty(&b.typ),
            _ => unreachable!(),
        };
        docs.append(pp_text(&b.id))
            .append(kwd(" :"))
            .append(func_doc)
    });
    sep_enclose_space(methods, ";", "{", "}")
}

fn pp_class<'a>(args: &'a [IDLType], t: &'a IDLType) -> RcDoc<'a> {
    let doc = pp_args(args).append(" ->").append(RcDoc::space());
    match t {
        IDLType::ServT(ref serv) => doc.append(pp_service_methods(serv)),
        IDLType::VarT(ref s) => doc.append(s),
        _ => unreachable!(),
    }
}

fn pp_defs(prog: &IDLMergedProg) -> RcDoc {
    lines(prog.bindings().map(|b| {
        let docs = pp_docs(&b.docs);
        docs.append(kwd("type"))
            .append(ident(&b.id))
            .append(kwd("="))
            .append(pp_ty(&b.typ))
            .append(";")
    }))
}

fn pp_actor(actor: &IDLActorType) -> RcDoc {
    let docs = pp_docs(&actor.docs);
    let service_doc = match actor.typ {
        IDLType::ServT(ref serv) => pp_service_methods(serv),
        IDLType::VarT(_) | IDLType::ClassT(_, _) => pp_ty(&actor.typ),
        _ => unreachable!(),
    };
    docs.append(kwd("service :")).append(service_doc)
}

pub fn pretty_print(prog: &IDLMergedProg) -> String {
    let actor = prog.resolve_actor().ok().flatten();
    let doc = match actor.as_ref() {
        None => pp_defs(prog),
        Some(actor) => pp_defs(prog).append(pp_actor(actor)),
    };
    doc.pretty(LINE_WIDTH).to_string()
}
