use pretty::RcDoc;

use crate::{
    pretty::{
        candid::{pp_docs, pp_label_raw, pp_modes, pp_text},
        utils::{concat, enclose, enclose_space, ident, kwd, lines, str, INDENT_SPACE, LINE_WIDTH},
    },
    syntax::{
        Binding, FuncType, IDLActorType, IDLMergedProg, IDLType, IDLTypeKind, PrimType, TypeField,
    },
};

fn pp_ty(ty: &IDLType) -> RcDoc<'_> {
    match &ty.kind {
        IDLTypeKind::PrimT(PrimType::Null) => str("null"),
        IDLTypeKind::PrimT(PrimType::Bool) => str("bool"),
        IDLTypeKind::PrimT(PrimType::Nat) => str("nat"),
        IDLTypeKind::PrimT(PrimType::Int) => str("int"),
        IDLTypeKind::PrimT(PrimType::Nat8) => str("nat8"),
        IDLTypeKind::PrimT(PrimType::Nat16) => str("nat16"),
        IDLTypeKind::PrimT(PrimType::Nat32) => str("nat32"),
        IDLTypeKind::PrimT(PrimType::Nat64) => str("nat64"),
        IDLTypeKind::PrimT(PrimType::Int8) => str("int8"),
        IDLTypeKind::PrimT(PrimType::Int16) => str("int16"),
        IDLTypeKind::PrimT(PrimType::Int32) => str("int32"),
        IDLTypeKind::PrimT(PrimType::Int64) => str("int64"),
        IDLTypeKind::PrimT(PrimType::Float32) => str("float32"),
        IDLTypeKind::PrimT(PrimType::Float64) => str("float64"),
        IDLTypeKind::PrimT(PrimType::Text) => str("text"),
        IDLTypeKind::PrimT(PrimType::Reserved) => str("reserved"),
        IDLTypeKind::PrimT(PrimType::Empty) => str("empty"),
        IDLTypeKind::VarT(ref s) => str(s),
        IDLTypeKind::PrincipalT => str("principal"),
        IDLTypeKind::OptT(ref t) => pp_opt(t),
        IDLTypeKind::VecT(ref t) => pp_vec(t),
        IDLTypeKind::RecordT(ref fs) => pp_record(fs, ty.is_tuple()),
        IDLTypeKind::VariantT(ref fs) => pp_variant(fs),
        IDLTypeKind::FuncT(ref func) => pp_function(func),
        IDLTypeKind::ServT(ref serv) => pp_service(serv),
        IDLTypeKind::ClassT(ref args, ref t) => pp_class(args, t),
    }
}

fn pp_field(field: &TypeField, is_variant: bool) -> RcDoc<'_> {
    let docs = pp_docs(&field.docs);
    let ty_doc = if is_variant && matches!(field.typ.kind, IDLTypeKind::PrimT(PrimType::Null)) {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty(&field.typ))
    };
    docs.append(pp_label_raw(&field.label)).append(ty_doc)
}

fn pp_fields(fs: &[TypeField], is_variant: bool) -> RcDoc<'_> {
    let fields = fs.iter().map(|f| pp_field(f, is_variant));
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_opt(ty: &IDLType) -> RcDoc<'_> {
    kwd("opt").append(pp_ty(ty))
}

fn pp_vec(ty: &IDLType) -> RcDoc<'_> {
    if matches!(ty.kind, IDLTypeKind::PrimT(PrimType::Nat8)) {
        str("blob")
    } else {
        kwd("vec").append(pp_ty(ty))
    }
}

fn pp_record(fs: &[TypeField], is_tuple: bool) -> RcDoc<'_> {
    if is_tuple {
        let tuple = concat(fs.iter().map(|f| pp_ty(&f.typ)), ";");
        kwd("record").append(enclose_space("{", tuple, "}"))
    } else {
        kwd("record").append(pp_fields(fs, false))
    }
}

fn pp_variant(fs: &[TypeField]) -> RcDoc<'_> {
    kwd("variant").append(pp_fields(fs, true))
}

fn pp_function(func: &FuncType) -> RcDoc<'_> {
    kwd("func").append(pp_method(func))
}

fn pp_method(func: &FuncType) -> RcDoc<'_> {
    let args = pp_args(&func.args);
    let rets = pp_rets(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .append(RcDoc::space())
        .append(rets.append(modes))
        .nest(INDENT_SPACE)
}

fn pp_args(args: &[IDLType]) -> RcDoc<'_> {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("(", doc, ")")
}

fn pp_rets(rets: &[IDLType]) -> RcDoc<'_> {
    pp_args(rets)
}

fn pp_service(methods: &[Binding]) -> RcDoc<'_> {
    kwd("service").append(pp_service_methods(methods))
}

fn pp_service_methods(methods: &[Binding]) -> RcDoc<'_> {
    let methods = methods.iter().map(|b| {
        let docs = pp_docs(&b.docs);
        let func_doc = match &b.typ.kind {
            IDLTypeKind::FuncT(ref f) => pp_method(f),
            IDLTypeKind::VarT(_) => pp_ty(&b.typ),
            _ => unreachable!(),
        };
        docs.append(pp_text(&b.id))
            .append(kwd(" :"))
            .append(func_doc)
    });
    let doc = concat(methods, ";");
    enclose_space("{", doc, "}")
}

fn pp_class<'a>(args: &'a [IDLType], t: &'a IDLType) -> RcDoc<'a> {
    let doc = pp_args(args).append(" ->").append(RcDoc::space());
    match &t.kind {
        IDLTypeKind::ServT(ref serv) => doc.append(pp_service_methods(serv)),
        IDLTypeKind::VarT(ref s) => doc.append(s),
        _ => unreachable!(),
    }
}

fn pp_defs(prog: &IDLMergedProg) -> RcDoc<'_> {
    lines(prog.bindings().map(|b| {
        let docs = pp_docs(&b.docs);
        docs.append(kwd("type"))
            .append(ident(&b.id))
            .append(kwd("="))
            .append(pp_ty(&b.typ))
            .append(";")
    }))
}

fn pp_actor(actor: &IDLActorType) -> RcDoc<'_> {
    let docs = pp_docs(&actor.docs);
    let service_doc = match &actor.typ.kind {
        IDLTypeKind::ServT(ref serv) => pp_service_methods(serv),
        IDLTypeKind::VarT(_) | IDLTypeKind::ClassT(_, _) => pp_ty(&actor.typ),
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
