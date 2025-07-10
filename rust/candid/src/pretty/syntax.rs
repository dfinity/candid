use pretty::RcDoc;

use crate::{
    pretty::{
        candid::{pp_modes, pp_text},
        utils::{concat, enclose, enclose_space, ident, kwd, lines, str, INDENT_SPACE, LINE_WIDTH},
    },
    types::{
        syntax::{
            Binding, FuncType, IDLActorType, IDLArgType, IDLMergedProg, IDLType, PrimType,
            TypeField,
        },
        Label,
    },
};

fn pp_ty(ty: &IDLType) -> RcDoc {
    match ty {
        IDLType::PrimT(PrimType::Null) => str("null"),
        IDLType::PrimT(PrimType::Bool) => str("bool"),
        IDLType::PrimT(PrimType::Nat) => str("nat"),
        IDLType::PrimT(PrimType::Int) => str("int"),
        IDLType::PrimT(PrimType::Nat8) => str("nat8"),
        IDLType::PrimT(PrimType::Nat16) => str("nat16"),
        IDLType::PrimT(PrimType::Nat32) => str("nat32"),
        IDLType::PrimT(PrimType::Nat64) => str("nat64"),
        IDLType::PrimT(PrimType::Int8) => str("int8"),
        IDLType::PrimT(PrimType::Int16) => str("int16"),
        IDLType::PrimT(PrimType::Int32) => str("int32"),
        IDLType::PrimT(PrimType::Int64) => str("int64"),
        IDLType::PrimT(PrimType::Float32) => str("float32"),
        IDLType::PrimT(PrimType::Float64) => str("float64"),
        IDLType::PrimT(PrimType::Text) => str("text"),
        IDLType::PrimT(PrimType::Reserved) => str("reserved"),
        IDLType::PrimT(PrimType::Empty) => str("empty"),
        IDLType::VarT(ref s) => str(s),
        IDLType::PrincipalT => str("principal"),
        IDLType::OptT(ref t) => kwd("opt").append(pp_ty(t)),
        IDLType::VecT(ref t) if matches!(t.as_ref(), IDLType::PrimT(PrimType::Nat8)) => str("blob"),
        IDLType::VecT(ref t) => kwd("vec").append(pp_ty(t)),
        IDLType::RecordT(ref fs) => {
            if ty.is_tuple() {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.typ)), ";");
                kwd("record").append(enclose_space("{", tuple, "}"))
            } else {
                kwd("record").append(pp_fields(fs, false))
            }
        }
        IDLType::VariantT(ref fs) => kwd("variant").append(pp_fields(fs, true)),
        IDLType::FuncT(ref func) => kwd("func").append(pp_function(func)),
        IDLType::ServT(ref serv) => kwd("service").append(pp_service(serv)),
        IDLType::ClassT(ref args, ref t) => {
            let doc = pp_args(args).append(" ->").append(RcDoc::space());
            match t.as_ref() {
                IDLType::ServT(ref serv) => doc.append(pp_service(serv)),
                IDLType::VarT(ref s) => doc.append(s),
                _ => unreachable!(),
            }
        }
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(id) => pp_text(id),
        Label::Id(_) | Label::Unnamed(_) => RcDoc::as_string(id),
    }
}

fn pp_field(field: &TypeField, is_variant: bool) -> RcDoc {
    let docs = pp_docs(&field.docs);
    let ty_doc = if is_variant && field.typ == IDLType::PrimT(PrimType::Null) {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty(&field.typ))
    };
    docs.append(pp_label(&field.label)).append(ty_doc)
}

fn pp_fields(fs: &[TypeField], is_variant: bool) -> RcDoc {
    let fields = fs.iter().map(|f| pp_field(f, is_variant));
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_function(func: &FuncType) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_rets(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .append(RcDoc::space())
        .append(rets.append(modes))
        .nest(INDENT_SPACE)
}

fn pp_args(args: &[IDLArgType]) -> RcDoc {
    let args = args.iter().map(|arg| {
        if let Some(name) = &arg.name {
            pp_text(name).append(kwd(" :")).append(pp_ty(&arg.typ))
        } else {
            pp_ty(&arg.typ)
        }
    });
    let doc = concat(args, ",");
    enclose("(", doc, ")")
}

fn pp_rets(rets: &[IDLType]) -> RcDoc {
    let doc = concat(rets.iter().map(pp_ty), ",");
    enclose("(", doc, ")")
}

fn pp_service(methods: &[Binding]) -> RcDoc {
    let methods = methods.iter().map(|b| {
        let docs = pp_docs(&b.docs);
        let func_doc = match b.typ {
            IDLType::FuncT(ref f) => pp_function(f),
            IDLType::VarT(_) => pp_ty(&b.typ),
            _ => unreachable!(),
        };
        docs.append(pp_text(&b.id))
            .append(kwd(" :"))
            .append(func_doc)
    });
    let doc = concat(methods, ";");
    enclose_space("{", doc, "}")
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

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    lines(docs.iter().map(|line| RcDoc::text("// ").append(line)))
}

fn pp_actor(actor: &IDLActorType) -> RcDoc {
    let docs = pp_docs(&actor.docs);
    let service_doc = match actor.typ {
        IDLType::ServT(ref serv) => pp_service(serv),
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
