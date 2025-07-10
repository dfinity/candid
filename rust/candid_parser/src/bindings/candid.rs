use candid::{
    pretty::{
        candid::{pp_args, pp_function, pp_label, pp_text},
        utils::{concat, enclose_space, ident, kwd, lines, str, LINE_WIDTH},
    },
    types::{
        syntax::{self, IDLActorType, IDLMergedProg, IDLType},
        ArgType, Field, Label, Type, TypeInner,
    },
    TypeEnv,
};
use pretty::RcDoc;

fn find_field<'a>(
    fields: Option<&'a [syntax::TypeField]>,
    label: &'a Label,
) -> (RcDoc<'a>, Option<&'a syntax::IDLType>) {
    let mut docs = RcDoc::nil();
    let mut syntax_field_ty = None;
    if let Some(bs) = fields {
        if let Some(field) = bs.iter().find(|b| b.label == *label) {
            docs = pp_docs(&field.docs);
            syntax_field_ty = Some(&field.typ);
        }
    };
    (docs, syntax_field_ty)
}

fn pp_ty_rich<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
            pp_record(ty, fields, Some(syntax_fields))
        }
        (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
            pp_variant(fields, Some(syntax_fields))
        }
        (TypeInner::Service(ref meths), Some(IDLType::ServT(methods))) => {
            pp_service(meths, Some(methods))
        }
        (TypeInner::Class(ref args, t), Some(IDLType::ClassT(_, syntax_t))) => {
            pp_class((args, t), Some(syntax_t))
        }
        (TypeInner::Opt(ref t), Some(IDLType::OptT(syntax_t))) => pp_opt(t, Some(syntax_t)),
        (TypeInner::Vec(ref t), Some(IDLType::VecT(syntax_t))) => pp_vec(t, Some(syntax_t)),
        (_, _) => pp_ty(ty),
    }
}

pub fn pp_ty(ty: &Type) -> RcDoc {
    use TypeInner::*;
    match ty.as_ref() {
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
        Opt(ref t) => pp_opt(t, None),
        Vec(ref t) => pp_vec(t, None),
        Record(ref fs) => pp_record(ty, fs, None),
        Variant(ref fs) => pp_variant(fs, None),
        Func(ref func) => kwd("func").append(pp_function(func)),
        Service(ref serv) => pp_service(serv, None),
        Class(ref args, ref t) => pp_class((args, t), None),
        Knot(ref id) => RcDoc::text(format!("{id}")),
        Unknown => str("unknown"),
        Future => str("future"),
    }
}

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    lines(docs.iter().map(|line| RcDoc::text("// ").append(line)))
}

fn pp_field<'a>(field: &'a Field, syntax: Option<&'a IDLType>, is_variant: bool) -> RcDoc<'a> {
    let ty_doc = if is_variant && *field.ty == TypeInner::Null {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty_rich(&field.ty, syntax))
    };
    pp_label(&field.id).append(ty_doc)
}

fn pp_fields<'a>(
    fs: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
    is_variant: bool,
) -> RcDoc<'a> {
    let fields = concat(
        fs.iter().map(|f| {
            let (docs, syntax_field_ty) = find_field(syntax, &f.id);
            docs.append(pp_field(f, syntax_field_ty, is_variant))
        }),
        ";",
    );
    enclose_space("{", fields, "}")
}

fn pp_opt<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    kwd("opt").append(pp_ty_rich(ty, syntax))
}

fn pp_vec<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    if matches!(ty.as_ref(), TypeInner::Nat8) {
        str("blob")
    } else {
        kwd("vec").append(pp_ty_rich(ty, syntax))
    }
}

fn pp_record<'a>(
    ty: &'a Type,
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
) -> RcDoc<'a> {
    if ty.is_tuple() {
        let tuple = concat(fields.iter().map(|f| pp_ty(&f.ty)), ";");
        kwd("record").append(enclose_space("{", tuple, "}"))
    } else {
        kwd("record").append(pp_fields(fields, syntax, false))
    }
}

fn pp_class<'a>((args, ty): (&'a [ArgType], &'a Type), syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    let doc = pp_args(args).append(" ->").append(RcDoc::space());
    match ty.as_ref() {
        TypeInner::Service(ref serv) => {
            if let Some(IDLType::ServT(ref fields)) = syntax {
                doc.append(pp_service_methods(serv, Some(fields)))
            } else {
                doc.append(pp_service_methods(serv, None))
            }
        }
        TypeInner::Var(ref s) => doc.append(s),
        _ => unreachable!(),
    }
}

fn pp_variant<'a>(fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    kwd("variant").append(pp_fields(fields, syntax, true))
}

fn pp_service<'a>(serv: &'a [(String, Type)], syntax: Option<&'a [syntax::Binding]>) -> RcDoc<'a> {
    kwd("service").append(pp_service_methods(serv, syntax))
}

fn pp_service_methods<'a>(
    serv: &'a [(String, Type)],
    syntax: Option<&'a [syntax::Binding]>,
) -> RcDoc<'a> {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let mut docs = RcDoc::nil();
            let mut syntax_field_ty = None;
            if let Some(bs) = syntax {
                if let Some(b) = bs.iter().find(|b| &b.id == id) {
                    docs = pp_docs(&b.docs);
                    syntax_field_ty = Some(&b.typ);
                }
            }
            let func_doc = match func.as_ref() {
                TypeInner::Func(ref f) => pp_function(f),
                TypeInner::Var(_) => pp_ty_rich(func, syntax_field_ty),
                _ => unreachable!(),
            };
            docs.append(pp_text(id)).append(kwd(" :")).append(func_doc)
        }),
        ";",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs<'a>(env: &'a TypeEnv, prog: &'a IDLMergedProg) -> RcDoc<'a> {
    lines(env.0.iter().map(|(id, ty)| {
        let syntax = prog.lookup(id);
        let docs = syntax
            .map(|b| pp_docs(b.docs.as_ref()))
            .unwrap_or(RcDoc::nil());
        docs.append(kwd("type"))
            .append(ident(id))
            .append(kwd("="))
            .append(pp_ty_rich(ty, syntax.map(|s| &s.typ)))
            .append(";")
    }))
}

fn pp_actor<'a>(ty: &'a Type, syntax: Option<&'a IDLActorType>) -> RcDoc<'a> {
    let service_doc = kwd("service :");
    match ty.as_ref() {
        TypeInner::Service(ref serv) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ServT(ref fields),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(service_doc)
                    .append(pp_service_methods(serv, Some(fields)))
            }
            _ => service_doc.append(pp_service_methods(serv, None)),
        },
        TypeInner::Class(ref args, ref t) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ClassT(_, syntax_t),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(service_doc)
                    .append(pp_class((args, t), Some(syntax_t)))
            }
            _ => service_doc.append(pp_class((args, t), None)),
        },
        TypeInner::Var(_) => service_doc.append(pp_ty(ty)),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, prog: &IDLMergedProg) -> String {
    let syntax_actor = prog.resolve_actor().ok().flatten();
    let doc = match actor {
        None => pp_defs(env, prog),
        Some(actor) => {
            let defs = pp_defs(env, prog);
            let actor = pp_actor(actor, syntax_actor.as_ref());
            let doc = defs.append(actor);
            doc
        }
    };
    doc.pretty(LINE_WIDTH).to_string()
}
