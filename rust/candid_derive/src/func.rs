use lazy_static::lazy_static;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;
use std::sync::Mutex;
use syn::{AttributeArgs, ItemFn, ReturnType, Signature, Type};

struct Method {
    args: Vec<String>,
    rets: Vec<String>,
    modes: String,
}

lazy_static! {
    static ref METHODS: Mutex<Option<BTreeMap<String, Method>>> =
        Mutex::new(Some(Default::default()));
}

pub(crate) fn candid_method(attrs: AttributeArgs, fun: ItemFn) -> TokenStream {
    use quote::ToTokens;
    let attrs = get_candid_attribute(&attrs);
    let sig = &fun.sig;
    if !sig.generics.params.is_empty() {
        unimplemented!("doesn't support generic parameters");
    }
    let ident = sig.ident.to_string();
    let name = attrs.rename.as_ref().unwrap_or_else(|| &ident).clone();
    let modes = attrs.method_type;
    let (args, rets) = get_args(sig);
    let args = args
        .iter()
        .map(|t| format!("{}", t.to_token_stream()))
        .collect();
    let rets = rets
        .iter()
        .map(|t| format!("{}", t.to_token_stream()))
        .collect();
    if let Some(map) = METHODS.lock().unwrap().as_mut() {
        map.insert(name, Method { args, rets, modes });
    }
    quote! { #fun }
}

pub(crate) fn export_service() -> TokenStream {
    let methods = METHODS.lock().unwrap().take();
    if let Some(meths) = methods {
        let gen_tys = meths.iter().map(|(name, Method { args, rets, modes })| {
            let args = args
                .iter()
                .map(|t| syn::parse_str::<Type>(t).unwrap())
                .collect::<Vec<_>>();
            let rets = rets
                .iter()
                .map(|t| syn::parse_str::<Type>(t).unwrap())
                .collect::<Vec<_>>();
            let modes = match modes.as_ref() {
                "query" => quote! { vec![::candid::parser::types::FuncMode::Query] },
                _ => quote! { vec![] },
            };
            quote! {
                {
                    let mut args = Vec::new();
                    #(args.push(<#args as ::candid::types::CandidType>::ty());)*
                    let mut rets = Vec::new();
                    #(rets.push(<#rets as ::candid::types::CandidType>::ty());)*
                    let func = ::candid::types::Function { args, rets, modes: #modes };
                    service.push((#name.to_string(), ::candid::types::Type::Func(func)));
                }
            }
        });
        let res = quote! {
            fn export_service() -> String {
                let mut service = Vec::new();
                #(#gen_tys)*
                let ty = ::candid::types::Type::Service(service);
                let env = ::candid::TypeEnv::new();
                let actor = Some(ty);
                let result = ::candid::bindings::candid::compile(&env, &actor);
                format!("{}", result)
            }
        };
        //panic!(res.to_string());
        res
    } else {
        panic!("export_service! called more than once")
    }
}

fn get_args(sig: &Signature) -> (Vec<Type>, Vec<Type>) {
    let mut args = Vec::new();
    for arg in &sig.inputs {
        match arg {
            syn::FnArg::Receiver(_) => unimplemented!("self function"),
            syn::FnArg::Typed(syn::PatType { ty, .. }) => args.push(ty.as_ref().clone()),
        }
    }
    let rets = match &sig.output {
        ReturnType::Default => Vec::new(),
        ReturnType::Type(_, ty) => match ty.as_ref() {
            Type::Tuple(tuple) => tuple.elems.iter().cloned().collect(),
            _ => vec![ty.as_ref().clone()],
        },
    };
    (args, rets)
}

struct CandidAttribute {
    rename: Option<String>,
    method_type: String,
}

fn get_candid_attribute(attrs: &[syn::NestedMeta]) -> CandidAttribute {
    use syn::Meta::{NameValue, Path};
    use syn::NestedMeta::Meta;
    let mut res = CandidAttribute {
        rename: None,
        method_type: "update".to_string(),
    };
    for attr in attrs.iter() {
        match &attr {
            Meta(NameValue(m)) if m.path.is_ident("rename") => {
                if let syn::Lit::Str(lit) = &m.lit {
                    res.rename = Some(lit.value());
                }
            }
            Meta(Path(p)) if p.get_ident().is_some() => {
                res.method_type = p.get_ident().unwrap().to_string();
            }
            _ => unimplemented!("unknown attr"),
        }
    }
    res
}
