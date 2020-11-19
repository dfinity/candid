use super::candid_path;
use lazy_static::lazy_static;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use std::collections::BTreeMap;
use std::sync::Mutex;
use syn::{AttributeArgs, Error, ItemFn, Result, ReturnType, Signature, Type};

struct Method {
    args: Vec<String>,
    rets: Vec<String>,
    modes: String,
}

// There is no official way to communicate information across proc macro invocations.
// lazy_static works for now, but may get incomplete info with incremental compilation.
// See https://github.com/rust-lang/rust/issues/44034
// Hopefully, we can have an attribute on impl, then we don't need global state.
lazy_static! {
    static ref METHODS: Mutex<Option<BTreeMap<String, Method>>> =
        Mutex::new(Some(Default::default()));
}

pub(crate) fn candid_method(attrs: AttributeArgs, fun: ItemFn) -> Result<TokenStream> {
    let attrs = get_candid_attribute(&attrs)?;
    let sig = &fun.sig;
    if !sig.generics.params.is_empty() {
        return Err(Error::new_spanned(
            &sig.generics,
            "candid_method doesn't support generic parameters",
        ));
    }
    let ident = sig.ident.to_string();
    let name = attrs.rename.as_ref().unwrap_or(&ident).clone();
    let modes = attrs.method_type.unwrap_or_else(|| "update".to_string());
    let (args, rets) = get_args(sig)?;
    let args: Vec<String> = args
        .iter()
        .map(|t| format!("{}", t.to_token_stream()))
        .collect();
    let rets: Vec<String> = rets
        .iter()
        .map(|t| format!("{}", t.to_token_stream()))
        .collect();
    if modes == "oneway" && !rets.is_empty() {
        return Err(Error::new_spanned(
            &sig.output,
            "oneway function should have no return value",
        ));
    }
    if let Some(map) = METHODS.lock().unwrap().as_mut() {
        if map
            .insert(name.clone(), Method { args, rets, modes })
            .is_some()
        {
            return Err(Error::new_spanned(
                &sig.ident,
                format!("duplicate method name {}", name),
            ));
        }
    }
    Ok(quote! { #fun })
}

pub(crate) fn export_service() -> TokenStream {
    if let Some(meths) = METHODS.lock().unwrap().as_mut() {
        let candid = candid_path();
        let gen_tys = meths.iter().map(|(name, Method { args, rets, modes })| {
            let args = args
                .iter()
                .map(|t| generate_arg(quote! { args }, t))
                .collect::<Vec<_>>();
            let rets = rets
                .iter()
                .map(|t| generate_arg(quote! { rets }, t))
                .collect::<Vec<_>>();
            let modes = match modes.as_ref() {
                "query" => quote! { vec![#candid::parser::types::FuncMode::Query] },
                "oneway" => quote! { vec![#candid::parser::types::FuncMode::Oneway] },
                "update" => quote! { vec![] },
                _ => unreachable!(),
            };
            quote! {
                {
                    let mut args = Vec::new();
                    #(#args)*
                    let mut rets = Vec::new();
                    #(#rets)*
                    let func = Function { args, rets, modes: #modes };
                    service.push((#name.to_string(), Type::Func(func)));
                }
            }
        });
        let res = quote! {
            fn __export_service() -> String {
                use #candid::types::{CandidType, Function, Type};
                let mut service = Vec::<(String, Type)>::new();
                let mut env = #candid::types::internal::TypeContainer::new();
                #(#gen_tys)*
                service.sort_unstable_by_key(|(name, _)| #candid::idl_hash(name));
                let ty = Type::Service(service);
                let actor = Some(ty);
                let result = #candid::bindings::candid::compile(&env.env, &actor);
                format!("{}", result)
            }
        };
        meths.clear();
        //panic!(res.to_string());
        res
    } else {
        unreachable!()
    }
}

fn generate_arg(name: TokenStream, ty: &str) -> TokenStream {
    let ty = syn::parse_str::<Type>(ty).unwrap();
    quote! {
        #name.push(env.add::<#ty>());
    }
}

fn get_args(sig: &Signature) -> Result<(Vec<Type>, Vec<Type>)> {
    let mut args = Vec::new();
    for arg in &sig.inputs {
        match arg {
            syn::FnArg::Receiver(r) => {
                if r.reference.is_none() {
                    return Err(Error::new_spanned(arg, "only works for borrowed self"));
                }
            }
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
    Ok((args, rets))
}

struct CandidAttribute {
    rename: Option<String>,
    method_type: Option<String>,
}

fn get_candid_attribute(attrs: &[syn::NestedMeta]) -> Result<CandidAttribute> {
    use syn::Meta::{NameValue, Path};
    use syn::NestedMeta::Meta;
    let mut res = CandidAttribute {
        rename: None,
        method_type: None,
    };
    for attr in attrs.iter() {
        match &attr {
            Meta(NameValue(m)) if m.path.is_ident("rename") && res.rename.is_none() => {
                if let syn::Lit::Str(lit) = &m.lit {
                    res.rename = Some(lit.value());
                }
            }
            Meta(Path(p)) if res.method_type.is_none() => {
                let mode = p.get_ident().unwrap().to_string();
                match mode.as_ref() {
                    "query" | "update" | "oneway" => res.method_type = Some(mode),
                    _ => return Err(Error::new_spanned(p, "unknown mode")),
                }
            }
            _ => return Err(Error::new_spanned(attr, "unknown or conflicting attribute")),
        }
    }
    Ok(res)
}
