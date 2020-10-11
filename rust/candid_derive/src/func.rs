use proc_macro2::TokenStream;
use quote::quote;
use syn::{AttributeArgs, ItemFn};

pub(crate) fn candid_type(attrs: AttributeArgs, fun: ItemFn) -> TokenStream {
    let _attrs = get_candid_attribute(&attrs);
    let signature = &fun.sig;
    if !signature.generics.params.is_empty() {
        unimplemented!("doesn't support generic parameters");
    }

    let gen = quote! {};
    gen
}

struct CandidAttribute {
    rename: Option<String>,
    method_type: &'static str,
}

fn get_candid_attribute(attrs: &[syn::NestedMeta]) -> CandidAttribute {
    use syn::Meta::{List, NameValue};
    use syn::NestedMeta::Meta;
    let mut res = CandidAttribute {
        rename: None,
        method_type: "update",
    };
    for attr in attrs.iter() {
        match &attr {
            Meta(NameValue(m)) if m.path.is_ident("rename") => {
                if let syn::Lit::Str(lit) = &m.lit {
                    res.rename = Some(lit.value());
                }
            }
            Meta(List(metas)) if metas.path.is_ident("query") => res.method_type = "query",
            _ => unimplemented!("unknown attr"),
        }
    }
    res
}
