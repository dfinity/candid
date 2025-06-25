use proc_macro::TokenStream;
use syn::{parse_macro_input, Result};

mod derive;
mod func;

#[proc_macro_derive(CandidType, attributes(candid_path))]
pub fn derive_idl_type(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    let custom_candid_path_result = get_custom_candid_path(&input);

    match custom_candid_path_result {
        Ok(custom_candid_path) => derive::derive_idl_type(input, &custom_candid_path).into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro_attribute]
pub fn candid_method(attr: TokenStream, item: TokenStream) -> TokenStream {
    use syn::{parse::Parser, punctuated::Punctuated, Meta, Token};
    let attrs = match Punctuated::<Meta, Token![,]>::parse_terminated.parse(attr) {
        Ok(attrs) => attrs.into_iter().collect(),
        Err(e) => return e.to_compile_error().into(),
    };
    let fun = parse_macro_input!(item as syn::ItemFn);
    func::candid_method(attrs, fun).map_or_else(|e| e.to_compile_error().into(), Into::into)
}

#[proc_macro]
pub fn export_service(input: TokenStream) -> TokenStream {
    if input.is_empty() {
        func::export_service(None).into()
    } else {
        func::export_service(Some(input.into())).into()
    }
}

#[inline]
pub(crate) fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.as_bytes() {
        s = s.wrapping_mul(223).wrapping_add(*c as u32);
    }
    s
}

pub(crate) fn candid_path(
    custom_candid_path: &Option<proc_macro2::TokenStream>,
) -> proc_macro2::TokenStream {
    match custom_candid_path {
        Some(custom_candid_path_value) => custom_candid_path_value.clone(),
        None => quote::quote! { ::candid },
    }
}
pub(crate) fn get_lit_str(expr: &syn::Expr) -> std::result::Result<syn::LitStr, ()> {
    if let syn::Expr::Lit(expr) = expr {
        if let syn::Lit::Str(lit) = &expr.lit {
            return Ok(lit.clone());
        }
    }
    Err(())
}

pub(crate) fn get_doc_comment_lines(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|attr| match &attr.meta {
            syn::Meta::NameValue(m) if m.path.is_ident("doc") => {
                if let Ok(lit) = get_lit_str(&m.value) {
                    Some(lit.value().trim().to_string())
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect()
}

pub(crate) fn get_doc_comment_from_lines(comment_lines: &[String]) -> proc_macro2::TokenStream {
    let comment_strings: Vec<proc_macro2::TokenStream> = comment_lines
        .iter()
        .map(|s| quote::quote! { #s.to_string() })
        .collect();

    quote::quote! { vec![#(#comment_strings),*] }
}

fn get_custom_candid_path(input: &syn::DeriveInput) -> Result<Option<proc_macro2::TokenStream>> {
    let candid_path_helper_attribute_option = input
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident("candid_path"));

    match candid_path_helper_attribute_option {
        Some(candid_path_helper_attribute) => {
            let custom_candid_path_lit: syn::LitStr = candid_path_helper_attribute.parse_args()?;
            let custom_candid_token_stream: proc_macro2::TokenStream =
                custom_candid_path_lit.value().parse()?;

            Ok(Some(custom_candid_token_stream))
        }
        None => Ok(None),
    }
}
