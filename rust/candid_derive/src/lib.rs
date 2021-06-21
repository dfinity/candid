use proc_macro::TokenStream;
use syn::parse_macro_input;

mod derive;
mod func;

#[proc_macro_derive(CandidType, attributes(candid_path))]
pub fn derive_idl_type(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    let custom_candid_path = get_custom_candid_path(&input);

    derive::derive_idl_type(input, &custom_candid_path).into()
}

#[proc_macro_attribute]
pub fn candid_method(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attrs = parse_macro_input!(attr as syn::AttributeArgs);
    let fun = parse_macro_input!(item as syn::ItemFn);
    func::candid_method(attrs, fun).map_or_else(|e| e.to_compile_error().into(), Into::into)
}

#[proc_macro]
pub fn export_service(_: TokenStream) -> TokenStream {
    func::export_service().into()
}

#[inline]
pub(crate) fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.as_bytes().iter() {
        s = s.wrapping_mul(223).wrapping_add(*c as u32);
    }
    s
}

#[cfg(feature = "cdk")]
pub(crate) fn candid_path(custom_candid_path: &Option<proc_macro2::TokenStream>) -> proc_macro2::TokenStream {
    match custom_candid_path {
        Some(custom_candid_path_value) => custom_candid_path_value.clone(),
        None => quote::quote! { ::ic_cdk::export::candid }
    }
}

#[cfg(not(feature = "cdk"))]
pub(crate) fn candid_path(custom_candid_path: &Option<proc_macro2::TokenStream>) -> proc_macro2::TokenStream {
    match custom_candid_path {
        Some(custom_candid_path_value) => custom_candid_path_value.clone(),
        None => quote::quote! { ::candid }
    }
}

// TODO I am not sure I parsed this in the best way possible...any pointers would be great
fn get_custom_candid_path(input: &syn::DeriveInput) -> Option<proc_macro2::TokenStream> {
    let candid_path_helper_attribute = input.attrs.iter().find(|attr| {
        return attr.path.is_ident("candid_path");
    })?;

    let custom_candid_path_lit: syn::LitStr = candid_path_helper_attribute.parse_args().unwrap(); // TODO not sure how to handle the result
    let custom_candid_token_stream: proc_macro2::TokenStream = custom_candid_path_lit.value().parse().unwrap(); // TODO not sure how to handle the result

    Some(custom_candid_token_stream)
}