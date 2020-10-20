use proc_macro::TokenStream;
use syn::parse_macro_input;

mod derive;
mod func;

#[proc_macro_derive(CandidType)]
pub fn derive_idl_type(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);
    derive::derive_idl_type(input).into()
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
pub(crate) fn candid_path() -> proc_macro2::TokenStream {
    quote::quote! { ::ic_cdk::export::candid }
}

#[cfg(not(feature = "cdk"))]
pub(crate) fn candid_path() -> proc_macro2::TokenStream {
    quote::quote! { ::candid }
}
