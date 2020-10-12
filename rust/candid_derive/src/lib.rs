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
    func::candid_method(attrs, fun).into()
}

#[proc_macro]
pub fn export_service(_: TokenStream) -> TokenStream {
    func::export_service().into()
}
