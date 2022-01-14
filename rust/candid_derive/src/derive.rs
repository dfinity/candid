use super::{candid_path, idl_hash};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeSet;
use syn::ext::IdentExt;
use syn::punctuated::Punctuated;
use syn::{Data, DeriveInput, GenericParam, Generics, Token};

pub(crate) fn derive_idl_type(
    input: DeriveInput,
    custom_candid_path: &Option<TokenStream>,
) -> TokenStream {
    let candid = candid_path(custom_candid_path);
    let name = input.ident;
    let generics = add_trait_bounds(input.generics, custom_candid_path);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let (ty_body, ser_body) = match input.data {
        Data::Enum(ref data) => enum_from_ast(&name, &data.variants, custom_candid_path),
        Data::Struct(ref data) => {
            let (ty, idents, is_bytes) = struct_from_ast(&data.fields, custom_candid_path);
            (ty, serialize_struct(&idents, &is_bytes, custom_candid_path))
        }
        Data::Union(_) => unimplemented!("doesn't derive union type"),
    };
    let gen = quote! {
        impl #impl_generics #candid::types::CandidType for #name #ty_generics #where_clause {
            fn _ty() -> #candid::types::Type {
                #ty_body
            }
            fn id() -> #candid::types::TypeId { #candid::types::TypeId::of::<#name #ty_generics>() }

            fn idl_serialize<__S>(&self, __serializer: __S) -> ::std::result::Result<(), __S::Error>
                where
                __S: #candid::types::Serializer,
                {
                    #ser_body
                }
        }
    };
    //panic!(gen.to_string());
    gen
}

struct Variant {
    real_ident: syn::Ident,
    renamed_ident: syn::Ident,
    hash: u32,
    ty: TokenStream,
    members: Vec<Ident>,
    with_bytes: bool,
}
enum Style {
    Struct,
    Tuple,
    Unit,
}
impl Variant {
    fn style(&self) -> Style {
        if self.members.is_empty() {
            return Style::Unit;
        };
        match self.members[0] {
            Ident::Named(_) => Style::Struct,
            Ident::Unnamed(_) => Style::Tuple,
        }
    }
    fn to_pattern(&self) -> (TokenStream, Vec<TokenStream>) {
        match self.style() {
            Style::Unit => (quote! {}, Vec::new()),
            Style::Struct => {
                let id: Vec<_> = self.members.iter().map(|ident| ident.to_token()).collect();
                (
                    quote! {
                        {#(ref #id),*}
                    },
                    id,
                )
            }
            Style::Tuple => {
                let id: Vec<_> = self
                    .members
                    .iter()
                    .map(|ident| {
                        let ident = ident.to_string();
                        let var = format!("__field{}", ident);
                        syn::parse_str(&var).unwrap()
                    })
                    .collect();
                (
                    quote! {
                        (#(ref #id),*)
                    },
                    id,
                )
            }
        }
    }
}

fn enum_from_ast(
    name: &syn::Ident,
    variants: &Punctuated<syn::Variant, Token![,]>,
    custom_candid_path: &Option<TokenStream>,
) -> (TokenStream, TokenStream) {
    let mut fs: Vec<_> = variants
        .iter()
        .map(|variant| {
            let id = variant.ident.clone();
            let attrs = get_attrs(&variant.attrs);
            let (renamed_ident, hash) = match attrs.rename {
                Some(ref rename) => (
                    proc_macro2::Ident::new(rename, proc_macro2::Span::call_site()),
                    idl_hash(rename),
                ),
                None => (id.clone(), idl_hash(&id.unraw().to_string())),
            };
            let (ty, idents, _) = struct_from_ast(&variant.fields, custom_candid_path);
            Variant {
                real_ident: id,
                renamed_ident,
                hash,
                ty,
                members: idents,
                with_bytes: attrs.with_bytes,
            }
        })
        .collect();
    let unique: BTreeSet<_> = fs.iter().map(|Variant { hash, .. }| hash).collect();
    assert_eq!(unique.len(), fs.len());
    fs.sort_unstable_by_key(|Variant { hash, .. }| *hash);

    let id = fs
        .iter()
        .map(|Variant { renamed_ident, .. }| renamed_ident.unraw().to_string());
    let ty = fs.iter().map(|Variant { ty, .. }| ty);
    let candid = candid_path(custom_candid_path);
    let ty_gen = quote! {
        #candid::types::Type::Variant(
            vec![
                #(#candid::types::Field {
                    id: #candid::types::Label::Named(#id.to_owned()),
                    ty: #ty }
                ),*
            ]
        )
    };

    let id = fs.iter().map(|Variant { real_ident, .. }| {
        syn::parse_str::<TokenStream>(&format!("{}::{}", name, real_ident)).unwrap()
    });
    let index = 0..fs.len() as u64;
    let (pattern, members): (Vec<_>, Vec<_>) = fs
        .iter()
        .map(|f| {
            let (pattern, id) = f.to_pattern();
            (
                pattern,
                if f.with_bytes {
                    quote! {
                        #(#candid::types::Compound::serialize_blob(&mut ser, #id.as_ref())?;)*
                    }
                } else {
                    quote! {
                        #(#candid::types::Compound::serialize_element(&mut ser, #id)?;)*
                    }
                },
            )
        })
        .unzip();
    let variant_gen = quote! {
        match *self {
            #(#id #pattern => {
                let mut ser = __serializer.serialize_variant(#index)?;
                #members
            }),*
        };
        Ok(())
    };
    (ty_gen, variant_gen)
}

fn serialize_struct(
    idents: &[Ident],
    is_bytes: &[bool],
    custom_candid_path: &Option<TokenStream>,
) -> TokenStream {
    let candid = candid_path(custom_candid_path);
    let id = idents.iter().map(|ident| ident.to_token());
    let ser_elem = id.zip(is_bytes.iter()).map(|(id, is_bytes)| {
        if *is_bytes {
            quote! { #candid::types::Compound::serialize_blob(&mut ser, self.#id.as_ref())?; }
        } else {
            quote! { #candid::types::Compound::serialize_element(&mut ser, &self.#id)?; }
        }
    });
    quote! {
        let mut ser = __serializer.serialize_struct()?;
        #(#ser_elem)*
        Ok(())
    }
}

fn struct_from_ast(
    fields: &syn::Fields,
    custom_candid_path: &Option<TokenStream>,
) -> (TokenStream, Vec<Ident>, Vec<bool>) {
    let candid = candid_path(custom_candid_path);
    match *fields {
        syn::Fields::Named(ref fields) => {
            let (fs, idents, is_bytes) = fields_from_ast(&fields.named, custom_candid_path);
            (
                quote! { #candid::types::Type::Record(#fs) },
                idents,
                is_bytes,
            )
        }
        syn::Fields::Unnamed(ref fields) => {
            let (fs, idents, is_bytes) = fields_from_ast(&fields.unnamed, custom_candid_path);
            if idents.len() == 1 {
                let newtype = derive_type(&fields.unnamed[0].ty, custom_candid_path);
                (quote! { #newtype }, idents, is_bytes)
            } else {
                (
                    quote! { #candid::types::Type::Record(#fs) },
                    idents,
                    is_bytes,
                )
            }
        }
        syn::Fields::Unit => (
            quote! { #candid::types::Type::Null },
            Vec::new(),
            Vec::new(),
        ),
    }
}

#[derive(Clone)]
enum Ident {
    Named(syn::Ident),
    Unnamed(u32),
}
impl Ident {
    fn to_token(&self) -> TokenStream {
        match self {
            Ident::Named(ident) => quote! { #ident },
            Ident::Unnamed(ref i) => syn::parse_str::<TokenStream>(&format!("{}", i)).unwrap(),
        }
    }
}
impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Ident::Named(ref ident) => f.write_fmt(format_args!("{}", ident)),
            Ident::Unnamed(ref i) => f.write_fmt(format_args!("{}", *i)),
        }
    }
}

struct Field {
    real_ident: Ident,
    renamed_ident: Ident,
    hash: u32,
    ty: TokenStream,
    with_bytes: bool,
}

fn get_serde_meta_items(attr: &syn::Attribute) -> Result<Vec<syn::NestedMeta>, ()> {
    if !attr.path.is_ident("serde") {
        return Ok(Vec::new());
    }
    match attr.parse_meta() {
        Ok(syn::Meta::List(meta)) => Ok(meta.nested.into_iter().collect()),
        _ => Err(()),
    }
}

struct Attributes {
    rename: Option<String>,
    with_bytes: bool,
}

fn get_attrs(attrs: &[syn::Attribute]) -> Attributes {
    use syn::Meta::{List, NameValue};
    use syn::NestedMeta::Meta;
    let mut res = Attributes {
        rename: None,
        with_bytes: false,
    };
    for item in attrs.iter().flat_map(get_serde_meta_items).flatten() {
        match &item {
            // #[serde(rename = "foo")]
            Meta(NameValue(m)) if m.path.is_ident("rename") => {
                if let syn::Lit::Str(lit) = &m.lit {
                    res.rename = Some(lit.value());
                }
            }
            // #[serde(rename(serialize = "foo"))]
            Meta(List(metas)) if metas.path.is_ident("rename") => {
                for item in metas.nested.iter() {
                    match item {
                        Meta(NameValue(m)) if m.path.is_ident("serialize") => {
                            if let syn::Lit::Str(lit) = &m.lit {
                                res.rename = Some(lit.value());
                            }
                        }
                        _ => continue,
                    }
                }
            }
            // #[serde(with = "serde_bytes")]
            Meta(NameValue(m)) if m.path.is_ident("with") => {
                if let syn::Lit::Str(lit) = &m.lit {
                    if lit.value() == "serde_bytes" {
                        res.with_bytes = true;
                    }
                }
            }
            _ => continue,
        }
    }
    res
}

fn fields_from_ast(
    fields: &Punctuated<syn::Field, syn::Token![,]>,
    custom_candid_path: &Option<TokenStream>,
) -> (TokenStream, Vec<Ident>, Vec<bool>) {
    let candid = candid_path(custom_candid_path);
    let mut fs: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let attrs = get_attrs(&field.attrs);
            let (real_ident, renamed_ident, hash) = match field.ident {
                Some(ref ident) => {
                    let real_ident = Ident::Named(ident.clone());
                    match attrs.rename {
                        Some(ref renamed) => {
                            let ident =
                                proc_macro2::Ident::new(renamed, proc_macro2::Span::call_site());
                            let renamed_ident = Ident::Named(ident);
                            (real_ident, renamed_ident, idl_hash(renamed))
                        }
                        None => (
                            real_ident.clone(),
                            real_ident,
                            idl_hash(&ident.unraw().to_string()),
                        ),
                    }
                }
                None => (Ident::Unnamed(i as u32), Ident::Unnamed(i as u32), i as u32),
            };
            Field {
                real_ident,
                renamed_ident,
                hash,
                ty: derive_type(&field.ty, custom_candid_path),
                with_bytes: attrs.with_bytes,
            }
        })
        .collect();
    let unique: BTreeSet<_> = fs.iter().map(|Field { hash, .. }| hash).collect();
    assert_eq!(unique.len(), fs.len());
    fs.sort_unstable_by_key(|Field { hash, .. }| *hash);

    let id = fs
        .iter()
        .map(|Field { renamed_ident, .. }| match renamed_ident {
            Ident::Named(ref id) => {
                let name = id.unraw().to_string();
                quote! { #candid::types::Label::Named(#name.to_string()) }
            }
            Ident::Unnamed(ref i) => quote! { #candid::types::Label::Id(#i) },
        });
    let ty = fs.iter().map(|Field { ty, .. }| ty);
    let ty_gen = quote! {
        vec![
            #(#candid::types::Field {
                id: #id,
                ty: #ty }
            ),*
        ]
    };
    let idents: Vec<Ident> = fs
        .iter()
        .map(|Field { real_ident, .. }| real_ident.clone())
        .collect();
    let is_bytes: Vec<_> = fs.iter().map(|f| f.with_bytes).collect();
    (ty_gen, idents, is_bytes)
}

fn derive_type(t: &syn::Type, custom_candid_path: &Option<TokenStream>) -> TokenStream {
    let candid = candid_path(custom_candid_path);
    quote! {
        <#t as #candid::types::CandidType>::ty()
    }
}

fn add_trait_bounds(mut generics: Generics, custom_candid_path: &Option<TokenStream>) -> Generics {
    for param in &mut generics.params {
        let candid = candid_path(custom_candid_path);
        if let GenericParam::Type(ref mut type_param) = *param {
            let bound = syn::parse_quote! { #candid::types::CandidType };
            type_param.bounds.push(bound);
        }
    }
    generics
}
