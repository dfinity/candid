use crate::get_lit_str;
use syn::Attribute;

pub(crate) fn extract_doc_comments(attrs: &[Attribute]) -> Vec<String> {
    let mut docs = Vec::new();
    for attr in attrs {
        if attr.path().is_ident("doc") {
            if let syn::Meta::NameValue(meta) = &attr.meta {
                if let Ok(lit) = get_lit_str(&meta.value) {
                    let doc_content = lit.value();
                    if !doc_content.is_empty() {
                        for line in doc_content.lines() {
                            docs.push(line.trim().to_string());
                        }
                    } else {
                        docs.push(String::new());
                    }
                }
            }
        }
    }
    docs
}
