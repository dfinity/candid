//! Language binding for generating Rust code from a Candid file.
//!
//! This generates a `pub trait Actor { ... }` code for the service (if there is one) and
//! a list of `pub type TypeX = ...` for each type declaration in a Candid file.
//!
//! The Actor name can be configured, as well as whether to use u128/i128 for
//! natural/integer numbers.
use crate::codegen::LanguageBinding;
use crate::error::{Error, Result};
use crate::parser::types::{Binding, Dec, FuncType, IDLType, PrimType, TypeField};
use crate::types::Label;
use crate::{generate_code, idl_hash, IDLProg};

/// Returns true if id is a rust keyword.
pub fn is_keyword(id: &str) -> bool {
    let all_keywords = [
        "abstract", "as", "async", "await", "become", "box", "break", "const", "continue", "crate",
        "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "if", "impl", "in",
        "let", "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub", "ref",
        "return", "self", "Self", "static", "struct", "super", "trait", "true", "try", "type",
        "typeof", "unsafe", "unsized", "use", "virtual", "where", "while", "yield",
    ];

    all_keywords.contains(&id)
}

/// Transforms a Candid ID into a valid Rust ID (as a string).
/// In case a string cannot be used as an ID in Rust, this will replace it with a
/// IDL Hash value of the ID, surrounged by `_` (e.g. `_12345_`).
/// If the string is a valid Rust
pub fn candid_id_to_rust(id: &str) -> String {
    // If the id is not representable in a Rust-compatible string
    if id.starts_with(|c: char| !c.is_ascii_alphabetic() && c != '_')
        || id.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
    {
        format!("_{}_", idl_hash(id))
    } else if is_keyword(id) {
        format!("r#{}", id)
    } else {
        id.to_string()
    }
}

/// Allow extra bindings to be passed in for Rust generation. This is higher level
/// bindings than languages ones.
///
/// The default implementation provided maps to a trait definition where functions are
/// empty and return Future<Output = ...> if necessary.
pub trait RustBindings {
    fn actor(&self, name: &str, all_functions: &[String]) -> Result<String> {
        // Make sure name is not a rust keyword.
        let name = if is_keyword(name) {
            format!("r#{}", name)
        } else {
            name.to_string()
        };

        let mut all_functions_str = String::new();
        for f in all_functions {
            all_functions_str += f;
        }

        Ok(format!("pub trait {} {{ {} }}", name, all_functions_str))
    }

    fn actor_function_body(
        &self,
        _name: &str,
        _arguments: &[(String, String)],
        _return_type: &str,
        _is_query: bool,
    ) -> Result<String> {
        Ok(";".to_string())
    }

    fn actor_function(
        &self,
        name: &str,
        arguments: &[(String, String)],
        returns: &[String],
        is_query: bool,
    ) -> Result<String> {
        let id = candid_id_to_rust(name);

        // Add Future binding.
        let return_type = if returns.is_empty() {
            "".to_string()
        } else if returns.len() == 1 {
            returns[0].to_string()
        } else {
            format!("( {} )", returns.join(" , "))
        };

        let return_type = if is_query {
            return_type
        } else {
            format!(
                "std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = {}>>>",
                if return_type.is_empty() {
                    "()"
                } else {
                    &return_type
                }
            )
        };

        let arguments_list = arguments
            .iter()
            .map(|(name, ty)| format!("{} : {}", name, ty))
            .collect::<Vec<String>>()
            .join(" , ");

        let body = self.actor_function_body(name, arguments, &return_type, is_query)?;

        Ok(format!(
            "fn {id}( {arguments} ) {return_type} {body}",
            id = id,
            arguments = arguments_list,
            body = body,
            return_type = if return_type.is_empty() {
                String::new()
            } else {
                format!(" -> {}", return_type)
            }
        ))
    }

    fn record(&self, id: &str, fields: &[(String, String)]) -> Result<String> {
        let all_fields = fields
            .iter()
            .map(|(name, ty)| format!("pub {} : {}", name, ty))
            .collect::<Vec<String>>()
            .join(" , ");
        Ok(format!(
            "#[derive(Clone)] pub struct {} {{ {} }}",
            id, all_fields
        ))
    }
}

pub struct Config {
    actor_name: Option<String>,
    bigint_type: Option<String>,
    biguint_type: Option<String>,
    bindings: Box<dyn RustBindings>,
}

impl Default for Config {
    fn default() -> Self {
        #[derive(Clone)]
        struct RustDefaultBinding {}
        impl RustBindings for RustDefaultBinding {}
        Self {
            actor_name: None,
            bigint_type: None,
            biguint_type: None,
            bindings: Box::new(RustDefaultBinding {}),
        }
    }
}

impl Config {
    pub fn with_actor_name(mut self, name: String) -> Self {
        self.actor_name = Some(name);
        self
    }
    pub fn with_bigint_type(mut self, typename: String) -> Self {
        self.bigint_type = Some(typename);
        self
    }
    pub fn with_biguint_type(mut self, typename: String) -> Self {
        self.biguint_type = Some(typename);
        self
    }
    pub fn with_bindings(mut self, bindings: Box<dyn RustBindings>) -> Self {
        self.bindings = bindings;
        self
    }
}

/// The codegen binding for Rust. This is not made public.
struct RustLanguageBinding<'a> {
    config: &'a Config,
    prog: &'a IDLProg,
}

impl<'a> LanguageBinding for RustLanguageBinding<'a> {
    fn usage_prim(&self, ty: &PrimType) -> Result<String> {
        Ok(match ty {
            PrimType::Nat => {
                if let Some(biguint_type) = self.config.biguint_type.as_ref() {
                    biguint_type
                } else {
                    "u128"
                }
            }
            PrimType::Nat8 => "u8",
            PrimType::Nat16 => "u16",
            PrimType::Nat32 => "u32",
            PrimType::Nat64 => "u64",
            PrimType::Int => {
                if let Some(bigint_type) = self.config.bigint_type.as_ref() {
                    bigint_type
                } else {
                    "i128"
                }
            }
            PrimType::Int8 => "i8",
            PrimType::Int16 => "i16",
            PrimType::Int32 => "i32",
            PrimType::Int64 => "i64",
            PrimType::Float32 => "f32",
            PrimType::Float64 => "f64",
            PrimType::Bool => "bool",
            PrimType::Text => "String",
            PrimType::Null => "()",
            PrimType::Empty => "!",

            PrimType::Reserved => {
                return Err(Error::msg("Unsupported PrimType: Reserved".to_string()));
            }
        }
        .to_string())
    }

    fn usage_var(&self, var: &str) -> Result<String> {
        Ok(self
            .prog
            .decs
            .iter()
            .find_map(|d| match d {
                Dec::TypD(Binding {
                    id,
                    typ: IDLType::RecordT(_),
                }) => {
                    if id == var {
                        Some(format!("Box<{}>", var))
                    } else {
                        None
                    }
                }
                _ => Some(var.to_string()),
            })
            .unwrap())
    }

    fn usage_func(&self, _func: &FuncType) -> Result<String> {
        unimplemented!()
    }

    fn usage_opt(&self, ty: &IDLType) -> Result<String> {
        Ok(format!("Option<{}>", self.usage(ty)?))
    }

    fn usage_vec(&self, ty: &IDLType) -> Result<String> {
        Ok(format!("Vec<{}>", self.usage(ty)?))
    }

    fn usage_record(&self, _fields: &[TypeField]) -> Result<String> {
        unimplemented!()
    }

    fn usage_variant(&self, _fields: &[TypeField]) -> Result<String> {
        unimplemented!()
    }

    fn usage_service(&self, _ty: &[Binding]) -> Result<String> {
        unimplemented!()
    }

    fn declare(&self, id: &str, ty: &IDLType) -> Result<String> {
        match ty {
            IDLType::PrimT(prim) => self.declare_prim(id, prim),
            IDLType::VarT(var) => self.declare_var(id, var),
            IDLType::FuncT(func) => self.declare_func(id, func),
            IDLType::OptT(sub_t) => self.declare_opt(id, sub_t.as_ref()),
            IDLType::VecT(item_t) => self.declare_vec(id, item_t.as_ref()),
            IDLType::RecordT(fields) => self.declare_record(id, fields),
            IDLType::VariantT(fields) => self.declare_variant(id, fields),
            IDLType::ServT(serv_t) => self.declare_service(id, serv_t),
            IDLType::ClassT(_, _) => unreachable!(),
            IDLType::PrincipalT => self.declare_var(id, "principal"),
        }
    }
    fn declare_prim(&self, id: &str, ty: &PrimType) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_prim(ty)?))
    }
    fn declare_var(&self, id: &str, var: &str) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_var(var)?))
    }
    fn declare_func(&self, id: &str, func: &FuncType) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_func(func)?))
    }
    fn declare_opt(&self, id: &str, ty: &IDLType) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_opt(ty)?))
    }
    fn declare_vec(&self, id: &str, ty: &IDLType) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_vec(ty)?))
    }
    fn declare_record(&self, id: &str, fields: &[TypeField]) -> Result<String> {
        let all_fields = fields
            .iter()
            .map(|TypeField { label, typ }| {
                let field_name = match label {
                    Label::Id(i) => format!("id_{}", i),
                    Label::Unnamed(i) => format!("id_{}", i),
                    Label::Named(i) => i.clone(),
                };
                let usage = self.usage(typ)?;

                Ok((field_name, usage))
            })
            .collect::<Result<Vec<(String, String)>>>()?;

        self.config.bindings.record(id, &all_fields)
    }
    fn declare_variant(&self, id: &str, fields: &[TypeField]) -> Result<String> {
        Ok(format!(
            "pub type {} = {};",
            id,
            self.usage_variant(fields)?
        ))
    }
    fn declare_service(&self, id: &str, ty: &[Binding]) -> Result<String> {
        Ok(format!("pub type {} = {};", id, self.usage_service(ty)?))
    }

    fn declaration_binding(&self, binding: &Binding) -> Result<String> {
        self.declare(&binding.id, &binding.typ)
    }

    fn service_binding(&self, _id: &str, _func_t: &FuncType) -> Result<String> {
        unreachable!()
    }

    fn service(&self, bindings: &[Binding]) -> Result<String> {
        let actor_str = self
            .config
            .actor_name
            .clone()
            .unwrap_or_else(|| "Actor".to_string());

        let all_functions = bindings
            .iter()
            .map(|Binding { id, typ }| match typ {
                IDLType::FuncT(func_t) => {
                    let return_type = func_t
                        .rets
                        .iter()
                        .map(|r| self.usage(r))
                        .collect::<Result<Vec<String>>>()?;

                    let arguments = func_t
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            let arg_name = format!("arg{}", i);
                            let ty = self.usage(ty)?;

                            Ok((arg_name, ty))
                        })
                        .collect::<Result<Vec<(String, String)>>>()?;

                    self.config.bindings.actor_function(
                        id,
                        &arguments,
                        &return_type,
                        func_t.is_query(),
                    )
                }
                _ => self.usage(typ),
            })
            .collect::<Result<Vec<String>>>()?;

        self.config.bindings.actor(&actor_str, &all_functions)
    }
}

/// Takes an IDL string and returns a Rust string, unformatted.
pub fn idl_to_rust(prog: &IDLProg, config: &Config) -> Result<String> {
    let binding = RustLanguageBinding { config, prog };

    generate_code(prog, binding)
}
