//! Language binding for generating Rust code from a Candid file.
//!
//! This generates a `pub trait Actor { ... }` code for the service (if there is one) and
//! a list of `pub type TypeX = ...` for each type declaration in a Candid file.
//!
//! The Actor name can be configured, as well as whether to use u128/i128 for
//! natural/integer numbers.
use crate::codegen::LanguageBinding;
use crate::error::{Error, Result};
use crate::parser::types::{Binding, Dec, FuncType, IDLType, Label, PrimType, TypeField};
use crate::{generate_code, IDLProg};

/// Returns true if id is a rust keyword.
fn is_keyword(id: &str) -> bool {
    let all_keywords = [
        "abstract", "as", "async", "await", "become", "box", "break", "const", "continue", "crate",
        "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "if", "impl", "in",
        "let", "loop", "macro", "match", "mod", "move", "mut", "override", "priv", "pub", "ref",
        "return", "self", "Self", "static", "struct", "super", "trait", "true", "try", "type",
        "typeof", "unsafe", "unsized", "use", "virtual", "where", "while", "yield",
    ];

    all_keywords.contains(&id)
}

#[derive(Clone, Default)]
pub struct Config {
    actor_name: Option<String>,
    bigint_type: Option<String>,
    biguint_type: Option<String>,
    derives: Option<String>,
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
    pub fn with_derives(mut self, derives: Vec<String>) -> Self {
        self.derives = Some(derives.join(" , "));
        self
    }
}

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
        let id = if is_keyword(id) {
            format!("r#{}", id)
        } else {
            id.to_string()
        };

        match ty {
            IDLType::PrimT(prim) => self.declare_prim(&id, prim),
            IDLType::VarT(var) => self.declare_var(&id, var),
            IDLType::FuncT(func) => self.declare_func(&id, func),
            IDLType::OptT(sub_t) => self.declare_opt(&id, sub_t.as_ref()),
            IDLType::VecT(item_t) => self.declare_vec(&id, item_t.as_ref()),
            IDLType::RecordT(fields) => self.declare_record(&id, fields),
            IDLType::VariantT(fields) => self.declare_variant(&id, fields),
            IDLType::ServT(serv_t) => self.declare_service(&id, serv_t),
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

                Ok(format!("pub {} : {} ,", field_name, usage))
            })
            .collect::<Result<Vec<String>>>()?
            .join(" ");

        let derives = self.config.derives.clone().unwrap_or("Clone".to_string());

        Ok(format!(
            "#[derive({})] pub struct {} {{ {} }}",
            derives, id, all_fields
        ))
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

    fn service_binding(&self, id: &str, func_t: &FuncType) -> Result<String> {
        let id = if is_keyword(id) {
            format!("r#{}", id)
        } else {
            id.to_string()
        };

        let return_type = if func_t.rets.is_empty() {
            "()".to_owned()
        } else {
            self.usage(&func_t.rets.first().unwrap())?
        };

        // Add Future binding.
        let return_type = if func_t.is_query() {
            return_type
        } else {
            format!("impl std::future::Future<Output = {}>", return_type)
        };

        let arguments = func_t
            .args
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let arg_name = format!("arg{}", i);
                let ty = self.usage(&ty)?;

                Ok(format!("{}: {}", arg_name, ty))
            })
            .collect::<Result<Vec<String>>>()?
            .join(" , ");

        Ok(format!(
            "fn {id}( {arguments} ) {return_type} ;",
            id = id,
            arguments = arguments,
            return_type = if return_type == "" {
                format!("")
            } else {
                format!(" -> {}", return_type)
            }
        ))
    }

    fn service(&self, bindings: &[Binding]) -> Result<String> {
        let all_functions = bindings
            .iter()
            .map(|Binding { id, typ }| match typ {
                IDLType::FuncT(func_t) => self.service_binding(id, func_t),
                _ => self.usage(typ),
            })
            .collect::<Result<Vec<String>>>()?;
        let actor_str = self
            .config
            .actor_name
            .clone()
            .unwrap_or_else(|| "Actor".to_string());

        Ok(format!(
            "pub trait {} {{ {} }}",
            actor_str,
            all_functions.join(" ")
        ))
    }
}

/// Takes an IDL string and returns a Rust string, formatted.
pub fn idl_to_rust(prog: &IDLProg, config: &Config) -> Result<String> {
    let binding = RustLanguageBinding {
        config,
        prog: &prog,
    };

    generate_code(&prog, binding)
}
