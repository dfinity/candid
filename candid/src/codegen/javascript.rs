use crate::codegen::LanguageBinding;
use crate::error::{Error, Result};
use crate::parser::types::{Binding, Dec, FuncMode, FuncType, IDLType, Label, PrimType, TypeField};
use crate::{generate_code, idl_hash, IDLProg};

/// Transforms a Candid ID into a valid JavaScript ID (as a string).
/// In case a string cannot be used as an ID in Rust, this will replace it with a
/// IDL Hash value of the ID, surrounged by `_` (e.g. `_12345_`).
/// If the string is a valid Rust
pub fn candid_id_to_javascript(id: &str) -> String {
    // If the id is not representable in a Rust-compatible string
    if id.starts_with(|c: char| !c.is_ascii_alphabetic() && c != '_')
        || id.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
    {
        format!("_{}_", idl_hash(&id))
    } else {
        id.to_string()
    }
}

pub enum Module {
    Es6 = 0,
    CommonJS = 1,
}

impl Default for Module {
    fn default() -> Self {
        Module::Es6
    }
}

#[derive(Default)]
pub struct Config {
    library_name: Option<String>,
    module: Module,
}

/// The codegen binding for JavaScript. This is not made public.
struct JavaScriptLanguageBinding<'a> {
    config: &'a Config,
    prog: &'a IDLProg,
}

impl<'a> JavaScriptLanguageBinding<'a> {
    fn idl_prefix(&self, v: &str) -> String {
        format!(
            "{}.{}",
            self.config
                .library_name
                .clone()
                .unwrap_or("IDL".to_string()),
            v
        )
    }
}

impl<'a> LanguageBinding for JavaScriptLanguageBinding<'a> {
    fn header(&self) -> Result<String> {
        let prefix = match self.config.module {
            Module::Es6 => "export default",
            Module::CommonJS => "exports =",
        };

        let header = format!(
            "{} function({{ {} }}) {{\n",
            prefix,
            self.config
                .library_name
                .clone()
                .map_or_else(|| "IDL".to_string(), |x| format!("IDL: {}", x))
        );

        Ok(header)
    }

    fn footer(&self) -> Result<String> {
        Ok("\n}\n".to_string())
    }

    fn usage_prim(&self, ty: &PrimType) -> Result<String> {
        let prop = match ty {
            PrimType::Nat => "Nat",
            PrimType::Nat8 => "Nat8",
            PrimType::Nat16 => "Nat8",
            PrimType::Nat32 => "Nat32",
            PrimType::Nat64 => "Nat64",
            PrimType::Int => "Int",
            PrimType::Int8 => "Int8",
            PrimType::Int16 => "Int16",
            PrimType::Int32 => "Int32",
            PrimType::Int64 => "Int64",
            PrimType::Float32 => "Float32",
            PrimType::Float64 => "Float64",
            PrimType::Bool => "Bool",
            PrimType::Text => "Text",
            PrimType::Null => "Null",
            // PrimType::Principal => "Principal",
            PrimType::Empty => "Empty",

            PrimType::Reserved => {
                return Err(Error::msg("Unsupported PrimType: Reserved".to_string()));
            }
        };

        Ok(self.idl_prefix(prop))
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
                        Some(var.to_string())
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
        Ok(self.idl_prefix(&format!("Opt({})", self.usage(ty)?)))
    }

    fn usage_vec(&self, ty: &IDLType) -> Result<String> {
        Ok(self.idl_prefix(&format!("Vec({})", self.usage(ty)?)))
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

    fn usage_principal(&self) -> Result<String> {
        Ok(self.idl_prefix("Principal"))
    }

    fn declare(&self, id: &str, ty: &IDLType) -> Result<String> {
        match ty {
            IDLType::PrimT(prim) => self.declare_prim(&id, prim),
            IDLType::VarT(var) => self.declare_var(&id, var),
            IDLType::FuncT(func) => self.declare_func(&id, func),
            IDLType::OptT(sub_t) => self.declare_opt(&id, sub_t.as_ref()),
            IDLType::VecT(item_t) => self.declare_vec(&id, item_t.as_ref()),
            IDLType::RecordT(fields) => self.declare_record(&id, fields),
            IDLType::VariantT(fields) => self.declare_variant(&id, fields),
            IDLType::ServT(serv_t) => self.declare_service(&id, serv_t),
            IDLType::PrincipalT => self.declare_principal(id),
        }
    }
    fn declare_prim(&self, id: &str, ty: &PrimType) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_prim(ty)?))
    }
    fn declare_var(&self, id: &str, var: &str) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_var(var)?))
    }
    fn declare_func(&self, id: &str, func: &FuncType) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_func(func)?))
    }
    fn declare_opt(&self, id: &str, ty: &IDLType) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_opt(ty)?))
    }
    fn declare_vec(&self, id: &str, ty: &IDLType) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_vec(ty)?))
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
            .collect::<Result<Vec<(String, String)>>>()?
            .iter()
            .map(|(name, ty)| format!("'{}': {},", name, ty))
            .collect::<Vec<String>>()
            .join("\n    ");

        Ok(format!(
            "  const {} = {}({{\n    {}\n  }});\n",
            id,
            self.idl_prefix("Record"),
            all_fields
        ))
    }
    fn declare_variant(&self, id: &str, fields: &[TypeField]) -> Result<String> {
        Ok(format!(
            "  const {} = {};\n",
            id,
            self.usage_variant(fields)?
        ))
    }
    fn declare_service(&self, id: &str, ty: &[Binding]) -> Result<String> {
        Ok(format!("  const {} = {};\n", id, self.usage_service(ty)?))
    }
    fn declare_principal(&self, id: &str) -> Result<String> {
        Ok(format!(
            "  const {} = {};\n",
            id,
            self.idl_prefix("Principal")
        ))
    }

    fn declaration_binding(&self, binding: &Binding) -> Result<String> {
        self.declare(&binding.id, &binding.typ)
    }

    fn service_binding(&self, _id: &str, _func_t: &FuncType) -> Result<String> {
        unreachable!()
    }

    fn service(&self, bindings: &[Binding]) -> Result<String> {
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
                        .map(|ty| self.usage(&ty))
                        .collect::<Result<Vec<String>>>()?;

                    let annotations = func_t
                        .modes
                        .iter()
                        .map(|m| match m {
                            FuncMode::Oneway => "'oneway'".to_string(),
                            FuncMode::Query => "'query'".to_string(),
                        })
                        .collect::<Vec<String>>()
                        .join(", ");

                    Ok(format!(
                        "    '{}': {}([{}], [{}], [{}]),",
                        candid_id_to_javascript(id),
                        self.idl_prefix("Func"),
                        arguments.join(", "),
                        return_type.join(" ,"),
                        annotations,
                    ))
                }
                _ => self.usage(typ),
            })
            .collect::<Result<Vec<String>>>()?;

        Ok(format!(
            "\n  return {}({{\n{}\n  }});",
            self.idl_prefix("Service"),
            all_functions.join("\n"),
        ))
    }
}

/// Takes an IDL string and returns a Rust string, unformatted.
pub fn idl_to_javascript(prog: &IDLProg, config: &Config) -> Result<String> {
    let binding = JavaScriptLanguageBinding {
        config,
        prog: &prog,
    };

    generate_code(&prog, binding)
}
