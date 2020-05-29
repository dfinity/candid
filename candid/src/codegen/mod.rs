//! Provide code generation functions and types for generating code from a Candid file.
//!
//! Each language will have its own module under this one, and a `idl_to_${language}`
//! function should be exported for simplicity.
//!
//! The LanguageBinding is available to all and can be used to configure generation for
//! languages that are unsupported.
use crate::parser::types::{Binding, Dec, FuncType, IDLType, PrimType, TypeField};
use crate::IDLProg;

pub mod rust;
pub use rust::idl_to_rust;

type Result<T = ()> = crate::error::Result<T>;

pub trait LanguageBinding {
    /// Called when the program starts to be analyzed.
    fn start(&self) -> Result<()> {
        Ok(())
    }

    /// Called when the code generation is done, with the output intended.
    /// The return value of this function will be the actual string outputted.
    fn done(&self, output: String) -> Result<String> {
        Ok(output)
    }

    /// The header string that will be prepended to the output.
    fn header(&self) -> Result<String> {
        Ok(String::new())
    }

    /// The footer string that will be appended to the output.
    fn footer(&self) -> Result<String> {
        Ok(String::new())
    }

    /// This method is called when a type is used as a right hand side. By default
    /// it forwards it to a specialized method for each type.
    fn usage(&self, ty: &IDLType) -> Result<String> {
        match ty {
            IDLType::PrimT(prim) => self.usage_prim(prim),
            IDLType::VarT(var) => self.usage_var(var),
            IDLType::FuncT(func) => self.usage_func(func),
            IDLType::OptT(sub_t) => self.usage_opt(sub_t.as_ref()),
            IDLType::VecT(item_t) => self.usage_vec(item_t.as_ref()),
            IDLType::RecordT(fields) => self.usage_record(fields),
            IDLType::VariantT(fields) => self.usage_variant(fields),
            IDLType::ServT(serv_t) => self.usage_service(serv_t),
        }
    }

    /// String to use when using a primary type as a right hand side.
    fn usage_prim(&self, ty: &PrimType) -> Result<String>;

    /// String to use when using a var reference as a right hand side.
    fn usage_var(&self, var: &str) -> Result<String>;

    /// String to use when using a function type as a right hand side.
    fn usage_func(&self, func: &FuncType) -> Result<String>;

    /// String to use when using an optional type as a right hand side.
    fn usage_opt(&self, ty: &IDLType) -> Result<String>;

    /// String to use when using a vector type as a right hand side.
    fn usage_vec(&self, ty: &IDLType) -> Result<String>;

    /// String to use when using a record type as a right hand side.
    fn usage_record(&self, fields: &[TypeField]) -> Result<String>;

    /// String to use when using a variant type as a right hand side.
    fn usage_variant(&self, fields: &[TypeField]) -> Result<String>;

    /// String to use when using a service type as a right hand side.
    fn usage_service(&self, ty: &[Binding]) -> Result<String>;

    /// String to use when declaring a type. This receives the ID of the type,
    /// and the right hand side of the type itself. By default it forwards it to a
    /// specialized method for each type.
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
        }
    }

    /// Function called when declaring a primary type.
    fn declare_prim(&self, id: &str, ty: &PrimType) -> Result<String>;

    /// Function called when declaring a var reference type.
    fn declare_var(&self, id: &str, var: &str) -> Result<String>;

    /// Function called when declaring a function type.
    fn declare_func(&self, id: &str, func: &FuncType) -> Result<String>;

    /// Function called when declaring a optional type.
    fn declare_opt(&self, id: &str, ty: &IDLType) -> Result<String>;

    /// Function called when declaring a vector type.
    fn declare_vec(&self, id: &str, ty: &IDLType) -> Result<String>;

    /// Function called when declaring a record type.
    fn declare_record(&self, id: &str, fields: &[TypeField]) -> Result<String>;

    /// Function called when declaring a variant type.
    fn declare_variant(&self, id: &str, fields: &[TypeField]) -> Result<String>;

    /// Function called when declaring a service type.
    fn declare_service(&self, id: &str, ty: &[Binding]) -> Result<String>;

    /// Function called when an import statement is used.
    fn declaration_import(&self, _module: &str) -> Result<String> {
        Ok(String::new())
    }

    /// Function called when a declaration binding is used.
    fn declaration_binding(&self, binding: &Binding) -> Result<String> {
        self.declare(&binding.id, &binding.typ)
    }

    /// Function called for all declarations in a Candid file.
    fn declarations(&self, declarations: &[Dec]) -> Result<String> {
        Ok(declarations
            .iter()
            .map(|d| match d {
                Dec::ImportD(module) => self.declaration_import(module),
                Dec::TypD(binding) => self.declaration_binding(binding),
            })
            .collect::<Result<Vec<String>>>()?
            .join("\n"))
    }

    /// Function called when declaring the service (or actor) of a candid file. By default
    /// returns the result of calling [service_binding] on all bindings, and returning a
    /// string separated by `\n`.
    fn service(&self, bindings: &[Binding]) -> Result<String> {
        bindings
            .iter()
            .map(|Binding { id, typ }| match typ {
                IDLType::FuncT(func_t) => self.service_binding(id, func_t),
                _ => self.usage(typ),
            })
            .collect::<Result<Vec<String>>>()
            .map(|s| s.join("\n"))
    }

    /// Function called when declaring a binding inside a service.
    fn service_binding(&self, id: &str, typ: &FuncType) -> Result<String>;

    /// The main function which is called when starting the code generation.
    fn prog(&self, prog: &IDLProg) -> Result<String> {
        self.start()?;

        let output = self.header()?
            + &self.declarations(&prog.decs)?
            + &match &prog.actor {
                None => String::new(),
                Some(IDLType::ServT(bindings)) => self.service(bindings)?,
                Some(IDLType::VarT(_)) => unimplemented!(),
                _ => unreachable!(),
            }
            + &self.footer()?;

        self.done(output)
    }
}

/// Generates code using the passed language binding.
pub fn generate_code<Binding: LanguageBinding>(
    prog: &IDLProg,
    language_bindings: Binding,
) -> Result<String> {
    language_bindings.prog(prog)
}
