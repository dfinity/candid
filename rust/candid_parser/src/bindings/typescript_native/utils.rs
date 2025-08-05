use swc_core::ecma::{
    ast::Module,
    codegen::{text_writer::JsWriter, Config, Emitter},
};

use candid::types::{Type, TypeEnv, TypeInner};
use swc_core::common::comments::SingleThreadedComments;
use swc_core::common::source_map::SourceMap;
use swc_core::common::sync::Lrc;

pub fn render_ast(module: &Module) -> String {
    let mut buf = vec![];
    let comments = SingleThreadedComments::default();
    let cm = Lrc::new(SourceMap::default());
    {
        let writer = JsWriter::new(cm.clone(), "\n", &mut buf, None);
        let mut emitter = Emitter {
            cfg: Config::default().with_minify(false),
            cm: cm.clone(),
            comments: Some(&comments),
            wr: Box::new(writer),
        };

        emitter.emit_module(module).unwrap();
    }

    String::from_utf8(buf).unwrap()
}

// Helper function to determine if a type is recursively optional
pub fn is_recursive_optional(
    env: &TypeEnv,
    ty: &Type,
    visited: &mut std::collections::HashSet<String>,
) -> bool {
    use TypeInner::*;

    match ty.as_ref() {
        Var(id) => {
            if !visited.insert(id.clone()) {
                // We've seen this type before, it's recursive
                return true;
            }

            if let Ok(inner_type) = env.find_type(id) {
                is_recursive_optional(env, inner_type, visited)
            } else {
                false
            }
        }
        Opt(inner) => {
            // If we have an optional type, check its inner type
            if let Var(id) = inner.as_ref() {
                if visited.contains(id) {
                    // Found recursive optional
                    return true;
                }
            }
            is_recursive_optional(env, inner, visited)
        }
        _ => false,
    }
}
