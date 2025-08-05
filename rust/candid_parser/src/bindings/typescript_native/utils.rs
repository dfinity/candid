use swc_core::ecma::{
    ast::Module,
    codegen::{text_writer::JsWriter, Config, Emitter},
};

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
