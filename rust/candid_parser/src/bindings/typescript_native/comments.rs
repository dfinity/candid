use super::conversion_functions_generator::TopLevelNodes;
use swc_core::common::{
    comments::{Comment, CommentKind},
    BytePos, Span, DUMMY_SP,
};

// Simple monotonic position source for synthetic spans
pub struct PosCursor {
    cur: BytePos,
}
impl PosCursor {
    pub fn new() -> Self {
        Self { cur: BytePos(1) }
    }
    pub fn new_synthetic_span(&mut self) -> Span {
        let lo = self.cur;
        self.cur = BytePos(self.cur.0 + 1);
        Span::new(lo, lo)
    }
}

fn make_comment(docs: &[String]) -> Option<Comment> {
    if docs.is_empty() {
        None
    } else {
        // Join all doc lines into a single block comment, with each line prefixed by a space
        let mut comment_text = String::new();
        comment_text.push_str("*\n");
        for line in docs {
            comment_text.push(' ');
            comment_text.push_str(&format!("* {}", line));
            comment_text.push('\n');
        }
        // Remove trailing newline
        if comment_text.ends_with('\n') {
            comment_text.pop();
        }

        comment_text.push('\n');

        Some(Comment {
            span: DUMMY_SP,
            kind: CommentKind::Block,
            text: comment_text.into(),
            // swc_core 0.80+ uses None for comments attached to no specific position
            // If you want to attach to leading, set as Some(true)
            // For now, we use None
            // has_trailing_newline: false, // Only in newer swc
        })
    }
}

pub fn add_comments(top_level_nodes: &mut TopLevelNodes, docs: &[String]) -> Span {
    use swc_core::common::comments::Comments;
    let (_, comments, cursor) = top_level_nodes;
    match docs.len() {
        0 => DUMMY_SP,
        _ => {
            let d = make_comment(docs);
            let span = cursor.new_synthetic_span();
            if let Some(d) = d {
                comments.add_leading(span.lo, d);
            }
            span
        }
    }
}
