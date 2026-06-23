use pretty::{RcAllocator, RcDoc};

pub const INDENT_SPACE: isize = 2;
pub const LINE_WIDTH: usize = 80;

pub fn enclose<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    RcDoc::text(left)
        .append(RcDoc::line_())
        .append(doc)
        .nest(INDENT_SPACE)
        .append(RcDoc::line_())
        .append(right)
        .group()
}

pub fn enclose_space<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    RcDoc::text(left)
        .append(RcDoc::line())
        .append(doc)
        .nest(INDENT_SPACE)
        .append(RcDoc::line())
        .append(right)
        .group()
}

/// Intersperse the separator between each item in `docs`.
pub fn strict_concat<'a, D>(docs: D, sep: &'a str) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::intersperse(docs, RcDoc::text(sep).append(RcDoc::line()))
}

pub fn lines<'a, D>(docs: D) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::concat(docs.map(|doc| doc.append(RcDoc::hardline())))
}

pub fn kwd<U: std::fmt::Display + ?Sized>(str: &U) -> RcDoc<'_> {
    RcDoc::as_string(str).append(RcDoc::space())
}

pub fn str(str: &str) -> RcDoc<'_> {
    RcDoc::text(str)
}

pub fn ident(id: &str) -> RcDoc<'_> {
    kwd(id)
}

pub fn quote_ident(id: &str) -> RcDoc<'_> {
    str("'")
        .append(format!("{}", id.escape_debug()))
        .append("'")
        .append(RcDoc::space())
}

/// Separate each item in `docs` with the separator `sep`, and enclose the result in `open` and `close`.
/// When placed on multiple lines, the last element gets a trailing separator.
pub fn sep_enclose<'a, D, S, O, C>(docs: D, sep: S, open: O, close: C) -> RcDoc<'a>
where
    D: IntoIterator<Item = RcDoc<'a>>,
    S: pretty::Pretty<'a, RcAllocator>,
    O: pretty::Pretty<'a, RcAllocator>,
    C: pretty::Pretty<'a, RcAllocator>,
{
    let sep = sep.pretty(&RcAllocator);
    let elems = RcDoc::intersperse(docs, sep.clone().append(RcDoc::line()));
    open.pretty(&RcAllocator)
        .into_doc()
        .append(RcDoc::line_())
        .append(elems)
        .append(sep.flat_alt(RcDoc::nil()))
        .nest(INDENT_SPACE)
        .append(RcDoc::line_())
        .append(close.pretty(&RcAllocator))
        .group()
}

/// Like `sep_enclose`, but inserts a space between the opening delimiter and the first element,
/// and between the last element and the closing delimiter when placed on a single line.
pub fn sep_enclose_space<'a, D, S, O, C>(docs: D, sep: S, open: O, close: C) -> RcDoc<'a>
where
    D: IntoIterator<Item = RcDoc<'a>>,
    S: pretty::Pretty<'a, RcAllocator>,
    O: pretty::Pretty<'a, RcAllocator>,
    C: pretty::Pretty<'a, RcAllocator>,
{
    let mut docs = docs.into_iter().peekable();
    if docs.peek().is_none() {
        return open.pretty(&RcAllocator).append(close).into_doc();
    }
    let open = open
        .pretty(&RcAllocator)
        .append(RcDoc::nil().flat_alt(RcDoc::space()));
    let close = RcDoc::nil().flat_alt(RcDoc::space()).append(close);
    sep_enclose(docs, sep, open, close)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enclose_empty() {
        let t = sep_enclose(vec![], ",", "(", ")")
            .pretty(LINE_WIDTH)
            .to_string();
        assert_eq!(t, "()");
    }

    #[test]
    fn enclose_single_line() {
        let printed = sep_enclose(vec![str("a"), str("b")], ",", "(", ")")
            .pretty(LINE_WIDTH)
            .to_string();
        assert_eq!(printed, "(a, b)");
    }

    #[test]
    fn enclose_multiline() {
        let docs: Vec<RcDoc> = vec![
            str("Very long line to make sure we get a multiline document"),
            str("Very long line to make sure we get a multiline document"),
        ];
        let printed = sep_enclose(docs, ",", "(", ")").pretty(20).to_string();
        assert_eq!(
            printed,
            "
(
  Very long line to make sure we get a multiline document,
  Very long line to make sure we get a multiline document,
)
"
            .trim()
        );
    }

    #[test]
    fn enclose_empty_space() {
        let t = sep_enclose_space(vec![], ",", "(", ")")
            .pretty(LINE_WIDTH)
            .to_string();
        assert_eq!(t, "()");
    }

    #[test]
    fn enclose_single_line_space() {
        let printed = sep_enclose_space(vec![str("a"), str("b")], ",", "(", ")")
            .pretty(LINE_WIDTH)
            .to_string();
        assert_eq!(printed, "( a, b )");
    }

    #[test]
    fn enclose_multiline_space() {
        let docs: Vec<RcDoc> = vec![
            str("Very long line to make sure we get a multiline document"),
            str("Very long line to make sure we get a multiline document"),
        ];
        let printed = sep_enclose_space(docs, ",", "(", ")")
            .pretty(20)
            .to_string();
        assert_eq!(
            printed,
            "
(
  Very long line to make sure we get a multiline document,
  Very long line to make sure we get a multiline document,
)"
            .trim()
        );
    }
}
