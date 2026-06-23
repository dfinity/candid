use pretty::{RcAllocator, RcDoc};

pub const INDENT_SPACE: isize = 2;
pub const LINE_WIDTH: usize = 80;

fn is_empty(doc: &RcDoc) -> bool {
    use pretty::Doc::*;
    match &**doc {
        Nil => true,
        FlatAlt(t1, t2) => is_empty(t2) || is_empty(t1),
        Union(t1, t2) => is_empty(t1) && is_empty(t2),
        Group(t) | Nest(_, t) | Annotated((), t) => is_empty(t),
        _ => false,
    }
}

pub fn enclose<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    if is_empty(&doc) {
        RcDoc::text(left).append(right)
    } else {
        RcDoc::text(left)
            .append(RcDoc::line_())
            .append(doc)
            .nest(INDENT_SPACE)
            .append(RcDoc::line_())
            .append(right)
            .group()
    }
}

pub fn enclose_space<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    if is_empty(&doc) {
        RcDoc::text(left).append(right)
    } else {
        RcDoc::text(left)
            .append(RcDoc::line())
            .append(doc)
            .nest(INDENT_SPACE)
            .append(RcDoc::line())
            .append(right)
            .group()
    }
}

/// Intersperse the separator between each item in `docs`.
pub fn strict_concat<'a, D>(docs: D, sep: &'a str) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::intersperse(docs, RcDoc::text(sep).append(RcDoc::line()))
}

/// Append the separator to each item in `docs`. If it is displayed in a single line, omit the last separator.
pub fn concat<'a, D>(docs: D, sep: &'a str) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    let mut docs = docs.peekable();
    if docs.peek().is_none() {
        return RcDoc::nil();
    }
    let singleline = RcDoc::intersperse(docs, RcDoc::text(sep).append(RcDoc::line()));
    let multiline = singleline.clone().append(sep);
    multiline.flat_alt(singleline)
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
mod test {
    use super::*;

    #[test]
    fn concat_empty() {
        let t = concat(vec![].into_iter(), ",")
            .pretty(LINE_WIDTH)
            .to_string();
        assert_eq!(t, "");
    }
}
