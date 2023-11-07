use pretty::RcDoc;

pub const INDENT_SPACE: isize = 2;
pub const LINE_WIDTH: usize = 80;

fn is_empty(doc: &RcDoc) -> bool {
    use pretty::Doc::*;
    match &**doc {
        Nil => true,
        FlatAlt(t1, t2) | Union(t1, t2) => is_empty(t1) && is_empty(t2),
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
    D: Iterator<Item = RcDoc<'a>> + Clone,
{
    RcDoc::intersperse(docs.clone().map(|d| d.append(sep)), RcDoc::line()).flat_alt(
        RcDoc::intersperse(docs, RcDoc::text(sep).append(RcDoc::line())),
    )
}

pub fn lines<'a, D>(docs: D) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::concat(docs.map(|doc| doc.append(RcDoc::hardline())))
}

pub fn kwd<U: std::fmt::Display + ?Sized>(str: &U) -> RcDoc {
    RcDoc::as_string(str).append(RcDoc::space())
}

pub fn str(str: &str) -> RcDoc {
    RcDoc::text(str)
}

pub fn ident(id: &str) -> RcDoc {
    kwd(id)
}

pub fn quote_ident(id: &str) -> RcDoc {
    str("'")
        .append(format!("{}", id.escape_debug()))
        .append("'")
        .append(RcDoc::space())
}
