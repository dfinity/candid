use pretty::RcDoc;

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
    // TODO: find a better way to check for empty doc
    if doc.pretty(80).to_string() == "" {
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

pub fn concat<'a, D>(docs: D, sep: &'a str) -> RcDoc<'a>
where
    D: Iterator<Item = RcDoc<'a>>,
{
    RcDoc::intersperse(
        docs,
        if sep != " " {
            RcDoc::text(sep).append(RcDoc::line())
        } else {
            RcDoc::line()
        },
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
