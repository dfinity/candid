use pretty::RcDoc;

pub fn enclose<'a>(left: &'a str, doc: RcDoc<'a>, right: &'a str) -> RcDoc<'a> {
    RcDoc::text(left)
        .append(RcDoc::line_())
        .append(doc)
        .nest(2)
        .append(RcDoc::line_())
        .append(right)
        .group()
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
            RcDoc::space()
        },
    )
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
