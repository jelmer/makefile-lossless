use crate::{Makefile, MakefileItem};
use rowan::ast::AstNode;

/// Parse `src` as a single item that does not end in a newline.
pub(crate) fn item_without_newline(src: &str) -> MakefileItem {
    let item = src.parse::<Makefile>().unwrap().items().next().unwrap();
    assert_eq!(item.syntax().to_string(), src);
    item
}

/// Check that `makefile` has the same tree as when its text is parsed again.
pub(crate) fn assert_matches_reparse(makefile: &Makefile) {
    let reparsed: Makefile = makefile.to_string().parse().unwrap();
    assert_eq!(
        format!("{:#?}", makefile.syntax()),
        format!("{:#?}", reparsed.syntax())
    );
}
