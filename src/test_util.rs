use crate::{Error, InvalidEdit, Makefile, MakefileItem};
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

/// The error of `result`, which must be an [`Error::InvalidEdit`].
pub(crate) fn expect_invalid_edit<T>(result: Result<T, Error>) -> InvalidEdit {
    match result {
        Err(Error::InvalidEdit(e)) => e,
        Err(e) => panic!("expected an invalid edit, got {e:?}"),
        Ok(_) => panic!("expected an invalid edit, got success"),
    }
}
