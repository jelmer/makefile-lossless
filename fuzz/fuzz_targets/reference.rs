#![no_main]

mod variant;

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{ParsedReference, ReferenceError};

/// Check that the offset of `error` is a position in `text`.
fn check_error(text: &str, error: &ReferenceError) {
    let offset = match error {
        ReferenceError::Syntax { offset, .. } | ReferenceError::UnknownModifier { offset, .. } => {
            *offset
        }
        _ => return,
    };
    assert!(offset <= text.len(), "{error:?}");
    assert!(text.is_char_boundary(offset), "{error:?}");
}

fuzz_target!(|data: &[u8]| {
    let Some((variant, text)) = variant::variant_and_text(data) else {
        return;
    };

    let prefix = ParsedReference::parse_prefix(text, variant);
    match &prefix {
        Ok((_, len)) => {
            assert!(*len > 0 && *len <= text.len(), "{len}");
            assert!(text.is_char_boundary(*len));
        }
        Err(e) => check_error(text, e),
    }

    // parse is parse_prefix of all of the text.
    let parsed = ParsedReference::parse(text, variant);
    match (&parsed, &prefix) {
        (Ok(parsed), Ok((prefix, len))) => {
            assert_eq!(*len, text.len());
            assert_eq!(parsed, prefix);
        }
        (Ok(_), Err(e)) => panic!("parse succeeded but parse_prefix failed: {e:?}"),
        (Err(e), Ok((_, len))) => {
            check_error(text, e);
            assert_ne!(*len, text.len(), "{e:?}");
        }
        (Err(e), Err(_)) => check_error(text, e),
    }

    if let Err(e) = ParsedReference::parse_body(text, variant) {
        check_error(text, &e);
    }
});
