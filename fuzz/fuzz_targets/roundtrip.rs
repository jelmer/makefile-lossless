#![no_main]

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{Makefile, Parse};

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };

    // The parser is meant to be lossless: serialising the tree back to text
    // should reproduce the input byte-for-byte, regardless of whether there
    // were parse errors.
    let parse = Parse::<Makefile>::parse_makefile(text);
    let tree = parse.tree();
    let serialised = tree.to_string();
    assert_eq!(
        serialised, text,
        "lossless roundtrip failed: input != tree.to_string()"
    );
});
