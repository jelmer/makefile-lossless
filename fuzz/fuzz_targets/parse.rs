#![no_main]

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{Makefile, Parse};

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };

    // Full-file parse: must never panic, even on garbage input.
    let parse = Parse::<Makefile>::parse_makefile(text);
    let _tree = parse.tree();
    let _ = parse.errors();
    let _ = parse.positioned_errors();

    // Also exercise the convenience FromStr entry point.
    let _: Result<Makefile, _> = text.parse();
});
