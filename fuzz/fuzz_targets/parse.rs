#![no_main]

mod variant;

use libfuzzer_sys::fuzz_target;
use makefile_lossless::Makefile;

fuzz_target!(|data: &[u8]| {
    let Some((variant, text)) = variant::optional_variant_and_text(data) else {
        return;
    };

    // Full-file parse: must never panic, even on garbage input.
    let parse = variant::parse(text, variant);
    assert_eq!(parse.variant(), variant);
    assert_eq!(parse.tree().to_string(), text);
    let _ = parse.errors();
    for error in parse.positioned_errors() {
        let range = std::ops::Range::<usize>::from(error.range);
        assert!(range.end <= text.len(), "{error:?}");
        assert!(text.is_char_boundary(range.start) && text.is_char_boundary(range.end));
    }

    // Also exercise the convenience FromStr entry point.
    let _: Result<Makefile, _> = text.parse();
});
