#![no_main]

mod variant;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((variant, text)) = variant::optional_variant_and_text(data) else {
        return;
    };

    // The parser is meant to be lossless: serialising the tree back to text
    // should reproduce the input byte-for-byte, regardless of whether there
    // were parse errors.
    let parse = variant::parse(text, variant);
    let serialised = parse.tree().to_string();
    assert_eq!(
        serialised, text,
        "lossless roundtrip failed for {variant:?}: input != tree.to_string()"
    );
});
