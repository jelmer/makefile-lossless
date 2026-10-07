#![no_main]

mod variant;

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{split_references, ParsedReference, TextPart};

fuzz_target!(|data: &[u8]| {
    let Some((variant, text)) = variant::variant_and_text(data) else {
        return;
    };

    // The parts are in order and together cover all of the text.
    let mut pos = 0;
    for part in split_references(text, variant) {
        let range = part.range();
        assert_eq!(range.start, pos, "{part:?}");
        assert!(
            range.end > range.start && range.end <= text.len(),
            "{part:?}"
        );
        assert!(text.is_char_boundary(range.end), "{part:?}");
        let part_text = &text[range.clone()];
        match &part {
            TextPart::Literal(_) => assert!(!part_text.contains('$'), "{part:?}"),
            TextPart::EscapedDollar(_) => assert_eq!(part_text, "$$"),
            TextPart::Reference { parsed, .. } => {
                assert!(part_text.starts_with('$') && !part_text.starts_with("$$"));
                // A BSD make reference may depend on the text after it, so
                // compare with parse_prefix rather than parse.
                if let Ok(parsed) = parsed {
                    assert_eq!(
                        ParsedReference::parse_prefix(&text[range.start..], variant),
                        Ok((parsed.clone(), range.len())),
                        "{part:?}"
                    );
                }
            }
            _ => {}
        }
        pos = range.end;
    }
    assert_eq!(pos, text.len());
});
