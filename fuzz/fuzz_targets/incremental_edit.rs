#![no_main]

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{apply_edit_to_text, Makefile, Parse, TextEdit, TextRange};

// Input layout:
//   u16 (LE) start offset
//   u16 (LE) end offset
//   u16 (LE) split point between original text and replacement text
//   remainder: original text || replacement text
//
// Offsets are clamped to char boundaries so we never construct a TextEdit
// that splits a UTF-8 codepoint (something the public API does not promise
// to handle, so we shouldn't fuzz it).
fuzz_target!(|data: &[u8]| {
    if data.len() < 6 {
        return;
    }
    let start = u16::from_le_bytes([data[0], data[1]]) as usize;
    let end = u16::from_le_bytes([data[2], data[3]]) as usize;
    let split = u16::from_le_bytes([data[4], data[5]]) as usize;
    let body = &data[6..];

    if split > body.len() {
        return;
    }
    let (orig_bytes, new_bytes) = body.split_at(split);

    let Ok(orig) = std::str::from_utf8(orig_bytes) else {
        return;
    };
    let Ok(new_text) = std::str::from_utf8(new_bytes) else {
        return;
    };

    let start = start.min(orig.len());
    let end = end.min(orig.len());
    let (lo, hi) = if start <= end { (start, end) } else { (end, start) };
    if !orig.is_char_boundary(lo) || !orig.is_char_boundary(hi) {
        return;
    }

    let edit = TextEdit::new(
        TextRange::new((lo as u32).into(), (hi as u32).into()),
        new_text.to_string(),
    );

    let parse = Parse::<Makefile>::parse_makefile(orig);
    let (incremental_parse, incremental_text) = parse.apply_edit(orig, &edit);

    // apply_edit_to_text and apply_edit must agree on the resulting text.
    let expected_text = apply_edit_to_text(orig, &edit);
    assert_eq!(incremental_text, expected_text);

    // Incremental reparse must produce the same text as a full reparse,
    // and that text must equal the new source (lossless property must
    // survive incremental edits too).
    let full_parse = Parse::<Makefile>::parse_makefile(&incremental_text);
    let incremental_str = incremental_parse.tree().to_string();
    assert_eq!(incremental_str, incremental_text);
    assert_eq!(incremental_str, full_parse.tree().to_string());
});
