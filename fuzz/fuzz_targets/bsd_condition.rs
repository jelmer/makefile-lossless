#![no_main]

use libfuzzer_sys::fuzz_target;
use makefile_lossless::{parse_bsd_condition, parse_bsd_if_else_condition};

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    for result in [parse_bsd_condition(text), parse_bsd_if_else_condition(text)] {
        if let Err(e) = result {
            assert!(e.offset <= text.len(), "{e:?}");
            assert!(text.is_char_boundary(e.offset), "{e:?}");
        }
    }
});
