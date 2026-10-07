//! Benchmarks for editing large makefiles.
//!
//! Run with `cargo bench`; `cargo test --benches` runs each one once.

use makefile_lossless::{Makefile, Parse, TextEdit, TextRange, TextSize};

mod common;

const MODULES: usize = 1000;

fn main() {
    divan::main();
}

/// Change a variable value in the middle of a large file and reparse.
#[divan::bench]
fn apply_edit(bencher: divan::Bencher) {
    let text = common::gnu_makefile(MODULES);
    let parse = Parse::<Makefile>::parse_makefile(&text);
    let needle = format!("mod{}_LIBS := -lm", MODULES / 2);
    let start = text.find(&needle).unwrap() + needle.len();
    let edit = TextEdit::new(
        TextRange::new(
            TextSize::try_from(start).unwrap(),
            TextSize::try_from(start).unwrap(),
        ),
        " -lz".to_string(),
    );
    bencher.bench(|| {
        parse
            .apply_edit(divan::black_box(&text), divan::black_box(&edit))
            .unwrap()
    });
}

/// Insert a new line in the middle of a large file and reparse.
#[divan::bench]
fn apply_edit_new_line(bencher: divan::Bencher) {
    let text = common::gnu_makefile(MODULES);
    let parse = Parse::<Makefile>::parse_makefile(&text);
    let needle = format!("# Module {}\n", MODULES / 2);
    let start = TextSize::try_from(text.find(&needle).unwrap()).unwrap();
    let edit = TextEdit::new(TextRange::new(start, start), "EXTRA = 1\n".to_string());
    bencher.bench(|| {
        parse
            .apply_edit(divan::black_box(&text), divan::black_box(&edit))
            .unwrap()
    });
}

#[divan::bench]
fn set_value(bencher: divan::Bencher) {
    let text = common::gnu_makefile(MODULES);
    let name = format!("mod{}_LIBS", MODULES - 1);
    bencher
        .with_inputs(|| Makefile::parse(&text).tree())
        .bench_local_values(|makefile| {
            let mut var = makefile.find_variable(&name).next().unwrap();
            var.set_value("-lm -lz");
            makefile
        });
}

#[divan::bench]
fn add_prerequisite(bencher: divan::Bencher) {
    let text = common::gnu_makefile(MODULES);
    let target = format!("check-mod{}", MODULES - 1);
    bencher
        .with_inputs(|| Makefile::parse(&text).tree())
        .bench_local_values(|makefile| {
            let mut rule = makefile.find_rule_by_target(&target).unwrap();
            rule.add_prerequisite("extra").unwrap();
            makefile
        });
}
