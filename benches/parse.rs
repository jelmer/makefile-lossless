//! Benchmarks for parsing makefiles.
//!
//! Run with `cargo bench`; `cargo test --benches` runs each one once.

use makefile_lossless::{Makefile, MakefileVariant};

mod common;

/// Parse `text`, checking that the benchmark input is valid.
fn checked(text: String, variant: Option<MakefileVariant>) -> String {
    let parsed = match variant {
        Some(variant) => Makefile::parse_with_variant(&text, variant),
        None => Makefile::parse(&text),
    };
    assert_eq!(parsed.errors(), &[]);
    text
}

fn main() {
    divan::main();
}

#[divan::bench(args = [100, 1000])]
fn gnu_make(bencher: divan::Bencher, modules: usize) {
    let text = checked(
        common::gnu_makefile(modules),
        Some(MakefileVariant::GNUMake),
    );
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| Makefile::parse(divan::black_box(&text)));
}

#[divan::bench(args = [100, 1000])]
fn gnu_make_with_variant(bencher: divan::Bencher, modules: usize) {
    let text = checked(
        common::gnu_makefile(modules),
        Some(MakefileVariant::GNUMake),
    );
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| Makefile::parse_with_variant(divan::black_box(&text), MakefileVariant::GNUMake));
}

/// BSD make lines with modifiers containing nested expressions, which used
/// to take time exponential in the nesting depth.
#[divan::bench(args = [4, 24])]
fn bsd_make_nested_modifiers(bencher: divan::Bencher, depth: usize) {
    let mut text = String::from(".include <bsd.own.mk>\n\n");
    for i in 0..200 {
        let matches = (0..depth).fold("*.c".to_string(), |inner, _| format!("${{SRCS:M{inner}}}"));
        let sysv = (0..depth).fold("a".to_string(), |inner, _| format!("${{X:{inner}=b}}"));
        text.push_str(&format!(
            ".if defined(OPT{i}) && !empty(SRCS:M*.c)\n\
             OBJS{i}:= {matches}\n\
             SUBST{i}= {sysv}\n\
             .endif\n\
             .for f in ${{SRCS:M*.c:S/.c$/.o/}}\n\
             CLEANFILES+= ${{f:T}}\n\
             .endfor\n"
        ));
    }
    let text = checked(text, Some(MakefileVariant::BSDMake));
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| Makefile::parse_with_variant(divan::black_box(&text), MakefileVariant::BSDMake));
}

#[divan::bench]
fn nmake(bencher: divan::Bencher) {
    let mut text = String::from("CC = cl\nCFLAGS = /nologo /W3\n\n");
    for i in 0..500 {
        text.push_str(&format!(
            "!IF \"$(CFG)\" == \"debug{i}\"\n\
             CFLAGS = $(CFLAGS) /Zi /DDEBUG={i}\n\
             !ELSEIF DEFINED(RELEASE{i})\n\
             CFLAGS = $(CFLAGS) /O2\n\
             !ENDIF\n\
             \n\
             mod{i}.obj: mod{i}.c mod{i}.h\n\
             \t$(CC) $(CFLAGS) /c mod{i}.c /Fo$@\n\
             \n\
             {{src}}.c{{$(OUTDIR)}}.obj::\n\
             \t$(CC) $(CFLAGS) /Fo$(OUTDIR)\\ /c $<\n\
             \n"
        ));
    }
    let text = checked(text, Some(MakefileVariant::NMake));
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| Makefile::parse_with_variant(divan::black_box(&text), MakefileVariant::NMake));
}

/// A variable value and a recipe line each continued over many lines.
#[divan::bench(args = [100, 5000])]
fn continued_lines(bencher: divan::Bencher, lines: usize) {
    let mut text = String::from("SOURCES = \\\n");
    for i in 0..lines {
        text.push_str(&format!("\tsrc/file{i}.c \\\n"));
    }
    text.push_str("\tsrc/main.c\n\nall:\n\tfor f in $(SOURCES); do \\\n");
    for i in 0..lines {
        text.push_str(&format!("\t  echo \"$$f {i}\"; \\\n"));
    }
    text.push_str("\tdone\n");
    let text = checked(text, Some(MakefileVariant::GNUMake));
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| Makefile::parse(divan::black_box(&text)));
}
