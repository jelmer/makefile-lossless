//! Benchmarks for looking up the line numbers of makefile items.
//!
//! Run with `cargo bench`; `cargo test --benches` runs each one once.

use makefile_lossless::Makefile;

mod common;

fn main() {
    divan::main();
}

/// Parse a makefile and look up the line of each of its items.
#[divan::bench(args = [100, 1000])]
fn parse_and_lines(bencher: divan::Bencher, modules: usize) {
    let text = common::gnu_makefile(modules);
    bencher
        .counter(divan::counter::BytesCount::of_str(&text))
        .bench(|| {
            let makefile = Makefile::parse(divan::black_box(&text)).tree();
            makefile.items().map(|item| item.line()).sum::<usize>()
        });
}

/// Look up item lines alternately in a makefile and one that it includes,
/// as an interpreter does when it returns from an include.
#[divan::bench(args = [10, 100])]
fn interleaved_lines(bencher: divan::Bencher, modules: usize) {
    let outer = Makefile::parse(&common::gnu_makefile(modules)).tree();
    let inner = Makefile::parse(&common::gnu_makefile(10)).tree();
    let outer_items: Vec<_> = outer.items().collect();
    let inner_item = inner.items().last().unwrap();
    bencher.bench_local(|| {
        outer_items
            .iter()
            .map(|item| item.line() + inner_item.line())
            .sum::<usize>()
    });
}
