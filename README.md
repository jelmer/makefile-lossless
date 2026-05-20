Lossless parser for Makefiles
=============================

This crate provides a lossless parser for Makefiles, producing a concrete
syntax tree (CST) that preserves all whitespace, comments and formatting.
Because nothing is discarded, a parsed Makefile can be modified and written
back out with only the intended changes applied.

Parsing
-------

```rust
use makefile_lossless::Makefile;

let contents = r#"PYTHON = python3

.PHONY: all

all: build

build:
	$(PYTHON) setup.py build
"#;

let makefile: Makefile = contents.parse().unwrap();

assert_eq!(makefile.rules().count(), 3);
for rule in makefile.rules() {
    println!("targets: {:?}", rule.targets().collect::<Vec<_>>());
}
```

You can also read from any `std::io::Read`:

```rust,no_run
use std::fs::File;
use makefile_lossless::Makefile;

let makefile = Makefile::read(File::open("Makefile").unwrap()).unwrap();
```

Use `Makefile::read_relaxed` to tolerate syntax errors and still get a tree
back.

Modifying
---------

The tree is mutable. Changes are applied in place and the rest of the file is
left untouched:

```rust
use makefile_lossless::Makefile;

let mut makefile: Makefile = "all:\n".parse().unwrap();
let mut rule = makefile.add_rule("build");
rule.push_command("$(PYTHON) setup.py build");

print!("{}", makefile);
```

License
-------

Apache-2.0
