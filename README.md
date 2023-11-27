Lossless parser for Makefiles
=============================

This crate provides a lossless parser for makefiles, creating a modifiable CST.

Example:

```rust

let mf = Makefile::read("Makefile").unwrap();

println!("Rules in the makefile: {:?}", mf.rules().map(|r| r.targets().join(" ")).collect::<Vec<_>>());
```
