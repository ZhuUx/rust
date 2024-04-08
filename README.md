This repository is created for implementating instrumentation-based [modified condition/decision coverage](https://en.wikipedia.org/wiki/Modified_condition/decision_coverage) in rust compiler based on llvm.

It is still under development and waiting for more tests. All changes are committed to the master branch.

## Roadmap

See the [track issure](https://github.com/rust-lang/rust/issues/124144)

## Quick start

To run tests

```bash
git clone https://github.com/ZhuUx/rust.git
git checkout master
./x build --stage 1
./x test tests/coverage/mcdc_if.rs
```

To check code of `foo`
```bash
export PATH=path/to/llvm-build:$PATH
rustup toolchain link mcdc build/host/stage1
cargo +mcdc rustc --bin foo -- -Cinstrument-coverage -Zcoverage-options=mcdc
cd target/debug
LLVM_PROFILE_FILE="foo.profraw" ./foo
llvm-profdata merge -sparse foo.profraw -o foo.profdata   
llvm-cov show ./foo -instr-profile=foo.profdata --show-mcdc
```

Note that if a custom llvm is used, the llvm version should be 18 or later.

## Acknowledgment & Credits

This repository only contains works by [Banma](https://www.ebanma.com). But mcdc implementation for rust also is co-authored by [RenjiSann](https://github.com/RenjiSann) from [Adacore](https://www.adacore.com), [Zalathar](https://github.com/Zalathar).

[evodius96](https://github.com/evodius96) lands mcdc implementation on llvm and clarifies the details.

 implements branch coverage, which introduces essential base for mcdc, and reviews a lot.

[Ferrous](https://ferrous-systems.com) shares their research about mcdc in rust.


