# w2 — a tiny C compiler for macOS x86-64

A small C compiler inspired by Nora Sandler’s “Writing a C Compiler”. It compiles a single C source file into macOS x86-64 assembly and links it via the system toolchain.

Pipeline: preprocess C ➜ lex ➜ parse ➜ validate ➜ generate three-address code (TAC, "tacky") ➜ generate x86-64 assembly ➜ assemble/link with `gcc`.

## Requirements
- macOS with Command Line Tools (`gcc`/`clang`) available on PATH
  - If missing, install with: `xcode-select --install`
- Rust toolchain with Cargo (edition 2024)
- For running the test suite: Python 3 (used by the upstream test harness)

Target platform: macOS x86-64 (Mach-O syntax, underscore-prefixed symbols). On Apple Silicon, assembling/running x86-64 binaries may require Rosetta and passing `-arch x86_64` (the current driver does not add that flag).

## Installation
This project does not publish binary releases. Clone the repository and build locally:
```bash
git clone --recurse-submodules https://github.com/Fred-Milhorn/w2.git
cd w2
cargo build
```

If you already cloned without submodules, initialize them with:
```bash
make test-init
```

## Build
```bash
# Build the compiler
cargo build

# The compiler binary will be at:
target/debug/w2
```

## Usage
Compile a C file end-to-end (default produces an executable):
```bash
target/debug/w2 path/to/file.c
```

Common flags (you can combine with `--debug` to print the data at each step):
- `--lex`       Stop after lexing
- `--parse`     Stop after parsing (AST)
- `--validate`  Stop after validation (typed/renamed AST)
- `--tacky`     Stop after TAC generation
- `--codegen`   Stop after lowering TAC to internal assembly IR
- `--emitcode`  Stop after emitting text assembly (prints if `--debug`)
- `--compile`   Produce an object file (`.o`) instead of an executable
- `--debug`     Print stage artifacts as they are produced

Examples:
```bash
# Show tokens only
target/debug/w2 --debug --lex examples/hello.c

# Parse and print the AST, then exit
target/debug/w2 --debug --parse examples/hello.c

# Generate assembly and write file.s, then link to produce an executable
target/debug/w2 examples/hello.c
```

Notes:
- The driver preprocesses with `gcc -E -P` to produce a `.i` file before lexing.
- Without `--compile`, the driver assembles/links the emitted `.s` using `gcc`.

## Tests
This repo includes the upstream “writing-a-c-compiler-tests” harness as a git submodule.

Initialize it (or re-sync nested submodules) with:
```bash
make test-init
```

To pull the latest upstream harness while developing:
```bash
make test-update
```

Run chapter tests with the helper script `w2test.sh` from the project root.

Environment variables:
- `CHAPTER` (required): numeric chapter directory to run (e.g., `10`)
- `STAGE` (optional): run tests at a specific compiler stage (`parse`, `validate`, `tacky`, `codegen`, `emitcode`)
- `FAILFAST` (optional): set to `1` to stop on the first test failure
- `RUST_BACKTRACE` (optional): set to `1` (or `full`) to enable Rust backtraces from compiler failures
- `-v`/`--verbose` (optional): verbose script output
- `-f`/`--failfast` (optional): stop on the first test failure
- `-b`/`--backtrace` (optional): force `RUST_BACKTRACE=1` while running the harness

Examples:
```bash
# Run chapter 10 tests end-to-end
CHAPTER=10 ./w2test.sh

# Run chapter 10 tests at the parse stage only
CHAPTER=10 STAGE=parse ./w2test.sh

# Stop on first failure
CHAPTER=10 FAILFAST=1 ./w2test.sh

# Enable Rust backtraces for compiler panics/errors
CHAPTER=10 RUST_BACKTRACE=1 ./w2test.sh

# Or with flags
./w2test.sh --chapter 10 --stage parse --verbose --failfast --backtrace
```

The script invokes `writing-a-c-compiler-tests/test_compiler` with the built binary at `target/debug/w2`.

For compiler-internal checks (non-chapter tests), run:
```bash
cargo test
```

## Contributing & code style
- Edition: Rust 2024. Formatting is enforced via `rustfmt.toml` (max width 100, compressed params, no trailing commas, etc.).
- Errors: use `anyhow::{Result, bail, anyhow}` and `?` for propagation.
- Architecture and extension guidelines are documented in `AGENTS.md`.

## Troubleshooting
- `gcc: command not found` / preprocessing fails: Install Xcode Command Line Tools.
- Assembler errors on Apple Silicon: the backend emits x86-64; consider testing on x86-64 macOS or adapting the build to pass `-arch x86_64` and run under Rosetta.
- If tests fail early, build the compiler first (`cargo build`) and confirm `target/debug/w2` exists.
