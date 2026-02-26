# w2 — a tiny C compiler for macOS

A small C compiler inspired by Nora Sandler’s “Writing a C Compiler”. It compiles a single C source file into macOS assembly and links it via the system toolchain.

Pipeline: preprocess C ➜ lex ➜ parse ➜ validate ➜ generate three-address code (TAC, "tacky") ➜ generate backend assembly (`x86_64` or `arm64`) ➜ assemble/link with `gcc`.

## Requirements
- macOS with Command Line Tools (`gcc`/`clang`) available on PATH
  - If missing, install with: `xcode-select --install`
- Rust toolchain with Cargo (edition 2024)
- For running the test suite: Python 3 (used by the upstream test harness)

Targets: macOS `x86_64` and macOS `arm64` (Mach-O syntax, underscore-prefixed symbols).
By default, `w2` picks the host architecture backend automatically. You can override it with `--target x86_64` or `--target arm64`.

## Installation
This project does not publish binary releases. Clone the repository and build locally:
```bash
git clone --recurse-submodules https://github.com/Fred-Milhorn/w2.git
cd w2
cargo build
```

If you already cloned without submodules, initialize them with:
```bash
cargo xtask test-init
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
- `--target`    Select backend target (`x86_64` or `arm64`)
- `--debug`     Print stage artifacts as they are produced

Examples:
```bash
# Show tokens only
target/debug/w2 --debug --lex examples/hello.c

# Parse and print the AST, then exit
target/debug/w2 --debug --parse examples/hello.c

# Generate assembly and write file.s, then link to produce an executable
target/debug/w2 examples/hello.c

# Force the arm64 backend on any host
target/debug/w2 --target arm64 examples/hello.c
```

Notes:
- The driver preprocesses with `gcc -E -P` to produce a `.i` file before lexing.
- Without `--compile`, the driver assembles/links the emitted `.s` using `gcc`.

## Tests
This repo includes the upstream “writing-a-c-compiler-tests” harness as a git submodule.

Initialize it (or re-sync nested submodules) with:
```bash
cargo xtask test-init
```

To pull the latest upstream harness while developing:
```bash
cargo xtask test-update
```

Run chapter tests with the Rust-native task runner:

Options:
- `CHAPTER` (required): numeric chapter directory to run (e.g., `10`)
- `STAGE` (optional): run tests at a specific stage (`lex`, `parse`, `validate`, `tacky`, `codegen`, `run`)
- `FAILFAST` (optional): set to `1` to stop on the first test failure
- `RUST_BACKTRACE` (optional): set to `1` (or `full`) to enable Rust backtraces from compiler failures
- `INCREMENT` (optional): set to `1` to include `++`/`--` extra-credit tests
- `GOTO` (optional): set to `1` to include `goto`/labeled-statement extra-credit tests
- `SWITCH` (optional): set to `1` to include `switch`/`case`/`default` extra-credit tests
- `-v`/`--verbose` (optional): verbose harness output
- `--latest-only` (optional): run tests from selected chapter only
- `--target` (optional): pass `x86_64` or `arm64` to the compiler under test
- `-f`/`--failfast` (optional): stop on the first test failure
- `-b`/`--backtrace` (optional): force `RUST_BACKTRACE=1` while running the harness
- `--increment` (optional): include `++`/`--` extra-credit tests
- `--goto` (optional): include `goto`/labeled-statement extra-credit tests
- `--switch` (optional): include `switch`/`case`/`default` extra-credit tests

Examples:
```bash
# Run chapter-10-only tests end-to-end
cargo xtask test --chapter 10 --latest-only

# Run chapter 10 tests at the parse stage only
cargo xtask test --chapter 10 --stage parse

# Run chapter-10-only codegen tests with explicit arm64 backend
cargo xtask test --chapter 10 --latest-only --stage codegen --target arm64

# Stop on first failure
cargo xtask test --chapter 10 --failfast

# Enable Rust backtraces for compiler panics/errors
cargo xtask test --chapter 10 --backtrace

# Include increment/decrement extra-credit tests
cargo xtask test --chapter 5 --increment

# Include goto/labeled-statement extra-credit tests
cargo xtask test --chapter 6 --goto

# Include switch/case/default extra-credit tests
cargo xtask test --chapter 8 --switch

# Include all extra-credit tests
cargo xtask test --chapter 8 --extra-credit

# Combine feature flags
cargo xtask test --chapter 8 --goto --switch

# Environment-variable form also works
CHAPTER=10 STAGE=parse FAILFAST=1 RUST_BACKTRACE=1 EXTRA_CREDIT=1 cargo xtask test
```

Run architecture-agnostic subset tests (Rust-native harness, no Python runner):
- Limited to chapters 1-10
- Excludes tests with upstream `assembly_libs` dependencies
- Includes compile-stage checks and run-stage behavior checks for C-only tests
- Without `--latest-only`, runs cumulatively in chapter order (`chapter_1` through selected chapter)

```bash
# Run portable chapter-10-only behavior/compile subset
cargo xtask test-portable --chapter 10 --latest-only

# Portable parse-stage subset
cargo xtask test-portable --chapter 10 --latest-only --stage parse

# Portable cumulative parse-stage run (chapters 1..10 in order)
cargo xtask test-portable --chapter 10 --stage parse

# Portable run with all extra-credit tests
cargo xtask test-portable --chapter 10 --latest-only --extra-credit
```

### Portable Harness Scope
- `test-portable` is intentionally capped at chapters 1-10.
- It models the architecture-agnostic subset needed for backend-independent compiler behavior checks.
- Later chapters add upstream-harness assumptions (for example, additional optimization/stage flows and other harness semantics) that are not fully mirrored yet in `test-portable`.
- Running beyond chapter 10 without those behaviors can produce misleading results (false pass/fail outcomes).

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
- Cross-architecture linker errors (mixing `arm64` and `x86_64` objects): compile all participating files for the same target architecture.
- If tests fail early, build the compiler first (`cargo build`) and confirm `target/debug/w2` exists.
