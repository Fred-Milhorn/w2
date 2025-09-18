# Copilot project instructions for `w2`

These instructions help Copilot produce code and edits that match this repository’s architecture, style, and constraints.

## Project overview
- Purpose: A tiny C compiler targeting x86-64 macOS, inspired by Nora Sandler’s “Writing a C Compiler”.
- Pipeline: preprocess C -> lex -> parse -> validate -> generate TAC (tacky) -> generate x86-64 asm -> assemble/link with gcc.
- Entry point: `src/main.rs` with flags to stop after stages: `--lex`, `--parse`, `--validate`, `--tacky`, `--codegen`, `--emitcode`, `--compile`. `--debug` prints stage artifacts.
- Supported C subset: ints/longs, unary/binary ops, conditionals, loops (`while`, `do-while`, `for`), `break`/`continue`, functions, file-scope and block-scope variables, `static`/`extern` storage.

## Modules and responsibilities
- `lex.rs`: Converts source into tokens (see `Token` enum and regexes). Keep regexes anchored at start; whitespace consumed per-loop.
- `parse.rs`: Pratt-style/precedence-climbing expression parser and statement/declaration parser producing AST. See enums: `Expression`, `Statement`, `Type`, `Declaration`, etc. Use `Token::precedence`, `is_binary_operator`, `is_compound_assignment`.
- `validate.rs`: Resolves identifiers with unique names, labels loops, maintains `SYMBOLS` and `BACKEND` tables, and performs type checking and conversion insertion. Also enforces storage class/linkage rules.
- `tacky.rs`: Low-level three-address code (TAC) generation from validated AST; emits control-flow with labels and simple instructions. Also converts file-scope `static`/`extern` symbols into definitions.
- `code.rs`: Low-level x86-64 assembly emission (macOS Mach-O syntax). Handles register allocation for params/temps, stack fixups, calling convention, and text/data/bss emission.
- `utils.rs`: GCC subprocess helpers for preprocessing and assembling, temp name generation.

## Coding conventions
- Edition: Rust 2024. Follow `rustfmt.toml` in repo (max width 100, Compressed params, Never trailing commas, etc.). Annotate dense match/impls with `#[rustfmt::skip]` where layout matters.
- Errors: Use `anyhow::{Result, bail, anyhow}`. Prefer `bail!(...)` for control-flow errors; propagate with `?`.
- Cloning: Most AST nodes are `Clone`; prefer cloning small enums/strings as needed over lifetimes.
- Thread-locals: Use `SYMBOLS`/`BACKEND` via `with_borrow/_mut` helpers; don’t store references across calls.
- Naming: Temporary names via `utils::temp_name(prefix)`; loop labels via `utils::mklabel(kind, label)`.
- Data types: C `int` => `Type::Int` (32-bit), `long` => `Type::Long` (64-bit). Assembly sizes via `AssemblyType::{Longword,Quadword}`.
- Platform: macOS x86-64, System V-like calling but Mach-O/Mac asm syntax, underscores on symbol names when emitting.

## Adding features safely
When extending the language or backend, keep these guardrails:
- Lexer: Update token enums and regex groups consistently. Add to `precedence`, `is_binary_operator`, and `is_compound_assignment` as needed.
- Parser: Respect precedence climbing in `parse_expression`. Update `parse_binary`, `parse_unary`, factor parsing, and statements. Ensure semicolons and parens are consumed.
- Validator: Resolve names with unique temps; enforce storage and linkage; add type rules. Insert conversions with `convert::convert_to` and `get_common_type`.
- Tacky: Keep instructions simple; generate branch structures with labels. Ensure functions without return still emit `Return(ZERO)`.
- Codegen: Convert TAC to assembly using helpers (`tacky_to_assembly`, `fixup_pseudo`, `fixup_invalid`, `allocate_stack`). Use `val_type` to choose mov width. Avoid invalid mem-mem ops; use scratch regs R10/R11/CX patterns already established.

## Typical workflows Copilot should follow
- New operator: add token/precedence -> parse -> validate type rules -> TAC emission (and/or lower in codegen) -> tests.
- New statement form: add tokens, parser production, validation semantics, TAC lowering, and assembly fixups if needed.
- Built-in functions: Declare in symbol table with `IdentAttrs::Function` and proper type to pass validation and codegen.

## Runtime and tests
- Build: `cargo build`.
- Run compiler: `target/debug/w2 [--debug] [--lex|--parse|--validate|--tacky|--codegen|--emitcode|--compile] file.c`.
- Tests: Use `w2test.sh` wrapper around `writing-a-c-compiler-tests/test_compiler`. Example: `CHAPTER=10 ./w2test.sh` or `CHAPTER=10 STAGE=parse ./w2test.sh`.

## Distribution/installation
- This repository does not publish binary releases. Users are expected to clone the repo and build locally with `cargo build`.
- Avoid suggesting install commands like `cargo install <crate>` or downloading binaries from GitHub releases.

## Style do’s and don’ts for suggestions
Do:
- Keep matches exhaustive and explicit; prefer small helper fns for clarity.
- Preserve existing public function signatures and module boundaries.
- Reuse existing tmp/label helpers instead of inventing formats.
- Use `#[rustfmt::skip]` where tables and alignment matter.

Don’t:
- Introduce external crates beyond the existing ones without discussion.
- Change calling convention, Mach-O specifics, or symbol underscore prefixing.
- Emit trailing commas in enums/structs contrary to rustfmt config.

## Known quirks/notes
- `parse_constant` uses `2 ^ 31` which is bitwise XOR in Rust; it still produces a small limit but is semantically off. If adjusting, consider `(1i64 << 31) - 1`.
- Assembly emitter currently always uses 32-bit ops for integer ALU and handles sign-extension/truncation explicitly; keep consistent unless widening semantics are changed.
- Function prologue/epilogue is minimal; stack alignment handled by `fixup_pseudo` and call-sites add padding for odd arg counts.

## Snippet patterns Copilot can reuse
- Label pattern for short-circuiting (see `tacky::emit_tacky` for And/Or, Conditional).
- Mem-mem fixup patterns with R10/R11 and shift-by-CX idiom in `code::fixup_invalid`.
- Param move-in from registers and from stack in `code::gen_assembly`.

## How to propose changes
- Touch the smallest surface area; avoid broad reformatting.
- Add value-focused comments near complex transformations.
- Prefer adding tests under `writing-a-c-compiler-tests` harness.

