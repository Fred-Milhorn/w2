## Makefile for w2: convenience wrappers around cargo & test harness

.PHONY: all build check release test test-init test-update test-status clean run

all: build

build:
	cargo build

check:
	cargo check

release:
	cargo build --release

# Initialize chapter-test submodule(s)
test-init:
	git submodule update --init --recursive writing-a-c-compiler-tests

# Pull latest upstream chapter tests and update submodule pointer
test-update:
	git submodule update --remote --merge writing-a-c-compiler-tests

# Show current pinned submodule commit
test-status:
	git submodule status --recursive writing-a-c-compiler-tests

# Usage: make test CHAPTER=10 [STAGE=parse] [FAILFAST=1] [BACKTRACE=1]
test:
	@if [ -z "$$CHAPTER" ]; then \
		echo "CHAPTER is required (e.g. make test CHAPTER=10)" >&2; \
		exit 1; \
	fi; \
	CHAPTER=$$CHAPTER STAGE=$$STAGE FAILFAST=$$FAILFAST RUST_BACKTRACE=$$BACKTRACE ./w2test.sh

# Quick run of the compiler on a file: make run FILE=examples/foo.c ARGS="--debug --parse"
run:
	@if [ -z "$$FILE" ]; then \
		echo "FILE is required (e.g. make run FILE=tests/chapter_1/return_2.c)" >&2; \
		exit 1; \
	fi; \
	cargo build >/dev/null && target/debug/w2 $$ARGS $$FILE

clean:
	cargo clean
