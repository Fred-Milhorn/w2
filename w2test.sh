#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
W2ROOT="${SCRIPT_DIR}"
W2BIN="${W2ROOT}/target/debug/w2"
HARNESS_DIR="${W2ROOT}/writing-a-c-compiler-tests"
HARNESS="${HARNESS_DIR}/test_compiler"

# Function to display script usage
usage() {
    echo "Usage: $(basename $0) [OPTIONS]"
    echo "Options:"
    echo " -h, --help      Display this help message"
    echo " -v, --verbose   Enable verbose mode"
    echo " -c, --chapter   Chapter we are working in"
    echo " -s, --stage     Compiler stage we're testing"
}

verbose_mode=false
chapter="${CHAPTER:-}"
stage="${STAGE:-}"

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            usage; exit 0 ;;
        -v|--verbose)
            verbose_mode=true; shift; continue ;;
        -c|--chapter)
            if [[ -z "$2" || "$2" == -* ]]; then
                echo "chapter number is required." >&2; usage; exit 1
            fi
            chapter="$2"; shift 2; continue ;;
        --chapter=*)
            number="${1#*=}"; if [[ -z "$number" ]]; then echo "chapter number is required." >&2; usage; exit 1; fi
            chapter="$number"; shift; continue ;;
        -s|--stage)
            if [[ -z "$2" || "$2" == -* ]]; then
                echo "stage name is required." >&2; usage; exit 1
            fi
            stage="$2"; shift 2; continue ;;
        --stage=*)
            name="${1#*=}"; if [[ -z "$name" ]]; then echo "stage name is required." >&2; usage; exit 1; fi
            stage="$name"; shift; continue ;;
        *)
            echo "Invalid option: $1" >&2; usage; exit 1 ;;
    esac
done

if [[ -z "$chapter" ]]; then
    echo "Chapter is required." >&2
    usage
    exit 1
fi

if [[ ! -x "$W2BIN" ]]; then
    echo "Compiler binary not found at '$W2BIN'." >&2
    echo "Build it first with: cargo build" >&2
    exit 1
fi

if [[ ! -d "$HARNESS_DIR" ]]; then
    echo "Missing test harness directory '$HARNESS_DIR'." >&2
    echo "Initialize submodules first: make test-init" >&2
    exit 1
fi

if [[ ! -x "$HARNESS" ]]; then
    echo "Missing test harness runner '$HARNESS'." >&2
    echo "Initialize or update submodules: make test-init" >&2
    exit 1
fi

cd "$HARNESS_DIR"
if [[ $verbose_mode == true ]]; then set -x; fi

args=(./test_compiler "$W2BIN" --chapter "$chapter")
if [[ -n "$stage" ]]; then
    args+=(--stage "$stage")
fi

"${args[@]}"
