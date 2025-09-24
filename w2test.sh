#!/bin/bash

W2ROOT="$(pwd)"

# Function to display script usage
usage() {
    echo "Usage: $(basename $0) [OPTIONS]"
    echo "Options:"
    echo " -h, --help      Display this help message"
    echo " -v, --verbose   Enable verbose mode"
    echo " -c, --chapter   Chapter we are working in"
    echo " -s, --stage     Compiler stage we're testing"
}

has_argument() {
    # Accept either --flag=value form or --flag value form.
    local current="$1"
    local next="$2"
    if [[ "$current" == *=* ]]; then
        return 0
    fi
    if [[ -n "$next" && "$next" != -* ]]; then
        return 0
    fi
    return 1
}

extract_argument() {
    echo "${2:-${1#*=}}"
}

verbose_mode=false
chapter=""
stage=""

if [[ ! -z $STAGE ]]; then
    stage="--stage $STAGE"
fi
if [[ ! -z $CHAPTER ]]; then
    chapter="--chapter $CHAPTER"
fi

while [ $# -gt 0 ]; do
    case $1 in
        -h | --help)
            usage
            exit 0
            ;;
        -v | --verbose)
            verbose_mode=true
            ;;
                -c | --chapter | --chapter=*)
                        if ! has_argument "$1" "$2"; then
                            echo "chapter number is required." >&2
                            usage
                            exit 1
                        fi
                        number=$(extract_argument "$1" "$2")
                        chapter="--chapter $number"
                        # If we consumed a separate argument (no =), shift an extra time
                        if [[ "$1" != *=* && "$1" != *"="* && "$1" != *"=" ]]; then
                            if [[ "$1" != *=* && "$1" != *"="* && -n "$2" && "$2" != -* ]]; then shift; fi
                        fi
                        ;;
                -s | --stage | --stage=*)
                        if ! has_argument "$1" "$2"; then
                            echo "stage name is required." >&2
                            usage
                            exit 1
                        fi
                        name=$(extract_argument "$1" "$2")
                        stage="--stage $name"
                        if [[ "$1" != *=* && -n "$2" && "$2" != -* ]]; then shift; fi
                        ;;
        *)
            echo "Invalid option: $1" >&2
            usage
            exit 1
            ;;
    esac
    shift
done

if [[ -z $chapter ]]; then
    echo "Chapter is required." >&2
    usage
    exit 1
fi

cd writing-a-c-compiler-tests
if [[ $verbose_mode == true ]]; then set -x; fi
./test_compiler "${W2ROOT}/target/debug/w2" $chapter $stage
