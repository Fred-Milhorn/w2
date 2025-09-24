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

extract_argument_pair() {
    # $1 = current token, $2 = next token
    local current="$1"; local next="$2"
    if [[ "$current" == *=* ]]; then
        echo "${current#*=}"
    else
        echo "$next"
    fi
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
        -h|--help)
            usage; exit 0 ;;
        -v|--verbose)
            verbose_mode=true; shift; continue ;;
        -c|--chapter)
            if [[ -z "$2" || "$2" == -* ]]; then
                echo "chapter number is required." >&2; usage; exit 1
            fi
            chapter="--chapter $2"; shift 2; continue ;;
        --chapter=*)
            number="${1#*=}"; if [[ -z "$number" ]]; then echo "chapter number is required." >&2; usage; exit 1; fi
            chapter="--chapter $number"; shift; continue ;;
        -s|--stage)
            if [[ -z "$2" || "$2" == -* ]]; then
                echo "stage name is required." >&2; usage; exit 1
            fi
            stage="--stage $2"; shift 2; continue ;;
        --stage=*)
            name="${1#*=}"; if [[ -z "$name" ]]; then echo "stage name is required." >&2; usage; exit 1; fi
            stage="--stage $name"; shift; continue ;;
        *)
            echo "Invalid option: $1" >&2; usage; exit 1 ;;
    esac
done

if [[ -z $chapter ]]; then
    echo "Chapter is required." >&2
    usage
    exit 1
fi

cd writing-a-c-compiler-tests
if [[ $verbose_mode == true ]]; then set -x; fi
./test_compiler "${W2ROOT}/target/debug/w2" $chapter $stage
