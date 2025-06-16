#!/bin/bash -x

W2ROOT="$(pwd)"
chapter=${CHAPTER:?"Chapter is required"}
if [ -z "$STAGE" ]; then
    stage=""
else
    stage="--stage $STAGE"
fi

cd writing-a-c-compiler-tests
./test_compiler "${W2ROOT}/target/debug/w2" --chapter "$chapter" $stage --bitwise --compound
