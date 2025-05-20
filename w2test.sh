#!/bin/bash -x

chapter=${CHAPTER:?"Chapter is required"}
if [ -z "$STAGE" ]; then
    stage=""
else
    stage="--stage $STAGE"
fi

cd writing-a-c-compiler-tests
./test_compiler $HOME/rust/w2/target/debug/w2 --chapter "$chapter" $stage --bitwise --compound
