#!/bin/bash -x

chapter=${CHAPTER:?"Chapter is required"}
if [ -z "$STAGE" ]; then
    stage=""
else
    stage="--stage $STAGE"
fi

cd $HOME/src/writing-a-c-compiler-tests
./test_compiler $HOME/src/w2/target/debug/w2 --chapter "$chapter" $stage --bitwise --compound
