#!/bin/bash

run_diff() {
    # $1: bil path
    # $2: binary path
    diff ./disas/$1.bil <(./ssa.sh ./bins/$1)
}

for l in $(ls ./bins); do
    run_diff $l
    if [ $? != 0 ]; then
        echo Fail $l
        exit 1
    else
        echo Success $l
    fi
done
exit 0
