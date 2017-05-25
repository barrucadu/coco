#!/usr/bin/env bash

echo -n "MVar:"
time stack exec examples-mvar         > examples/MVar.out

echo -ne "\nStack:"
time stack exec examples-stack        > examples/Stack.out

echo -ne "\nComplex Stack:"
time stack exec examples-complexstack > examples/ComplexStack.out

echo -ne "\nSemaphore:"
time stack exec examples-sem          > examples/Sem.out
