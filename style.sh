#!/usr/bin/env bash

find $dir -not -path '*/\.*' -name '*.hs' -exec stylish-haskell -i {} \;
