#!/bin/bash
# Build helper: build the given module(s) and show only errors / sorry warnings.
export PATH=/n/home13/junweil/.elan/toolchains/leanprover--lean4---v4.29.1/bin:$PATH
out=$(lake build "$@" 2>&1)
echo "$out" | grep -E "^error:|declaration uses .sorry|Build completed|build failed" | grep -v "^error: build failed" | head -60
echo "---"
echo "$out" | grep -A25 "^error: StatLean" | head -120
