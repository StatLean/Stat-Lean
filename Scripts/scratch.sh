#!/usr/bin/env bash
# Compile a scratch file against the already-built StatLean + Mathlib olean tree.
set -u
ROOT=/n/holylabs/junweil_lab/Lab/Users/junweil/Projects/Stat-Lean.worktrees/ts-s9-tar-pathspace
export LEAN_PATH=$ROOT/.lake/packages/Cli/.lake/build/lib/lean:$ROOT/.lake/packages/batteries/.lake/build/lib/lean:$ROOT/.lake/packages/Qq/.lake/build/lib/lean:$ROOT/.lake/packages/aesop/.lake/build/lib/lean:$ROOT/.lake/packages/proofwidgets/.lake/build/lib/lean:$ROOT/.lake/packages/importGraph/.lake/build/lib/lean:$ROOT/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$ROOT/.lake/packages/plausible/.lake/build/lib/lean:/n/holylabs/junweil_lab/Lab/Users/junweil/lake-shared/mathlib/5e932f97dd25535344f80f9dd8da3aab83df0fe6/.lake/build/lib/lean:$ROOT/.lake/build/lib/lean
exec /n/holylabs/junweil_lab/Lab/Users/junweil/elan/toolchains/leanprover--lean4---v4.29.1/bin/lean "$@"
