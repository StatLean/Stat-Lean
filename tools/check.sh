#!/usr/bin/env bash
# check.sh — `#check` scaffold for fully-elaborated Mathlib name verification.
#
# **For 95% of brick-verification needs, use `./tools/find.sh` instead** —
# it's 270× faster (~0.3s vs ~8s warm) and 626× less RAM (~8 MB vs ~5 GB).
# Use check.sh ONLY when you genuinely need:
#   - elaborated type (universe vars, instance args, desugared notation)
#   - typeclass inference verification
#   - notation reverse-lookup
#
# Usage:
#   ./tools/check.sh 'MemLp.integrable_mul'
#   ./tools/check.sh '(0 : ENNReal) < 1'
#
# Each invocation prints a final line `[check.sh: warm/cold, Ns]` with the
# elapsed wall time, so you can tell whether OS page cache held the Mathlib
# oleans. Threshold: ≤15s = warm, >15s = cold (page cache evicted).
#
# **Cold-start mitigation**: `tools/spawn-worktree.sh` runs one warm-up
# call after creating a fresh worktree, so the first user-facing check.sh
# in any worktree should already be warm. If you see "cold" in this script
# output, your previous workload evicted Mathlib oleans from page cache.
#
# Memory peak: ~5 GB RSS during the lean elaboration. Do NOT run multiple
# check.sh in parallel without a memory budget — see
# notes/agent-workflow/universal-conventions.md §8.

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 '<Lean expression>'" >&2
  echo "(For brick existence + signature, prefer ./tools/find.sh '<name>')" >&2
  exit 1
fi

EXPR="$1"
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="$REPO_ROOT/scratch.lean"

cat > "$SCRATCH" <<EOF
import Mathlib
import LeanSearchClient
#check $EXPR
EOF

cd "$REPO_ROOT"

# Time the call so we can tag it warm vs cold.
START_NS=$(date +%s%N)
lake env lean "$SCRATCH" 2>&1 | grep -v '^$' | head -30
END_NS=$(date +%s%N)

ELAPSED_MS=$(( (END_NS - START_NS) / 1000000 ))
ELAPSED_S=$(( ELAPSED_MS / 1000 ))

if [[ $ELAPSED_S -le 15 ]]; then
  TAG="warm"
else
  TAG="cold"
fi

echo "[check.sh: $TAG, ${ELAPSED_S}s]" >&2
