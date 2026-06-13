#!/usr/bin/env bash
# spawn-worktree.sh — create a sibling git worktree for a subagent task.
#
# Used by the manager (main conversation) to give a worker subagent its own
# tree to write/build in. One-shot: creates `../Asymptotic-Statistics-<name>/`
# off current HEAD and primes the Mathlib cache. No daemon, no cleanup.
#
# Usage:
#   ./tools/spawn-worktree.sh <name>
#
# After it returns, paste the printed `cd` line into the subagent's prompt.
# Tear down later with:
#   git worktree remove ../Asymptotic-Statistics-<name>

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <name>" >&2
  exit 1
fi

NAME="$1"
case "$NAME" in
  *[^a-zA-Z0-9_-]*|"")
    echo "Worktree name must be non-empty and only [A-Za-z0-9_-]: '$NAME'" >&2
    exit 1
    ;;
esac

ROOT="$(git rev-parse --show-toplevel)"
PARENT="$(dirname "$ROOT")"
TARGET="$PARENT/Asymptotic-Statistics-$NAME"
BRANCH="agent-$NAME"

if [[ -e "$TARGET" ]]; then
  echo "Refusing to overwrite: $TARGET already exists." >&2
  echo "Pick a different name or remove the existing tree:" >&2
  echo "  git worktree remove $TARGET" >&2
  exit 1
fi

if git -C "$ROOT" show-ref --verify --quiet "refs/heads/$BRANCH"; then
  echo "Refusing to reuse branch: refs/heads/$BRANCH already exists." >&2
  echo "Pick a different name, or delete with:  git branch -D $BRANCH" >&2
  exit 1
fi

echo "Creating worktree at $TARGET on new branch $BRANCH (from HEAD)..." >&2
git -C "$ROOT" worktree add -b "$BRANCH" "$TARGET" HEAD

if [[ ! -d "$ROOT/.lake/packages" ]]; then
  echo "Refusing to spawn: $ROOT/.lake/packages missing." >&2
  echo "Run 'lake exe cache get' or 'lake build' in the source worktree first, then retry." >&2
  git -C "$ROOT" worktree remove "$TARGET" 2>/dev/null || true
  git -C "$ROOT" branch -D "$BRANCH" 2>/dev/null || true
  exit 1
fi

echo "Symlinking .lake/packages from source worktree (avoids re-fetching Mathlib, saves ~2 GB per worktree)..." >&2
mkdir -p "$TARGET/.lake"
ln -s "$ROOT/.lake/packages" "$TARGET/.lake/packages"

# By default, give the new worktree its own .lake/build/ as a real directory
# inside the worktree. Set LAKE_BUILD_TMPDIR (e.g. =/tmp/lake-builds) to
# redirect to a faster location instead — useful when the worktree itself
# sits on slow shared storage (NFS) and a local SSD is available. The
# previous behavior of `cp -r` from $ROOT's build dir is unsafe when $ROOT
# itself uses LAKE_BUILD_TMPDIR (cp follows the symlink and produces a
# copy that races with the master), so we never copy by default — rely on
# Mathlib cache-replay for cold builds, which is fast.
if [[ -n "${LAKE_BUILD_TMPDIR-}" ]]; then
  TARGET_BUILD="$LAKE_BUILD_TMPDIR/Asymptotic-Statistics-$NAME"
  echo "LAKE_BUILD_TMPDIR set; symlinking .lake/build to $TARGET_BUILD..." >&2
  mkdir -p "$TARGET_BUILD"
  ln -s "$TARGET_BUILD" "$TARGET/.lake/build"
else
  echo "Creating .lake/build/ inside worktree (set LAKE_BUILD_TMPDIR to redirect to fast storage)..." >&2
  mkdir -p "$TARGET/.lake/build"
fi

# Warm up Mathlib oleans into OS page cache so the first user-facing
# check.sh call in this worktree starts warm (~8s) rather than cold (~50s).
# This costs ~30-50s once at spawn, paid by the manager (not by the user-
# facing subagent doing real work). Skipped if check.sh isn't present.
if [[ -x "$TARGET/tools/check.sh" ]]; then
  echo "Warming up Mathlib oleans into OS page cache (one-time, ~30-50s)..." >&2
  ( cd "$TARGET" && ./tools/check.sh 'Nat.add' >/dev/null 2>&1 ) || true
  echo "Warm-up done; subsequent check.sh in this worktree should be warm (~8s)." >&2
fi

cat <<EOF

Worktree ready.
  path:   $TARGET
  branch: $BRANCH

Next step (paste into the worker prompt):
  cd $TARGET

Tear down when done:
  git worktree remove $TARGET
  git branch -D $BRANCH
EOF
