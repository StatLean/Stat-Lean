#!/usr/bin/env bash
# find.sh — fast Mathlib declaration text-search.
#
# Replaces ~95% of `check.sh` use cases at ~270× speed and ~626× less RAM:
# - check.sh:  8-50s, 5 GB RSS  (full `import Mathlib`)
# - find.sh:   0.3s, 8 MB RSS   (ripgrep on .lake/packages/mathlib/)
#
# Usage:
#   ./tools/find.sh 'Filter.liminf_le_liminf'
#   ./tools/find.sh 'IsTightMeasureSet.map'
#   ./tools/find.sh 'lintegral_liminf_le'
#
# What you get: source-code form of the declaration (signature + first
# few lines after the colon). Universe variables are NOT shown explicitly
# (they are `Type*` in source); typeclass instances NOT pre-elaborated
# (e.g. `Filter.IsBoundedUnder (fun x1 x2 => x1 ≥ x2)` becomes `(· ≥ ·)`).
#
# When to use check.sh INSTEAD (the 5% cases):
# - You need fully elaborated type with universe / instance args explicit
# - You need to verify typeclass inference fires (e.g. `[Inhabited α]`
#   is auto-derived for your specific `α`)
# - You need to check a notation reverse-lookup (`⟪x, y⟫` → which lemma)
# - The query name involves complex anonymous instances
#
# Falls back to a "namespace block" search if the literal name is not
# found at top level (handles `namespace Foo / theorem bar : ...` cases
# where the full name is `Foo.bar` but source says `theorem bar`).

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 '<Lean.qualified.name>'" >&2
  echo "Example: $0 'Filter.liminf_le_liminf'" >&2
  exit 1
fi

QUERY="$1"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MATHLIB_DIR="$ROOT/.lake/packages/mathlib/Mathlib"

if [[ ! -d "$MATHLIB_DIR" ]]; then
  echo "Mathlib source not found at $MATHLIB_DIR" >&2
  echo "Run 'lake exe cache get' or 'lake build' first." >&2
  exit 1
fi

# Escape dots in the query for regex
QUERY_ESCAPED="${QUERY//./\\.}"

# Last namespace component (e.g. "map" from "IsTightMeasureSet.map")
LAST="${QUERY##*.}"

# Everything before the last component (parent namespace)
PARENT="${QUERY%.*}"
if [[ "$PARENT" == "$QUERY" ]]; then
  PARENT=""
fi

# Pattern (a): the full name appears explicitly in source.
#   theorem Filter.liminf_le_liminf ...
PATTERN_FULL="(theorem|lemma|def|instance|abbrev|noncomputable def) +${QUERY_ESCAPED}\b"

# Try pattern (a) first.
RESULT=$(rg -n -B 0 -A 5 --no-heading --max-count 3 "$PATTERN_FULL" "$MATHLIB_DIR" 2>/dev/null || true)

if [[ -n "$RESULT" ]]; then
  echo "$RESULT"
  exit 0
fi

# Pattern (b): the name is inside a `namespace <PARENT>` block, so source
# only writes `theorem <LAST>`. Find files that have BOTH `namespace <PARENT>`
# and `theorem <LAST>` near each other.
if [[ -n "$PARENT" ]]; then
  PARENT_ESCAPED="${PARENT//./\\.}"
  PATTERN_LAST="(theorem|lemma|def|instance|abbrev|noncomputable def) +${LAST}\b"

  # Get list of files containing `namespace <PARENT>`
  CANDIDATE_FILES=$(rg -l --no-heading "^namespace +${PARENT_ESCAPED}\b" "$MATHLIB_DIR" 2>/dev/null || true)

  if [[ -n "$CANDIDATE_FILES" ]]; then
    FOUND_ANY=""
    OUTPUT=""
    while IFS= read -r f; do
      [[ -z "$f" ]] && continue
      MATCH=$(rg -n -B 0 -A 5 --no-heading --max-count 1 "$PATTERN_LAST" "$f" 2>/dev/null || true)
      if [[ -n "$MATCH" ]]; then
        FOUND_ANY="1"
        OUTPUT+="$f"$'\n'"$MATCH"$'\n---\n'
      fi
    done <<< "$CANDIDATE_FILES"

    if [[ -n "$FOUND_ANY" ]]; then
      echo "[searching inside namespace $PARENT blocks...]"
      echo "$OUTPUT"
      exit 0
    fi
  fi
fi

# Pattern (c): give up — print a hint about the query and exit non-zero.
echo "Not found: $QUERY" >&2
echo "" >&2
echo "Tried:" >&2
echo "  (a) literal '$PATTERN_FULL' across $MATHLIB_DIR" >&2
if [[ -n "$PARENT" ]]; then
  echo "  (b) '$PATTERN_LAST' inside files with 'namespace $PARENT'" >&2
fi
echo "" >&2
echo "Suggested next step: try ./tools/check.sh '$QUERY' (slower but elaborated)" >&2
echo "  or ./tools/explore.sh '<concept>' for semantic search." >&2
exit 1
