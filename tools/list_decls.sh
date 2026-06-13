#!/usr/bin/env bash
# list_decls.sh — enumerate book-relevant non-theorem declarations
# (structure / def / noncomputable def / instance / class / abbrev /
# inductive) under our project layers, grouped by directory.
#
# Purpose: discoverability for the "have we cited vdV for every
# project-level mathematical object?" check.  Inline docstrings can be
# inspected per-decl via tools/where.sh, but you can't audit
# completeness without a central enumeration.  This is that enumeration.
#
# Default scope is the book-aligned layers — ParametricFamily/, DQM/,
# Ch7/, Ch8/.  ForMathlib/ is theorem-agnostic (no vdV citation
# expected); Experiment/ is WIP.  Pass --all to include them anyway.
#
# Usage:
#   ./tools/list_decls.sh                   # book-relevant scope
#   ./tools/list_decls.sh --all             # every layer
#   ./tools/list_decls.sh --in Ch8          # one sub-directory
#   ./tools/list_decls.sh --count           # only directory totals

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
BOOK_DIRS=(ParametricFamily DQM Ch7 Ch8)
ALL_DIRS=(ParametricFamily DQM ForMathlib Ch7 Ch8 Experiment)
KINDS=(structure class "noncomputable def" def abbrev inductive instance)

SCOPE_DIRS=("${BOOK_DIRS[@]}")
SUBDIR=""
COUNT_ONLY=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --all)    SCOPE_DIRS=("${ALL_DIRS[@]}"); shift ;;
    --in)     SUBDIR="${2:?--in needs a sub-directory}"; SCOPE_DIRS=("$SUBDIR"); shift 2 ;;
    --count)  COUNT_ONLY=1; shift ;;
    -h|--help)
      sed -n '2,/^set -euo/p' "$0" | sed 's/^# \{0,1\}//;s/^set -euo.*//' >&2
      exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 1 ;;
  esac
done

WHERE="$ROOT/tools/where.sh"
[[ -x "$WHERE" ]] || { echo "Missing $WHERE" >&2; exit 1; }

total=0
for dir in "${SCOPE_DIRS[@]}"; do
  [[ -d "$ROOT/StatLean/AsymptoticStatistics/$dir" ]] || continue
  block=""
  subtotal=0
  for k in "${KINDS[@]}"; do
    raw=$("$WHERE" --kind "$k" --in "$dir" "" 2>/dev/null || true)
    [[ -z "$raw" ]] && continue
    # Drop docstring false positives — where.sh's awk parser doesn't
    # recognize `/-! ... -/` module docstrings, so a line literally
    # ending in `-/` (e.g. "structure available ... -/") will be
    # mis-flagged.  Real declarations don't end in `-/`.
    out=""
    while IFS= read -r line; do
      [[ -z "$line" ]] && continue
      # Extract path:Lline from leading "  path:Lline  kind  name"
      rel_loc=$(echo "$line" | awk '{print $1}')
      path="${rel_loc%%:L*}"; lineno="${rel_loc##*:L}"
      content=$(sed -n "${lineno}p" "$ROOT/$path" 2>/dev/null || echo "")
      if [[ ! "$content" =~ -/[[:space:]]*$ ]]; then
        out+="$line"$'\n'
      fi
    done <<< "$raw"
    if [[ -n "$out" ]]; then
      block+="$out"
      n=$(printf '%s' "$out" | grep -c '.')
      subtotal=$((subtotal + n))
    fi
  done
  # Supplementary pass: anonymous `instance : Foo := ...` / `instance [H]`
  # / `instance {x}` / `instance (priority := n)` — where.sh's regex
  # requires a name-starting char so it misses these.  POSIX grep (not
  # rg — rg is sometimes a shell function wrapper on this host and isn't
  # inherited by subshells).  `[[:space:]]` filters the "instances"
  # prefix false-positive in lieu of a word boundary.
  anon=$(grep -rn -E "^instance[[:space:]]*([:[{(]|$)" \
           "$ROOT/StatLean/AsymptoticStatistics/$dir" --include='*.lean' 2>/dev/null || true)
  if [[ -n "$anon" ]]; then
    while IFS= read -r line; do
      path="${line%%:*}"; rest="${line#*:}"; lineno="${rest%%:*}"
      rel="${path#$ROOT/}"
      block+=$(printf '  %-50s  %-20s  %s\n' "$rel:L$lineno" "instance" "<anonymous>")$'\n'
      subtotal=$((subtotal + 1))
    done <<< "$anon"
  fi
  if [[ $subtotal -gt 0 ]]; then
    printf '=== %s/  (%d) ===\n' "$dir" "$subtotal"
    [[ $COUNT_ONLY -eq 1 ]] || printf '%s' "$block"
    echo ""
    total=$((total + subtotal))
  fi
done

printf 'total: %d declarations\n' "$total" >&2
