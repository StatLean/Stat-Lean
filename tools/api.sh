#!/usr/bin/env bash
# api.sh — list the public declarations in a Lean file.
#
# Usage:
#   ./tools/api.sh StatLean/AsymptoticStatistics/DQM/Properties.lean
#
# Output: one line per top-level declaration, showing line number, kind
# (theorem / lemma / def / structure / instance / …), and name.
#
# Intended for quick orientation when re-entering a file — not a full type
# signature dump. For signatures, open the file at the reported line, or use
# `tools/check.sh '<Namespace.name>'`.
#
# Pure grep/sed; zero external deps beyond what ships with macOS/Linux.

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <lean-file>" >&2
  exit 1
fi

FILE="$1"
if [[ ! -f "$FILE" ]]; then
  echo "Not a file: $FILE" >&2
  exit 1
fi

# Keyword list, in the order we want to recognise them. `noncomputable def`
# must come before `def` because the alternation is matched left-to-right.
# Require a named identifier after the keyword; this skips anonymous instances
# like `instance {M : ...} : CoeFun ...` which are not part of the "public API"
# in the orientation sense this tool is for.
PATTERN='^(noncomputable def|theorem|lemma|def|structure|instance|class|abbrev|inductive)[ ]+[A-Za-z_]'

if ! grep -qE "$PATTERN" "$FILE"; then
  echo "No top-level declarations found in $FILE" >&2
  exit 0
fi

grep -nE "$PATTERN" "$FILE" |
  sed -E 's/^([0-9]+):(noncomputable def|theorem|lemma|def|structure|instance|class|abbrev|inductive) +([A-Za-z_][A-Za-z0-9_\.«»]*).*/L\1|\2|\3/' |
  awk -F'|' '
    {
      printf "  L%-5s  %-20s  %s\n", substr($1, 2), $2, $3
    }
  '
