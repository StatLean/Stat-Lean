#!/usr/bin/env bash
# loogle.sh — pattern-search Mathlib via the public Loogle web service.
#
# Usage:
#   ./tools/loogle.sh '?a + ?b ≤ _'
#   ./tools/loogle.sh 'Real.sqrt ?x'
#   ./tools/loogle.sh '"sqrt_add"'        # quoted: name substring match
#   ./tools/loogle.sh '_ * _ < _ * _'
#
# Prints matching lemmas as `name : type` on stdout, one per line,
# with the module path as a `-- module` suffix comment.
#
# Deps: curl, python3 (both preinstalled on most systems).
# Portability: zero machine-local state — any machine that clones the repo has
# this script. Only needs network access to loogle.lean-lang.org.

set -euo pipefail

if [[ $# -lt 1 ]]; then
  cat >&2 <<EOF
Usage: $0 '<Loogle pattern>'

Pattern forms:
  Real.sqrt ?x         — lemmas mentioning Real.sqrt applied to something
  ?a + ?b ≤ _          — any lemma whose statement fits this shape
  "substring"          — name substring search (quotes inside the arg)
  _ * _ < _ * _        — holes (_) match any term

See https://loogle.lean-lang.org for the full pattern syntax.
EOF
  exit 1
fi

PATTERN="$1"
LIMIT="${LOOGLE_LIMIT:-15}"

RESPONSE="$(curl -s --max-time 15 -G \
  --data-urlencode "q=$PATTERN" \
  "https://loogle.lean-lang.org/json")"

# Format via Python (portable; no jq dependency).  Bash heredoc would steal
# stdin from the pipe, so the script is passed via `-c` instead.
echo "$RESPONSE" | LIMIT="$LIMIT" python3 -c '
import json, os, sys

resp = json.load(sys.stdin)
limit = int(os.environ.get("LIMIT", "15"))

if "error" in resp:
    err = resp["error"]
    print(f"Loogle error: {err}", file=sys.stderr)
    for s in resp.get("suggestions", []):
        print(f"  {s}", file=sys.stderr)
    sys.exit(2)

hits = resp.get("hits", [])
count = resp.get("count", len(hits))
print(f"Loogle: {count} hit(s), showing first {limit}", file=sys.stderr)

for hit in hits[:limit]:
    name = hit.get("name", "?")
    type_ = hit.get("type", "?")
    module = hit.get("module", "?")
    print(f"{name} :{type_}")
    print(f"  -- {module}\n")
'
