#!/usr/bin/env bash
# explore.sh — semantic / natural-language search over Mathlib via the
# LeanExplore web service (https://www.leanexplore.com).
#
# Complements loogle.sh: loogle searches by *type shape* / name substring;
# explore searches by *concept* / informal description ("Cauchy-Schwarz for
# L² integrals", "score function has zero mean").  This is the CLI analogue
# of `#leansearch` / `#moogle` in a scratch .lean file — same query style,
# no scratch file needed.
#
# Usage:
#   ./tools/explore.sh "Cauchy-Schwarz for L² integrals"
#   ./tools/explore.sh "score function has zero expectation"
#   LEANEXPLORE_LIMIT=20 ./tools/explore.sh "central limit theorem iid"
#
# Setup (one-time, per machine):
#   1. Register at https://www.leanexplore.com to get a free API key.
#   2. export LEANEXPLORE_API_KEY=...   (e.g. in ~/.bashrc / ~/.zshrc)
#
# Unlike loogle.sh, this tool is NOT zero-setup — the LeanExplore API
# requires Bearer-token auth.  On a fresh machine the script will exit
# with a clear setup hint.
#
# Deps: curl, python3 (both preinstalled on most systems).

set -euo pipefail

if [[ $# -lt 1 ]]; then
  cat >&2 <<EOF
Usage: $0 '<natural-language query>'

Examples:
  $0 'Cauchy-Schwarz for L² integrals'
  $0 'central limit theorem for iid sequence'
  $0 'score function has zero expectation'

Set LEANEXPLORE_LIMIT=N to change the default 15-result cap.
Set LEANEXPLORE_PACKAGES="Mathlib,Std" to filter by package.
EOF
  exit 1
fi

if [[ -z "${LEANEXPLORE_API_KEY:-}" ]]; then
  cat >&2 <<EOF
LEANEXPLORE_API_KEY is not set.

LeanExplore requires a free API key:
  1. Register at https://www.leanexplore.com
  2. export LEANEXPLORE_API_KEY=...   (add to ~/.bashrc or ~/.zshrc)

Alternative: use ./tools/loogle.sh for type-shape / name-substring search,
or '#leansearch' / '#moogle' in a scratch .lean file for the same kind of
semantic search this script provides.
EOF
  exit 2
fi

QUERY="$1"
LIMIT="${LEANEXPLORE_LIMIT:-15}"

CURL_ARGS=(
  -s --max-time 20 -G
  -H "Authorization: Bearer ${LEANEXPLORE_API_KEY}"
  --data-urlencode "q=${QUERY}"
  --data-urlencode "limit=${LIMIT}"
)

if [[ -n "${LEANEXPLORE_PACKAGES:-}" ]]; then
  # API takes repeated `packages` query params, one per package.
  IFS=',' read -ra PKGS <<< "${LEANEXPLORE_PACKAGES}"
  for pkg in "${PKGS[@]}"; do
    CURL_ARGS+=(--data-urlencode "packages=${pkg}")
  done
fi

# Capture body and HTTP status separately so we can distinguish
# auth (401) and rate-limit (429) errors from real result payloads.
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT
HTTP_CODE="$(curl "${CURL_ARGS[@]}" -o "$TMP" -w "%{http_code}" \
  "https://www.leanexplore.com/api/v2/search")"
RESPONSE="$(cat "$TMP")"

case "$HTTP_CODE" in
  200) ;;
  401)
    echo "LeanExplore: 401 Unauthorized — check LEANEXPLORE_API_KEY." >&2
    exit 2 ;;
  429)
    echo "LeanExplore: 429 Rate limit exceeded — try again later." >&2
    exit 2 ;;
  *)
    echo "LeanExplore: HTTP $HTTP_CODE" >&2
    echo "$RESPONSE" >&2
    exit 2 ;;
esac

echo "$RESPONSE" | LIMIT="$LIMIT" python3 -c '
import json, os, sys

resp = json.load(sys.stdin)
limit = int(os.environ.get("LIMIT", "15"))

if "msg" in resp and "results" not in resp:
    err = resp["msg"]
    print(f"LeanExplore error: {err}", file=sys.stderr)
    sys.exit(2)

results = resp.get("results", [])
count = resp.get("count", len(results))
elapsed = resp.get("processing_time_ms")
suffix = f" ({elapsed} ms)" if elapsed is not None else ""
print(f"LeanExplore: {count} hit(s){suffix}, showing first {limit}",
      file=sys.stderr)

def extract_signature(src_text):
    """Return the first declaration line in source_text, skipping any
    leading /-- ... -/ docstring block (possibly multi-line)."""
    in_doc = False
    for line in src_text.splitlines():
        s = line.strip()
        if not s:
            continue
        if not in_doc and s.startswith("/--"):
            # one-line docstring: /-- ... -/
            if s.endswith("-/") and len(s) > 3:
                continue
            in_doc = True
            continue
        if in_doc:
            if "-/" in s:
                in_doc = False
            continue
        return s
    return ""

for hit in results[:limit]:
    name = hit.get("name", "?")
    module = hit.get("module", "?")
    src_text = hit.get("source_text") or ""
    sig = extract_signature(src_text)
    doc = (hit.get("docstring") or "").strip().splitlines()
    doc_first = doc[0] if doc else ""
    print(f"{name}")
    if sig:
        print(f"  {sig}")
    if doc_first:
        print(f"  -- {doc_first}")
    print(f"  -- {module}\n")
'
