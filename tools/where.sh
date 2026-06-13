#!/usr/bin/env bash
# where.sh — find a declaration in *our* StatLean project by name
# (default) or by docstring text (--doc).
#
# Walks StatLean/**/*.lean looking at every top-level declaration. Prints
# `path:Lline  kind  name`, with the docstring's first line in --doc mode.
#
# Project-local complement to:
#   - loogle.sh  / explore.sh  — search Mathlib by type shape / concept
#   - check.sh                  — verify a known fully-qualified name
# Use this when you suspect *we* already have a lemma in our own code.
#
# Usage:
#   ./tools/where.sh score                       # name substring (case-insens.)
#   ./tools/where.sh --exact ScoreFunction       # exact local-name match
#   ./tools/where.sh --in AsymptoticStatistics/DQM residual   # only that subtree
#   ./tools/where.sh --kind theorem residual     # only theorems
#   ./tools/where.sh --doc 'Cauchy-Schwarz'      # docstring contains text
#
# For type signatures, take the result's name and run
#   ./tools/check.sh '<Namespace.name>'
# or open the file at the reported line.

set -euo pipefail

MODE="name"        # "name" or "doc"
EXACT=0
SUBDIR=""
KIND=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --doc)    MODE="doc"; shift ;;
    --exact)  EXACT=1; shift ;;
    --in)     SUBDIR="${2:?--in needs a sub-directory}"; shift 2 ;;
    --kind)   KIND="${2:?--kind needs a kind keyword}"; shift 2 ;;
    --) shift; break ;;
    -h|--help)
      sed -n '2,/^set -euo/p' "$0" | sed 's/^# \{0,1\}//;s/^set -euo.*//' >&2
      exit 0 ;;
    -*)
      echo "Unknown option: $1" >&2; exit 1 ;;
    *)
      break ;;
  esac
done

if [[ $# -lt 1 ]]; then
  cat >&2 <<EOF
Usage:
  $0 [--exact] [--in <subdir>] [--kind <kind>] <name-substring>
  $0 --doc [--in <subdir>] [--kind <kind>] <docstring-substring>

Run \`$0 --help\` for the full header. Searches StatLean/**/*.lean.
EOF
  exit 1
fi

QUERY="$1"

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
SEARCH_DIR="$ROOT/StatLean"
if [[ -n "$SUBDIR" ]]; then
  SEARCH_DIR="$SEARCH_DIR/$SUBDIR"
  [[ -d "$SEARCH_DIR" ]] || { echo "Not a directory: $SEARCH_DIR" >&2; exit 1; }
fi

# Same kind list as api.sh; "noncomputable def" must precede "def".
ALL_KINDS='noncomputable def|theorem|lemma|def|structure|instance|class|abbrev|inductive'
KIND_PAT="${KIND:-$ALL_KINDS}"

# Single awk pass per file.  Keeps a one-slot docstring buffer that is
# consumed by the next declaration.  Uses only POSIX-ish awk features
# (no 3-arg match capture groups) so it works on mawk / BSD awk too.
HITS=$(find "$SEARCH_DIR" -type f -name '*.lean' -print0 |
  xargs -0 awk \
    -v root="$ROOT/" \
    -v query="$QUERY" \
    -v mode="$MODE" \
    -v exact="$EXACT" \
    -v kind_pat="$KIND_PAT" \
    '
    BEGIN {
      decl_re  = "^(" kind_pat ")[ \t]+[A-Za-z_]"
      doc_open = "^[ \t]*/--"
      qlc      = tolower(query)
    }
    FNR == 1 { in_doc = 0; doc_first = "" }

    {
      line = $0

      if (!in_doc && line ~ doc_open) {
        in_doc    = 1
        doc_first = ""
        # One-line docstring:  /-- ... -/
        if (line ~ /-\/[ \t]*$/) {
          tmp = line
          sub(/^[ \t]*\/--[ \t]*/, "", tmp)
          sub(/[ \t]*-\/[ \t]*$/, "", tmp)
          doc_first = tmp
          in_doc    = 0
        } else {
          tmp = line; sub(/^[ \t]*\/--[ \t]*/, "", tmp)
          if (tmp ~ /[^ \t]/) doc_first = tmp
        }
        next
      }

      if (in_doc) {
        if (doc_first == "") {
          tmp = line; sub(/^[ \t]+/, "", tmp); sub(/[ \t]+$/, "", tmp)
          if (tmp != "") doc_first = tmp
        }
        if (index(line, "-/") > 0) in_doc = 0
        next
      }

      # Outside any docstring.  Reset doc_first when we hit a non-empty,
      # non-attribute line that is also not a declaration — that means the
      # docstring belonged to something else (rare in this project, but cheap).
      if (line !~ decl_re && line !~ /^[ \t]*$/ && line !~ /^[ \t]*@\[/) {
        doc_first = ""
      }

      if (line ~ decl_re) {
        n = split(line, parts, /[ \t]+/)
        if (parts[1] == "noncomputable" && parts[2] == "def") {
          kind = "noncomputable def"; name = parts[3]
        } else {
          kind = parts[1]; name = parts[2]
        }
        # Trim trailing punctuation: ( [ { : that bleed in from the signature.
        gsub(/[(\[{:].*$/, "", name)

        ok = 0
        if (mode == "doc") {
          if (doc_first != "" && index(tolower(doc_first), qlc) > 0) ok = 1
        } else if (exact == 1) {
          if (name == query) ok = 1
        } else {
          if (index(tolower(name), qlc) > 0) ok = 1
        }

        if (ok) {
          rel = FILENAME; sub(root, "", rel)
          if (mode == "doc") {
            printf "  %-50s  %-20s  %s\n    -- %s\n",
                   rel ":L" FNR, kind, name, doc_first
          } else {
            printf "  %-50s  %-20s  %s\n", rel ":L" FNR, kind, name
          }
        }
        doc_first = ""
      }
    }
    ' || true)

if [[ -z "$HITS" ]]; then
  echo "No matches in ${SEARCH_DIR#$ROOT/} for ${MODE}=${QUERY}" >&2
  exit 1
fi
echo "$HITS"
