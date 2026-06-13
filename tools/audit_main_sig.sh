#!/usr/bin/env bash
# tools/audit_main_sig.sh — semi-mechanical seven-check audit on a main theorem signature.
#
# USAGE:
#     tools/audit_main_sig.sh <milestone>
#
# Example:
#     tools/audit_main_sig.sh local_asymptotic_minimax
#     tools/audit_main_sig.sh asymptotic_representation
#
# Milestones are concept-named (matching the notes/<milestone>/ directory and
# the concept-named Lean file), NOT vdV book numbers.  Run with no argument to
# list the registered milestones.
#
# WHAT IT DOES:
#   1. Resolves <milestone> via the explicit registry below to
#      (Lean file, main theorem name, parser variant).
#   2. Locates the spec doc:   notes/<milestone>/vdv_book_reference.md
#   3. Extracts hypothesis names from BOTH and diffs them.
#   4. Runs Tier 0 mechanical checks (sorry / #print axioms hints).
#   5. Outputs a status summary to stdout.
#
# WHAT IT DOES NOT DO:
#   - Check (4) Conclusion vs book — needs human eyes.
#   - Check (7) joint consistency — needs human "exhibit a satisfying instance".
#   - Read the book for you.
#
# This is the *mechanical* part of the seven-check audit.  Human follow-up
# is still required to discharge the substantive checks; this just stops
# Manager / next-session agent from forgetting to look.
#
# Exit code:
#   0  — no mechanical drift detected (still need human follow-up for checks (4) and (7))
#   1  — mechanical drift detected (undocumented hypothesis on main signature, or known-drift still present)
#   2  — usage error / file not found

set -u

MILESTONE="${1:-}"

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$REPO_ROOT"

# ---------------------------------------------------------------------------
# Milestone registry — the ONLY lookup mechanism (book-number lookup removed
# 2026-06-11; milestones are addressed by concept name, matching the released
# branch convention).  One row per milestone:
#
#   LEAN_FILE  — concept-named Lean file holding the main theorem.
#   THM_NAME   — main theorem to audit (explicit; the "last theorem in file"
#                heuristic is gone — concept files carry corollaries/variants
#                after the main statement).  $MAIN_THM env var still overrides.
#   PARSER     — hypothesis-extraction variant:
#                * legacy:   the historical parser — `(`-only binders, ASCII
#                  names, stop at `:= by`.  Kept byte-for-byte because the
#                  pre-existing reference docs were calibrated to its exact
#                  output (incl. Unicode-truncation quirks like `h_ψDot_mat`
#                  → dropped).  Do NOT switch an old milestone to extended
#                  without re-calibrating its vdv_book_reference.md.
#                * extended: handles `{ }` binders, `_h…` underscore tags,
#                  non-ASCII names (`_hψ`, `_hℓ_sub`), multi-line `let`-block
#                  conclusions.  Count check gates the exit code.
#
# Add a new row when a milestone gets its vdv_book_reference.md.  New
# milestones should use PARSER=extended.
# ---------------------------------------------------------------------------

LEAN_FILE=""
THM_NAME=""
PARSER=""
case "$MILESTONE" in
  lan_expansion)                                                  # vdV Thm 7.2
    LEAN_FILE="StatLean/AsymptoticStatistics/LocalAsymptoticNormality/LANExpansion.lean"
    THM_NAME="LAN_expansion"
    PARSER="legacy"
    ;;
  asymptotic_representation)                                      # vdV Thm 7.10
    LEAN_FILE="StatLean/AsymptoticStatistics/LocalAsymptoticNormality/AsymptoticRepresentation.lean"
    THM_NAME="LAN_representation_vdV"
    PARSER="legacy"
    ;;
  lower_bound_for_experiments)                                    # vdV Thm 8.3
    LEAN_FILE="StatLean/AsymptoticStatistics/Efficiency/LowerBoundForExperiments.lean"
    THM_NAME="lower_bound_for_experiments"
    PARSER="legacy"
    ;;
  gaussian_shift_convolution)                                     # vdV Prop 8.4
    LEAN_FILE="StatLean/AsymptoticStatistics/Experiment/GaussianShiftConvolution.lean"
    THM_NAME="equivariant_in_law_convolution_decomposition"
    PARSER="legacy"
    ;;
  hajek_lecam_convolution)                                        # vdV Thm 8.8
    LEAN_FILE="StatLean/AsymptoticStatistics/Efficiency/HajekLeCamConvolution.lean"
    THM_NAME="hajek_le_cam_convolution_theorem"
    PARSER="legacy"
    ;;
  local_asymptotic_minimax)                                       # vdV Thm 8.11
    LEAN_FILE="StatLean/AsymptoticStatistics/Efficiency/LocalAsymptoticMinimax.lean"
    THM_NAME="local_asymptotic_minimax_bound"
    PARSER="legacy"
    ;;
  semiparametric_convolution)                                     # vdV Thm 25.20
    LEAN_FILE="StatLean/AsymptoticStatistics/LowerBounds/Convolution.lean"
    THM_NAME="semiparametric_convolution_theorem"
    PARSER="legacy"
    ;;
  semiparametric_lam)                                             # vdV Thm 25.21
    LEAN_FILE="StatLean/AsymptoticStatistics/LowerBounds/LAM.lean"
    THM_NAME="semiparametric_local_asymptotic_minimax_theorem"
    PARSER="extended"
    ;;
  *)
    echo "usage: $0 <milestone>" >&2
    echo "registered milestones:" >&2
    echo "  lan_expansion" >&2
    echo "  asymptotic_representation" >&2
    echo "  lower_bound_for_experiments" >&2
    echo "  gaussian_shift_convolution" >&2
    echo "  hajek_lecam_convolution" >&2
    echo "  local_asymptotic_minimax" >&2
    echo "  semiparametric_convolution" >&2
    echo "  semiparametric_lam" >&2
    [[ -n "$MILESTONE" ]] && echo "ERROR: unknown milestone '$MILESTONE'" >&2
    exit 2
    ;;
esac

if [[ ! -f "$LEAN_FILE" ]]; then
  echo "ERROR: registry points at missing Lean file: $LEAN_FILE" >&2
  echo "  (fix the registry row for '$MILESTONE' in $0)" >&2
  exit 2
fi

REF_FILE="notes/${MILESTONE}/vdv_book_reference.md"
if [[ ! -f "$REF_FILE" ]]; then
  echo "ERROR: reference spec not found: $REF_FILE" >&2
  echo "  (per-milestone spec doc required; see notes/local_asymptotic_minimax/vdv_book_reference.md for template)" >&2
  exit 2
fi

AUDIT_LOG="notes/${MILESTONE}/audit-log.md"

echo "=== Milestone ${MILESTONE} main-signature audit ==="
echo "Lean source:    $LEAN_FILE"
echo "Reference spec: $REF_FILE"
echo "Audit log:      $AUDIT_LOG"
echo ""

# ---------------------------------------------------------------------------
# The main theorem name comes from the registry (THM_NAME).  Still list ALL
# top-level theorems in the file so a human can spot a registry row that went
# stale after a refactor.
# ---------------------------------------------------------------------------

echo "--- Top-level theorems in this file ---"
grep -nE '^theorem [a-zA-Z_]' "$LEAN_FILE" | head -10
echo ""

# ---------------------------------------------------------------------------
# Extract hypothesis names from the Lean main signature.
#
# Convention (per hypothesis-discipline.md, post-2026-05-15):
# Lean source files no longer carry inline USER-INPUT / LEAN-ONLY tags on
# main theorem hypotheses; the canonical metadata lives in the reference
# spec doc.  We extract h-prefix parenthesized identifiers from the main
# theorem signature block.
# ---------------------------------------------------------------------------

echo "--- Hypothesis names (from Lean MAIN theorem signature only) ---"
# Identify the main theorem block.  Precedence: $MAIN_THM env var > registry
# THM_NAME (always set; the old last-`theorem`-in-file heuristic is gone).
MAIN_THM="${MAIN_THM:-$THM_NAME}"
echo "  (auditing theorem: $MAIN_THM — set \$MAIN_THM to override)"
# Hypothesis = a binder `(name : …)` / `{name : …}` whose name is `h`- or
# `_h`-prefixed (the project's two main-signature naming conventions: bare
# `hT_n` and underscore-tagged `_hCone`).  Data/object binders (`T_set`,
# `ψ`, `T_n`, `ℓ`, `IF_eff`) are intentionally excluded.
#
# Two extractors, selected by the registry's PARSER field:
#   * legacy: the historical parser — `(`-only, ASCII-name only, stop at
#     `:= by`.  Kept byte-for-byte so the pre-existing reference docs
#     (calibrated to this parser's exact output, including its
#     Unicode-truncation quirks like `h_ψDot_mat` → `h_`) keep diffing clean.
#   * extended: handles `{ }` binders, `_h…` underscore tags, non-ASCII names
#     (`_hψ`, `_hℓ_sub`), and a conclusion that is a multi-line `let …`-block
#     (stop at the conclusion `) :` line).  Required because e.g. LAM.lean's
#     hypotheses are nearly all `_h`-prefixed with Unicode in their names —
#     which the legacy parser silently drops.
if [[ "$PARSER" == "extended" ]]; then
  LEAN_HYPS=$(awk -v thm="$MAIN_THM" '
    $0 ~ "^theorem "thm"( |$)" { in_thm = 1; next }
    in_thm && /:= by/ { in_thm = 0; next }
    # Skip comment-only lines (a trailing-colon comment like `-- Loss:` must
    # NOT be mistaken for the conclusion colon).
    in_thm && /^[[:space:]]*--/ { next }
    # Conclusion-introducing colon: the last binder group closes with `)`/`}`
    # then a bare `:` ends the line (the conclusion is a multi-line `let …`).
    in_thm && /[)}][[:space:]]*:[[:space:]]*$/ { stop_after = 1 }
    in_thm {
      # The binder name is the run of characters after `(`/`{` up to the first
      # whitespace, `:`, comma, or bracket.  Non-ASCII letters are allowed
      # (`_hψ`, `_hℓ_sub`): the class is "not a terminator", not an ASCII set.
      line = $0
      # POSIX awk (no gawk 3-arg match): capture = whole match minus the
      # leading `(`/`{` + spaces, recovered via RSTART/RLENGTH + sub().
      while (match(line, /[({][[:space:]]*[^[:space:]:(){},]+/) > 0) {
        nm = substr(line, RSTART, RLENGTH)
        sub(/^[({][[:space:]]*/, "", nm)
        if ((substr(nm,1,1) == "h" && length(nm) > 1) || (substr(nm,1,2) == "_h" && length(nm) > 2))
          print nm
        line = substr(line, RSTART + RLENGTH)
      }
      if (stop_after) { in_thm = 0 }
    }
  ' "$LEAN_FILE" | sort -u)
else
  LEAN_HYPS=$(awk -v thm="$MAIN_THM" '
    $0 ~ "^theorem "thm"( |$)" { in_thm = 1; next }
    in_thm && /:= by/ { in_thm = 0; next }
    in_thm {
      # Extract identifier from EVERY opening paren on the line (multiple decls
      # per line are common in Lean signatures).
      # POSIX awk: identifier = whole match minus leading `(` + spaces.
      line = $0
      while (match(line, /\([[:space:]]*[a-zA-Z_][a-zA-Z_0-9]*/) > 0) {
        nm = substr(line, RSTART, RLENGTH)
        sub(/^\([[:space:]]*/, "", nm)
        if (nm != "" && substr(nm,1,1) == "h" && length(nm) > 1) print nm
        line = substr(line, RSTART + RLENGTH)
      }
    }
  ' "$LEAN_FILE" | sort -u)
fi
echo "$LEAN_HYPS"
LEAN_HYP_COUNT=$(printf '%s' "$LEAN_HYPS" | grep -c . || true)
echo "  (count: $LEAN_HYP_COUNT)"
echo ""

# ---------------------------------------------------------------------------
# Count documented ACTIVE-signature hypothesis ROWS in the reference doc.
#
# A "documented row" is a markdown table data row (`| … |`) inside an ACTIVE
# §A.* section (§A.1 vdV / §A.2 LEAN-ONLY / §A.3 current drift) that is neither
# the column-header row (`| Lean hypothesis | …`, in any of its variant forms)
# nor the `|---|---|` separator.  This is a structural count (one row == one
# documented active hypothesis), independent of the name-extraction heuristics
# below, so it works even when the doc uses descriptive identifiers
# (`_hTight tightness`, …) rather than the exact Lean binder names.  The doc is
# authored so that the active §A.1 table has exactly one row per Lean-signature
# hypothesis (the `_h`/`h`-prefixed binders the parser below extracts); data
# binders (`T_set`, `ψ`, `IF_eff`, `T_n`, `ℓ`) are folded into the row of their
# associated hypothesis, NOT given standalone rows.
#
# EXCLUDED sections (historical / non-hypothesis; must not inflate the count):
#   * "Original drift table …" / "Historical drift …" / "Historical … record"
#     (the §A.4 provenance tables of eliminated drift),
#   * "Derived (NOT hypotheses) …".
# Excluded section headers are matched at the SECTION level: once such a header
# is seen, `in_A` stays 0 until the next ACTIVE §A.* header.  (The §A.4 wrapper
# header itself is an §A.* header, so its `### §A.4a Historical drift table …`
# sub-header is what turns counting back off.)
# ---------------------------------------------------------------------------

REF_ROW_COUNT=$(awk '
  # Enter any §A.* section ("## A.", "### A.", "## §A.", "### §A.").
  /^#+[[:space:]]+(§)?A\./ { in_A = 1 }
  # Leave on any non-A "## …" / "### …" header, or on an excluded sub-table.
  /^#+[[:space:]]+(§)?[B-Z]\./                        { in_A = 0 }
  /^#+[[:space:]].*[Oo]riginal drift table/           { in_A = 0 }
  /^#+[[:space:]].*[Hh]istorical drift/               { in_A = 0 }
  /^#+[[:space:]].*[Dd]erived/                        { in_A = 0 }
  in_A && /^\|/ {
    # Skip any column-header row (`| Lean hypothesis …`, `| Historical hypothesis …`)
    # and the |---| / |:--:| separator row.
    if ($0 ~ /^\|[[:space:]]*[Ll]ean hypothesis/)      next
    if ($0 ~ /^\|[[:space:]]*[Hh]istorical hypothesis/) next
    if ($0 ~ /^\|[[:space:]]*-+[[:space:]]*\|/) next
    if ($0 ~ /^\|[[:space:]]*:?-+:?[[:space:]]*\|/) next
    cnt++
  }
  END { print cnt + 0 }
' "$REF_FILE")

echo "--- Count check: #signature-hyps vs #documented-rows (§A.1+§A.2+§A.3) ---"
echo "  Lean signature hypotheses:      $LEAN_HYP_COUNT"
echo "  Documented reference §A rows:   $REF_ROW_COUNT"
if [[ "$LEAN_HYP_COUNT" -eq "$REF_ROW_COUNT" ]]; then
  echo "  Count check: PASS ✓  ($LEAN_HYP_COUNT == $REF_ROW_COUNT)"
  COUNT_FAIL=0
else
  echo "  Count check: FAIL ⚠  ($LEAN_HYP_COUNT != $REF_ROW_COUNT)"
  echo "    A mismatch means an undocumented signature hypothesis OR a documented"
  echo "    §A row with no matching hypothesis.  Reconcile $REF_FILE §A.1/§A.2/§A.3."
  COUNT_FAIL=1
fi
echo ""

# ---------------------------------------------------------------------------
# Extract hypothesis names from the reference doc.
#
# We expect each hypothesis to appear in a markdown table row as
# `| `hypothesis_name | ...` (backtick-quoted at start of cell).
# ---------------------------------------------------------------------------

echo "--- Hypothesis names (from reference spec §A, ACTIVE sections only) ---"
# Only extract identifiers from ACTIVE Section A table rows (skip §B definitions /
# §C theorems, and skip the §A.4 historical drift record).  Headers may be `§`-
# prefixed (`## §A.1`).  Rows may contain multiple decls in one backtick block,
# e.g. `L : 𝓨 → ℝ≥0∞; hL_bowl : BowlShaped L` — extract ALL h-prefix identifiers
# from the first cell of each row.
#
# Two extractors, paired with the two Lean-side extractors above (selected by
# the registry's PARSER field):
#   * legacy: byte-for-byte the historical parser — bare `h…`, ASCII-only ident
#     chars.  Kept so the pre-existing docs (calibrated to the legacy Lean
#     parser's exact output, including its Unicode-truncation quirks like
#     `h_ψDot_mat` → `h_`) keep diffing clean.
#   * extended: allows an optional leading `_` (`_hCone`) and Unicode in the
#     identifier body (`_hℓ_sub`, `_hψ`) — matching the extended Lean parser, so
#     underscore/Unicode binders diff cleanly instead of being silently dropped
#     to `_h`.
if [[ "$PARSER" == "extended" ]]; then
  REF_HYPS=$(awk '
    /^#+[[:space:]]+(§)?A\./              { in_A = 1 }
    /^#+[[:space:]]+(§)?[B-Z]\./          { in_A = 0 }
    /^#+[[:space:]].*[Hh]istorical drift/ { in_A = 0 }
    in_A && /^\| `/ {
      line = $0
      gsub(/\\\|/, "@@PIPE@@", line)
      sub(/^\|[[:space:]]*/, "", line)
      cell = line
      sub(/[[:space:]]*\|.*/, "", cell)
      while (match(cell, /`[^`]*`/) > 0) {
        btblock = substr(cell, RSTART+1, RLENGTH-2)
        cell    = substr(cell, RSTART + RLENGTH)
        # ident = optional `_`, `h`, then a run of NON-terminator chars
        # (terminators: whitespace, : , ; ( ) { } and backtick) — allows Unicode.
        # POSIX awk: the leading separator char (never `_`/`h`, which the ident
        # starts with) is stripped from the whole match via sub().
        while (match(btblock, /(^|[^[:alnum:]_])(_?h[^[:space:]:,;(){}`]*)/) > 0) {
          nm = substr(btblock, RSTART, RLENGTH)
          sub(/^[^_h]/, "", nm)
          if (nm != "h" && nm != "_h") print nm
          btblock = substr(btblock, RSTART + RLENGTH)
        }
      }
    }
  ' "$REF_FILE" | sort -u)
else
  REF_HYPS=$(awk '
    /^## A\./ || /^### A\./ { in_A = 1 }
    /^## [B-Z]\./ { in_A = 0 }
    in_A && /^\| `/ {
      line = $0
      gsub(/\\\|/, "@@PIPE@@", line)
      sub(/^\|[[:space:]]*/, "", line)
      cell = line
      sub(/[[:space:]]*\|.*/, "", cell)
      while (match(cell, /`[^`]*`/) > 0) {
        btblock = substr(cell, RSTART+1, RLENGTH-2)
        cell    = substr(cell, RSTART + RLENGTH)
        # POSIX awk: strip the leading separator char (never `h`) via sub().
        while (match(btblock, /(^|[^a-zA-Z_0-9])(h[a-zA-Z_0-9]*)/) > 0) {
          nm = substr(btblock, RSTART, RLENGTH)
          sub(/^[^h]/, "", nm)
          if (nm != "h") print nm
          btblock = substr(btblock, RSTART + RLENGTH)
        }
      }
    }
  ' "$REF_FILE" | sort -u)
fi
echo "$REF_HYPS"
echo ""

# ---------------------------------------------------------------------------
# Diff: hypothesis names present in Lean but missing from reference (undocumented drift).
# ---------------------------------------------------------------------------

echo "--- Diff: in Lean signature but NOT in reference spec ---"
UNDOCUMENTED=$(comm -23 <(echo "$LEAN_HYPS") <(echo "$REF_HYPS"))
if [[ -z "$UNDOCUMENTED" ]]; then
  echo "  (none) ✓"
else
  echo "$UNDOCUMENTED" | sed 's/^/  ⚠ /'
fi
echo ""

# ---------------------------------------------------------------------------
# Diff: in reference but not in Lean (stale entries).
# ---------------------------------------------------------------------------

echo "--- Diff: in reference but NOT in Lean signature (stale entries) ---"
STALE=$(comm -13 <(echo "$LEAN_HYPS") <(echo "$REF_HYPS"))
if [[ -z "$STALE" ]]; then
  echo "  (none) ✓"
else
  echo "$STALE" | sed 's/^/  ⚠ /'
fi
echo ""

# ---------------------------------------------------------------------------
# Check for forbidden defences in reference doc (per hypothesis-discipline.md).
# The "implicit" word + similar passcode phrases are forbidden in §A rows.
# ---------------------------------------------------------------------------

echo "--- Forbidden defences in reference §A.1 rows (USER-INPUT only; §A.2 LEAN-ONLY allowed) ---"
# Restrict to §A.1 (USER-INPUT hypotheses, where "implicit"-defence is forbidden).
# §A.2 LEAN-ONLY rows legitimately use "implicit" to describe encoding artefacts.
# Also strip double-quoted spans before checking, so disclaimer text like
#   (which bans "implicit" / "by analogy" defences)
# does not false-trigger when discussing the rule itself.
IMPLICIT_HITS=$(awk '
  /^#+[[:space:]]+(§)?A\.1/             { in_A1 = 1; next }
  /^#+[[:space:]]+(§)?A\.[2-9]/         { in_A1 = 0 }
  /^#+[[:space:]]+(§)?[B-Z]\./          { in_A1 = 0 }
  in_A1 && /^\| `h/ {
    line = $0
    gsub(/"[^"]*"/, "", line)        # strip "..."-quoted meta-discussion
    if (line ~ /implicit/ || line ~ /by analogy/ || line ~ /book is informal/) {
      print NR": "$0
    }
  }
' "$REF_FILE" || true)
if [[ -z "$IMPLICIT_HITS" ]]; then
  echo "  (none) ✓"
else
  echo "$IMPLICIT_HITS" | sed 's/^/  ⚠ /'
fi
echo ""

# ---------------------------------------------------------------------------
# Mechanical check (1): stray sorry in the Lean file.
# ---------------------------------------------------------------------------

echo "--- Check (1): stray sorry in main theorem file ---"
SORRY_COUNT=$(grep -c "sorry" "$LEAN_FILE" 2>/dev/null || true)
echo "  Sorry occurrences in $LEAN_FILE: $SORRY_COUNT  (need to cross-check against documented inventory in status.md)"
echo ""

# ---------------------------------------------------------------------------
# Check whether reference doc marks any hypothesis as 'Drift'.
# ---------------------------------------------------------------------------

echo "--- Drift hypotheses still on main signature (per reference §A.3) ---"
# Look for rows in reference that mention "Drift" (status), and check if the named
# hypothesis is still in $LEAN_HYPS.
DRIFT_NAMES=$(awk '
  # Only inside the ACTIVE §A.3 drift section, and only rows explicitly
  # classified "Drift" (skip "Encoding").  The §A.4 historical record is NOT
  # the active signature, so it is excluded (matched via "Historical drift").
  /^#+[[:space:]]+(§)?A\.3/ { in_drift = 1; next }
  /^#+[[:space:]]+(§)?A\.[14-9]/ || /^#+[[:space:]]+(§)?[B-Z]\./ { in_drift = 0 }
  /^#+[[:space:]].*[Hh]istorical drift/ { in_drift = 0 }
  in_drift && /^\| `h/ && /[Dd]rift/ && !/[Ee]ncoding/ {
    # Extract first h-prefix identifier from the row (POSIX awk: backtick
    # block via RSTART/RLENGTH, separator stripped via sub()).
    if (match($0, /`[^`]*`/) > 0) {
      bt = substr($0, RSTART + 1, RLENGTH - 2)
      while (match(bt, /(^|[^a-zA-Z_0-9])(h[a-zA-Z_0-9]*)/) > 0) {
        nm = substr(bt, RSTART, RLENGTH)
        sub(/^[^h]/, "", nm)
        if (nm != "h") { print nm; break }
        bt = substr(bt, RSTART + RLENGTH)
      }
    }
  }
' "$REF_FILE" | sort -u)
STILL_PRESENT_DRIFT=""
for h in $DRIFT_NAMES; do
  if echo "$LEAN_HYPS" | grep -qx "$h"; then
    STILL_PRESENT_DRIFT="$STILL_PRESENT_DRIFT $h"
  fi
done
if [[ -z "$STILL_PRESENT_DRIFT" ]]; then
  echo "  (none) ✓"
else
  for h in $STILL_PRESENT_DRIFT; do
    echo "  ⚠ $h (marked Drift in reference, still on main signature — revert pending per option_c_plan.md or similar)"
  done
fi
echo ""

# ---------------------------------------------------------------------------
# Exit status.
# ---------------------------------------------------------------------------

FAIL=0
[[ -n "$UNDOCUMENTED" ]] && FAIL=1
[[ -n "$IMPLICIT_HITS" ]] && FAIL=1
[[ -n "$STILL_PRESENT_DRIFT" ]] && FAIL=1
# Count check gates the exit code ONLY for extended-parser milestones (e.g.
# semiparametric_lam).  For legacy-parser milestones the count line stays
# informational so their established PASS/FAIL verdict — driven by the
# name-diff — is unchanged.
[[ "$PARSER" == "extended" && "${COUNT_FAIL:-0}" -eq 1 ]] && FAIL=1

echo "=== Audit summary ==="
if [[ $FAIL -eq 0 ]]; then
  echo "Mechanical checks: PASS ✓"
  echo "  Still need human follow-up:"
  echo "    Check (4): conclusion vs book (read \$REF_FILE §A and compare)"
  echo "    Check (7): exhibit one ℓ / M / etc. satisfying full hypothesis conjunction"
  exit 0
else
  echo "Mechanical checks: FAIL ⚠"
  echo ""
  echo "Action: open $REF_FILE and reconcile (a) undocumented hypotheses,"
  echo "        (b) 'implicit' defences (must give page+line citation),"
  echo "        (c) drift hypotheses pending revert (per option_c_plan.md)."
  echo ""
  echo "After fixing, append a new entry to $AUDIT_LOG with the seven-check"
  echo "results.  Do not merge the wave until check (7) joint consistency"
  echo "is verified by a concrete instance witness."
  exit 1
fi
