The file `StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean` on this branch has
`expectation_max_le` FULLY WRITTEN (no sorry) with helper lemmas, but a preemption killed the
session mid-edit and `lake build StatLean.ConcentrationInequalities.Maximal.FiniteMaximal` FAILS.
Fix ALL errors to a clean ZERO-error, ZERO-sorry build. Do NOT touch `tail_max_le`. Do NOT change
the `expectation_max_le` STATEMENT. Obey CLAUDE.md §7. Keep the proof approach (Jensen + optimize λ).

IMPORTANT: build with plain `lake build <target>` and ITERATE until 0 errors — do NOT submit an
async job and stop. The remaining errors are mostly Mathlib renames:
- `Filter.eventually_of_forall` → `Filter.Eventually.of_forall` (or `eventually_of_forall`) — check.
- `integral_mul_left` → `MeasureTheory.integral_const_mul` (or `integral_mul_left` in a different
  namespace) — `./tools/check.sh`.
- `le_div_iff` → `le_div_iff₀`.
- a `No goals to be solved` (drop the stray trailing tactic, §7.10).
- a few `Application type mismatch` / `Type mismatch` (wrong arg arity on `Finset.*`/`ciSup` helpers).

CURRENT BUILD ERRORS (from the latest gate):
- 112:10 Application type mismatch; 132:2 Type mismatch; 187:38 Application type mismatch;
  228 & 237 Unknown constant `Filter.eventually_of_forall`; 231 Unknown identifier `integral_mul_left`;
  263:18 No goals to be solved; 264:11 Unknown identifier `le_div_iff`.

EARLIER ERRORS (already partially addressed):
- line ~112: `Function expected at` + `Type mismatch` — likely a misplaced application / wrong
  argument arity in a helper (`exp_mul_ciSup_le_sum_exp` or the abs-bound helper). Inspect and fix.
- line ~132: `Function expected at` — same kind.
- line ~178: `Type mismatch`.
- line ~182: `Unknown identifier 'le_or_lt'` and a downstream `rcases` failure — replace with the
  correct Mathlib name: `le_or_lt a b : a ≤ b ∨ b < a` IS in Mathlib (check `./tools/check.sh 'le_or_lt'`);
  if the namespace differs use `lt_or_ge`/`le_or_lt` as found, or `rcases le_or_lt t α with h | h`.
  Make sure the `rcases` target is the `Or` so the two-regime case split works.

Re-read the existing proof, fix the broken applications/identifiers, and rebuild until ZERO errors.
If a helper lemma is structurally wrong, you may rewrite that helper (but keep
`expectation_max_le`'s statement intact).

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
# DONE = build exits 0, ZERO sorries (whole file). Commit
(`conc(maximal): fix expectation_max_le proof — E[max] ≤ σ√(2 log d) (Lu-BDA §4.2)`). Report build +
sorry count (must be 0).
