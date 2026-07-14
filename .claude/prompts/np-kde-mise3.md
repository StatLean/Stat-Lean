# FIX: 3 compile errors in NonparametricStatistics/KernelDensity/ExactMISE.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.KernelDensity.ExactMISE` (no `srun`).

The file currently FAILS to build with exactly:
- `ExactMISE.lean:257:66: No goals to be solved`
- `ExactMISE.lean:273:42: linarith failed to find a contradiction`
- `ExactMISE.lean:278:62: Application type mismatch`
(MISEVariance.lean and MISEBias.lean build 0-sorry — do NOT touch them.)

Almost certainly the assembly proof drifted against the (recently completed) MISEBias
internals. Repair the PROOFS around those lines — typical fixes: delete a now-redundant
tactic after something got auto-closed; strengthen the `linarith` hint set
(`nlinarith [ ... ]` with the nearby `have`s); adjust an argument to the changed
lemma signature (read the lemma it applies and match). Keep the THEOREM statements
(`kdeMise_eq_integrated`, `kde_exact_mise`) and all tags/docstrings UNCHANGED; private
helpers may be adjusted.

- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/ExactMISE.lean`.
- Goal: **0 errors, 0 sorries** in the module. Foreground `lake build` only. Commit when green.
- After green: `#print axioms StatLean.NonparametricStatistics.kde_exact_mise` → only
  `propext, Classical.choice, Quot.sound`.

Report final `lake build` status + the axioms line.
