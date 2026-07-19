# Close the 4 sorries in PointEstimation/ForMathlib/MGFUniqueness.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.ForMathlib.MGFUniqueness` and read its output directly. **Never** background the build, never wrap it in `srun`/`sbatch`, never poll with `until pgrep` — you are already inside the allocation and a nested job will hang this session.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/ForMathlib/MGFUniqueness.lean`. Touch nothing else.
- **Signatures, hypothesis tags, and docstrings are FROZEN.** You may add `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors** in that file. Escape hatch: if one statement resists, leave exactly one lifted `private` sorry with a `-- TODO:` explaining precisely what is missing, and report it.
- **Do not weaken any statement.** If you become convinced a statement is false as written, STOP, leave it sorried, and report the counterexample — that is a success, not a failure.
- Commit after each lemma compiles, so work is banked if the session is preempted.
- After the file is green: run `#print axioms ext_of_integral_exp_eqOn` and `#print axioms ae_eq_zero_of_integral_exp_smul_eq_zero`; both must show only `propext, Classical.choice, Quot.sound`.

## What to prove

Two public results plus two private helpers. This is the load-bearing brick for exponential-family completeness, so correctness matters more than elegance.

1. `integral_exp_tilted_mul` (private) — the tilted-measure mgf identity.
2. `eqOn_complexMGF_of_mgf_eqOn` (private) — a **local** `Set.EqOn` variant of Mathlib's `eqOn_complexMGF_of_mgf`. Mathlib's version demands *global* mgf equality, which we do not have; this is exactly why the helper exists.
3. `ext_of_integral_exp_eqOn` — two finite measures on `ℝ` whose Laplace transforms agree on a set `S` with `(interior S).Nonempty` are equal.
4. `ae_eq_zero_of_integral_exp_smul_eq_zero` — the signed corollary.

## Recommended route (verified to exist at this pin)

For (3): pick `η₀ ∈ interior S`. Tilt both measures by `exp (η₀ * ·)` using `Measure.tilted`; the tilts are finite and their mgfs agree on a neighbourhood of `0`, so `0 ∈ interior (integrableExpSet …)` for both. Then `analyticOnNhd_complexMGF` gives analyticity on the vertical strip containing the imaginary axis; the identity theorem propagates equality of `complexMGF` from the real interval to the whole strip; restricting to the imaginary axis gives equality of `charFun`; conclude with `Measure.ext_of_charFun`. Finally undo the tilt with `withDensity_inv_same` (the tilting density is strictly positive, so this is invertible).

For (4): split `f = f⁺ - f⁻`, apply (3) to the two finite measures `ν.withDensity (ofReal ∘ f⁺)` and `ν.withDensity (ofReal ∘ f⁻)`, then conclude `f =ᵐ[ν] 0` from equality of those measures.

Useful names, all verified present at this pin: `Measure.tilted`, `tilted_tilted`, `integral_tilted`, `isProbabilityMeasure_tilted`, `integrableExpSet`, `convex_integrableExpSet`, `complexMGF`, `analyticOnNhd_complexMGF`, `eqOn_complexMGF_of_mgf`, `Measure.ext_of_complexMGF_eq`, `Measure.ext_of_charFun`, `withDensity_inv_same`, `withDensity_eq_iff_of_sigmaFinite`.

## Report

Final `lake build` status line, the sorry count in the file, and the two `#print axioms` outputs. If you left a lifted sorry, say exactly which statement and why.
