# Close the sorries in PointEstimation/{ForMathlib/MGFUniquenessPi,Completeness/ExpFamily}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read the repo `CLAUDE.md` first). Pin `v4.29.1`.

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.ForMathlib.MGFUniquenessPi` then `lake build StatLean.PointEstimation.Completeness.ExpFamily`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/ForMathlib/MGFUniquenessPi.lean` and `StatLean/PointEstimation/Completeness/ExpFamily.lean`. Touch nothing else — in particular NOT `Completeness/Defs.lean` or `ExponentialFamily/Defs.lean` (frozen, laptop-only).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import the already-proved `StatLean.PointEstimation.ForMathlib.MGFUniqueness`, and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a `-- TODO:`; report it.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms isCompleteStat_of_interior_nonempty` and `#print axioms ext_of_integral_exp_inner_eqOn` — expect only `propext, Classical.choice, Quot.sound`.

## This is the load-bearing item of the batch

Exponential-family completeness is consumed by Lehmann–Scheffé (Cor 1.12), the normal linear model, and the whole Batch-12 UMPU/similarity layer. Correctness matters far more than elegance.

## Already available (proved, treat as black boxes)

`StatLean.PointEstimation.ForMathlib.MGFUniqueness` is **closed and axiom-clean**:
- `ext_of_integral_exp_eqOn` — finite measures on `ℝ` with equal Laplace transforms on a set with nonempty interior are equal.
- `ae_eq_zero_of_integral_exp_smul_eq_zero` — the signed corollary.

Its proof route (worth imitating for the s-dim case): tilt at an interior point so `0 ∈ interior (integrableExpSet …)`; use the *local* `Set.EqOn` variant of the complex-mgf identity theorem seeded from an interior point via `interior_maximal`, with preconnectedness of the strip from `Convex.inter` / `.linear_preimage Complex.reLm`; restrict to the imaginary axis with `complexMGF_id_mul_I` to reach `charFun`; finish with `Measure.ext_of_charFun`; untilt with `withDensity_inv_same`.

## What to prove

1. `ext_of_integral_exp_inner_eqOn` / `ae_eq_zero_of_integral_exp_inner_eq_zero` (MGFUniquenessPi) — the same statements on `EuclideanSpace ℝ (Fin s)` with `⟪t, x⟫_ℝ`. Recommended route: reduce to the 1-D result **one coordinate at a time**, or via the one-dimensional marginals along a spanning set of directions. The in-repo files `AsymptoticStatistics/ForMathlib/BivariateMGFUniqueness.lean` and `MultivariateComplexMGFCoeff.lean` have done this shape twice — read them for the induction pattern (do not import if not needed).
2. `isCompleteStat_of_interior_nonempty` (Completeness/ExpFamily) — for `Ξ' ⊆ E.natSet` with `(interior Ξ').Nonempty`, the family of laws of `E.stat` is complete. This is exactly the signed corollary applied to the law of `T` under the tilts: `∫ f d((E.P θ).map E.stat) = 0` for all `θ ∈ Ξ'` unfolds to a vanishing Laplace transform of `f · (density of T#base)` on a set with nonempty interior.
3. `isCompleteStat_of_interior_nonempty_real` — the `V := ℝ` specialization.

Note the deliberate asymmetry, and do not try to "fix" it: **Thm 6.22 needs only nonempty interior** — no full-rank, no nondegeneracy — because the conclusion is an a.e. statement about the law of `T`.

## Report

Final `lake build` status for both modules, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false.
