# Close the remaining sorries in PointEstimation/LinearModel/{Canonical,LeastSquares,Equivariant,RandomDesign}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.LinearModel.Canonical`, then `.LeastSquares`, `.Equivariant`, `.RandomDesign`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** those four files. Touch nothing else — NOT `LinearModel/Defs.lean`, and NOT `GaussMarkov.lean` (already 0-sorry — leave it alone).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import already-closed project modules, and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**, except the one sanctioned deferral below. Escape hatch elsewhere: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms isUMVU_lse_functional`, `#print axioms isUMVU_residual_variance` — expect only `propext, Classical.choice, Quot.sound`.

## This is a second pass

An earlier session closed `GaussMarkov` completely (Thm 4.12 + Cor 4.13, pure projection geometry) and several `RandomDesign` / `Equivariant` helpers (`designMean_mem_designSpace`, `injective_designMean`, `designMean_lseCoeff` via the normal equations, `residualScaleConst_one` via chi-square moments). **Roughly 15 sorries remain**, concentrated in the completeness/transport machinery. Read each file's existing TODO comments first — they record where the previous session stopped and why.

## Already closed, treat as black boxes (import them)

- **`Completeness.ExpFamily.isCompleteStat_of_interior_nonempty`** — exponential-family completeness (Thm 6.22), axiom-clean. **This is the intended engine for `canonicalStat_isCompleteStat`.**
- `Sufficiency.Factorization.{isSufficient_of_isFactorizedDensity, isFactorizedDensity_of_isSufficient}` and `Sufficiency.RegularConditional.hasSufficientKernel_of_isSufficient_dominated` — for `canonicalStat_hasSufficientKernel`.
- `UMVU.LehmannScheffe.{unique_unbiased_function_of_complete, isUMVU_of_complete_sufficient, risk_le_of_complete_sufficient}` — the UMVU conclusions route through these.
- `ExponentialFamily.{Basic,MGF,NaturalStatistic}` — fully closed, including `P_eq_withDensity` and `map_stat_P`.
- Elsewhere: `AsymptoticStatistics.ForMathlib.PiGaussian.pi_gaussianReal_eq_withDensity`; `MultipleTesting.ForMathlib.ChiSquared` (`chiSquared`, `map_sum_sq_eq_chiSquared`, `integral_id_chiSquared`, `variance_chiSquared`); Mathlib's `stdGaussian_eq_map_pi_orthonormalBasis`.

## The key step, and where the last session stalled

`canonicalStat_isCompleteStat` is the hinge — everything else in `Canonical` and most of `LeastSquares` reduces to it. The route:

1. Write the canonical model's joint density via `pi_gaussianReal_eq_withDensity`.
2. Recognise it as a **canonical exponential family** with natural statistic
   `T y = (y₀, …, y_{s−1}, Σ_{j ≥ s} y_j²)` and natural parameter
   `η = (η₁/σ², …, η_s/σ², −1/(2σ²))`. Build the `ExpFamily` via `ExpFamily.ofDensity`
   and prove `IsCanonicalRepr` for the model.
3. The parameter set has **nonempty interior** in `ℝ^{s+1}` (that is exactly what
   `PosVar` and free `η` give you), so `isCompleteStat_of_interior_nonempty` applies.

For `LeastSquares`, transport to the canonical case by an orthonormal basis adapted to `W`
(`stdGaussian_eq_map_pi_orthonormalBasis`); `inner_lse_eq_inner_starProjection` is self-adjointness
of `Submodule.starProjection`. `Module.finrank ℝ W` plays the role of `s`.

## Sanctioned deferral

`RandomDesign.not_exists_blue_of_known_design_moment` — DEFERRAL-ELIGIBLE. It carries a nondegeneracy hypothesis beyond the printed source statement because **the universal form as printed is false**: for an a.s. constant design the fixed-design theorem does supply a BLUE. Do not remove that hypothesis. Leave it sorried with a `-- TODO:` if it resists.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, whether the sanctioned deferral was closed or left, and any statement you believe is false (with the counterexample).
