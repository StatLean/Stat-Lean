# Close the sorries in PointEstimation/UMVU/{Basic,CovarianceCriterion,RaoBlackwell}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.UMVU.Basic` (then `.CovarianceCriterion`, then `.RaoBlackwell`). **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** `StatLean/PointEstimation/UMVU/Basic.lean`, `.../CovarianceCriterion.lean`, `.../RaoBlackwell.lean`. Touch nothing else — in particular NOT `UMVU/Defs.lean`, `Sufficiency/Defs.lean`, or `Model/Defs.lean` (frozen, laptop-only).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*` and `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a `-- TODO:`; report it.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms isUMVU_iff_uncorrelated_unbiasedZero` and `#print axioms risk_rbEstimator_le` — expect only `propext, Classical.choice, Quot.sound`.

## Context

`IsUMVU` (frozen, `UMVU/Defs.lean`) is **variance-based**: unbiased, in `Δ = {δ | ∀ θ, MemLp δ 2 (P θ)}`, and of minimal variance at every `θ` among square-integrable unbiased competitors. `IsUnbiasedZero P U` is unbiasedness for the zero estimand.

Mathlib argument order (verify, then rely on it): `ProbabilityTheory.covariance X Y μ` and `ProbabilityTheory.variance X μ`.

## Notes on specific targets

- `isUnbiased_iff_sub_unbiasedZero` (Lem 1.4): with a fixed unbiased `δ₀`, the unbiased estimators are exactly `δ₀ - 𝒰`. Both directions are integral algebra; watch that subtraction of integrals needs the integrability side conditions already in the signature.
- `isUMVU_unique`: two UMVU estimators of the same estimand agree a.e. under each `P θ`. Standard route: their average is unbiased and in `Δ`; compare variances; equality in Cauchy–Schwarz forces a.e. equality. `variance_add`/`covariance` bilinearity plus `ProbabilityTheory.variance_eq_zero_iff`-style reasoning.
- `isUMVU_iff_uncorrelated_unbiasedZero` (Thm 1.7): the classical characterization. (⇐) perturb `δ` by `t·U` and minimize the quadratic in `t`. (⇒) if `cov(δ,U) ≠ 0` at some `θ`, the perturbation `δ - (cov/var)·U` is unbiased with strictly smaller variance there.
- `covariance_depends_only_on_mean_iff` (Thm 5.1, §2.5): read the file docstring — it is stated in Blyth's form, with the reference statistic allowed to depend on `θ`. Both directions follow from `covariance_sub_left` / `covariance_zero_left`.
- **Rao–Blackwell**: `rbEstimator Q δ s = ∫ x, δ x ∂(Q s)` where `Q` is the θ-free sufficient kernel from `HasSufficientKernel`. Unbiasedness is the disintegration identity. The risk bound uses **plain Jensen on each probability fiber** — `ConvexOn.map_integral_le` — NOT conditional Jensen; then Fubini through the graph identity. Fiber integrability is **derived** from the reconstruction identity, not assumed; do not add hypotheses.
- `variance_rbEstimator_le` is the `ρ = (·)²` instance of the risk bound.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, and any statement you believe is false.
