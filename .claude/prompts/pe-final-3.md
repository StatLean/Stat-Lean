# Close the remaining PointEstimation debts: LinearModel/{LeastSquares,Equivariant}, ExponentialFamily/{Smoothness,MinimalSufficient}, Equivariance/{LocationMRE,LocationExamples,ScaleStructure,ScaleMRE}

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** those eight files. Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors** except the named genuine obstructions. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — six such reports have been acted on this campaign, three of them false statements with counterexamples. That is the highest-value output you can produce.
- Commit after each lemma compiles.

## Batch 11 is at 26 open declarations out of an original 175. These are the tail.

**Priority order** (highest leverage first):

1. **`LeastSquares` (3)** — the orthonormal-basis transport `linearModelFull → canonicalModel`. `LinearModel.Canonical` is now **entirely closed** (complete sufficiency, the sufficiency kernel, and the UMVU trio), so this is a genuine reduction. Mathlib has `ProbabilityTheory.stdGaussian_map (f : E ≃ₗᵢ[ℝ] F) : (stdGaussian E).map f = stdGaussian F`. What is still needed: (a) an affine bridge `gaussianVector ξ σ² = (stdGaussian _).map (√σ² • · + ξ)`; (b) an isometry built from an orthonormal basis whose first `finrank W` vectors span `W` (`Orthonormal.exists_orthonormalBasis_extension`); (c) transport of `IsUMVU` along a measurable equiv of the sample space — `RandomDesign.isUMVU_reparam` is a working template for the parameter-side analogue. `inner_lse_eq_inner_starProjection` is self-adjointness of `Submodule.starProjection`.
2. **`LocationExamples` (1)** — `isLocMRE_mean_gaussian`. **`Pitman.lean` is now 0-sorry**, so the cheap route is open: for the Gaussian location family the Pitman ratio evaluates in closed form to `X̄` by completing the square in the exponent. No Basu machinery needed. Do **not** attempt the Kagan–Linnik–Rao converse (out of scope).
3. **`LocationMRE` (2)** — `exists_measurable_condMinimizer_convex`: the crux is continuity of the `ℝ≥0∞`-valued convex objective `w ↦ ∫⁻ ofReal(ρ(δ₀· − w)) ∂κ(z)`, which can jump finite→∞ at its finiteness boundary; plus coercivity via Fatou, feeding `ForMathlib.MeasurableArgmin.exists_measurable_argmin` (closed — it takes **continuity**, deliberately, not lower semicontinuity). And `exists_isLocMRE_of_bounded_loss`: translation-continuity of `c ↦ ∫ ρ(t−c) f(t) dt` by DCT, then extreme value on a compact sublevel set.
4. **`ScaleMRE` (2) / `ScaleStructure` (2)** — `isScaleMRE_of_conditional_min` is closed, and `exists_isScaleMRE_of_convex` has just been corrected: it now carries `hposmin : ∀ u, ∃ v > 0, γ v ≤ γ u` (your predecessor proved the old form FALSE at r=0 — γ could dip below its positive-axis infimum on the non-positives, so no MRE existed). **Close it now** via the corrected engine plus `exists_measurable_argmin`; `hposmin` reduces the all-`w` domination to the positive axis where `hconv`/`hnotmono` give attainment. The older note said `isScaleMRE_of_conditional_min` is now **closed** (its `hmin` was corrected to range over all `w ≠ 0` after a session proved the positive-only form false). Finish `exists_isScaleMRE_of_convex` on top of it. For `ScaleStructure`, the `mpr` of the measurable factorization was reported false (a non-Borel subset of the null hyperplane); verify, and if it holds leave it sorried **with the counterexample** rather than forcing it.
5. **`Equivariant` (4)** — the canonical/subspace MRE clauses: a Gaussian conditional-risk minimization in canonical coordinates, plus for the scale clause the chi-square moment minimization `argmin_c E(c·Vʳ − 1)²` (`residualScaleConst_one` is already closed as the `r = 1` value).
6. **`Smoothness` (4)** — the multivariate dominated-convergence work: continuity and `HasFDerivAt` for `η ↦ ∫ f·e^{⟪η,T⟫} dν` on the interior, via `hasFDerivAt_integral_of_dominated_loc_of_lip` with the `2^s` sign-vector envelope `exp(c·Σ|Tᵢ|) ≤ Σ_ε exp⟪c·ε, T⟫`. **`analyticOnNhd_integral_exp_inner` (full joint analyticity) is a sanctioned deferral — do not attempt it.**
7. **`MinimalSufficient` (2)** — Cor 6.16, on top of the closed `Completeness.ExpFamily` and `Sufficiency` stack.

## Closed, axiom-clean — black boxes

`ForMathlib` (all 8); `ExponentialFamily/{Basic,MGF,NaturalStatistic}`; `Sufficiency/*` (except the sanctioned general regular-conditional deferral); `Completeness/{Basu,ExpFamily}`; `UMVU/{Basic,CovarianceCriterion,RaoBlackwell}`; `InformationInequality/{Basic,CramerRao,Additivity,Multiparameter}`; `Equivariance/{General,LocationStructure,ConditionalRiskEngine,RiskUnbiased,Pitman}`; `LinearModel/{Canonical,GaussMarkov}`.

**Do not route UMVU conclusions through `isUMVU_of_complete_sufficient`** — it calls a private lemma holding an open debt, so proofs through it report `sorryAx`. Use `UMVU.CovarianceCriterion.isUMVU_iff_uncorrelated_unbiasedZero` instead; for Gaussian models the measurable-representative gap closes because all members are mutually absolutely continuous.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms isUMVU_lse_functional`, and for anything left open the precise obstruction.
