# Build the Gaussian ↔ chi-squared bridge in ForMathlib/NoncentralChiSquared.lean, then apply it

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session. Work sequentially, committing each lemma as it compiles.

## The one reusable brick, then its consumers

Two separate work items (the trinity and the χ² goodness-of-fit chapter) are both blocked on the **same missing lemma**: the law of a Gaussian quadratic form is chi-squared.

**Only edit** `StatLean/HypothesisTesting/ForMathlib/NoncentralChiSquared.lean` and `.../GoodnessOfFit/ChiSquaredMultinomial.lean` and `.../LikelihoodMethods/TrinityChiSquared.lean`.

Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars. Goal 0-sorry on the reachable targets; escape hatch = one lifted `private` sorry per file with a precise TODO. **Do not weaken any statement**; report false ones precisely — ten such reports have been acted on this campaign.

## Priority 1 — the bridge (in `NoncentralChiSquared`)

State and prove: for `Z ~ multivariateGaussian 0 (I_k)` (standard `k`-dim Gaussian) and a positive-definite `Σ`, the law of `⟪z, Σ⁻¹ z⟫` under `multivariateGaussian 0 Σ` is `chiSquared k`; more generally with mean `μ` it is `noncentralChiSquared k (⟪μ, Σ⁻¹ μ⟫).toNNReal`. Route (whitening):
- `multivariateGaussian 0 Σ = (multivariateGaussian 0 1).map (Σ^{1/2} • ·)` — the repo has `MultivariateGaussianSmul`/`MultivariateGaussianConv`; `Matrix.PosDef` gives the sqrt (`Matrix.PosDef.sqrt` / `posSemidef_sqrt`).
- Under that map, `⟪z, Σ⁻¹ z⟫ = ‖Σ^{-1/2} z‖²` becomes `‖standard normal‖²`, whose law is `chiSquared k` — the repo has `map_sum_sq_eq_chiSquared` (`MultipleTesting.ForMathlib.ChiSquared`) for exactly `‖·‖² of standard Gaussian`.
Note the existing `noncentralChiSquared_zero` and direction-invariance lemmas (closed) are the pieces for the noncentral case.

## Priority 2 — apply it

- `TrinityChiSquared.score_tendsto_chiSquared`: a predecessor closed everything **modulo** exactly this bridge (a named `private` sorry with a whitening TODO). Discharge that sorry with the Priority-1 lemma.
- `ChiSquaredMultinomial.pearsonQ_weakConverges_chiSquared`: Pearson's `Qₙ ⇒ chiSquared (k−1)`. The multivariate CLT (`AsymptoticStatistics/ForMathlib/MultivariateCLT`, closed) gives `√n(p̂−p) ⇒ N(0, Σ)` with `Σ = diag(p) − ppᵀ`; the continuous-mapping theorem plus the bridge gives the quadratic form's χ² limit. The `k−1` (not `k`) comes from `Σ` being rank `k−1`; handle by restricting to the `∑=0` subspace where it is nonsingular, or cite the generalized-inverse form — transcribe honestly and if the rank-deficiency needs a lemma the repo lacks, report it precisely.

## Closed, axiom-clean — black boxes

`ForMathlib.NoncentralChiSquared.{noncentralChiSquared_zero, direction-invariance, tail-monotone}` (the parts already closed); `MultipleTesting.ForMathlib.ChiSquared` (`chiSquared`, `map_sum_sq_eq_chiSquared`, moments); `AsymptoticStatistics.ForMathlib.{MultivariateCLT, CramerWold, MultivariateGaussianSmul, MultivariateGaussianConv}`; `ForMathlib.LindebergCLT`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms` on the bridge lemma and `score_tendsto_chiSquared`, and for anything left open the precise obstruction.
