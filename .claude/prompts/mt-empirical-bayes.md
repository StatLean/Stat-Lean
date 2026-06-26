# mt-empirical-bayes — Bayes risk of the Gaussian shrinkage estimator (Candès L15 Prop 1)

You are a Lean 4 proof subagent on branch `mt/empirical-bayes` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/EmpiricalBayes/BayesRisk.lean`

Do not touch any other file. You MAY add `private` helper lemmas within the touch-set. Do not change
the public theorem signature.

## Goal
Prove `empiricalBayes_risk` (0-sorry). Verify
`lake build StatLean.MultipleTesting.EmpiricalBayes.BayesRisk` green.

## The theorem (Candès L15 §15.3.3, Prop 1)
Prior `θᵢ ∼ N(0,τ²)`, noise `εᵢ ∼ N(0,σ²)`, `θᵢ ⟂ εᵢ`, shrinkage `s = τ²/(σ²+τ²)`. Then
`∫ ∑ᵢ (s(θᵢ+εᵢ) − θᵢ)² dμ = p · σ²τ²/(σ²+τ²)`.

## Proof roadmap
Set `s = τ2/(σ2+τ2)`, `den = σ2+τ2 > 0`. Residualᵢ `= s(θᵢ+εᵢ) − θᵢ = (s−1)θᵢ + s·εᵢ`.
1. **Sum out the integral**: `∫ ∑ᵢ residualᵢ² = ∑ᵢ ∫ residualᵢ²` via `integral_finset_sum`
   (each `residualᵢ²` integrable — see step 4). So it suffices to show
   `∫ residualᵢ² dμ = σ2*τ2/den` for each `i`, then `∑ᵢ = p · (σ2*τ2/den)` (`Finset.sum_const`,
   `Finset.card_fin`).
2. **Expand**: `residualᵢ² = (s−1)²·θᵢ² + s²·εᵢ² + 2s(s−1)·(θᵢ·εᵢ)`. `integral_add`/`integral_sub`
   + `integral_const_mul`.
3. **Per-coordinate moments** (push to the law via `integral_map (h?.aemeasurable) (by fun_prop)`):
   - `∫ θᵢ² dμ = ∫ x² d(N(0,τ2)) = τ2`. Second moment `= variance` (mean 0): use
     `variance_id_gaussianReal` (gives `variance = v`) + `variance_eq_integral` (mean-0 case), as in
     the merged `ForMathlib/GaussianMoments.lean integral_sq_stdGaussian` (READ it — same incantation,
     here with `v = τ2`). Likewise `∫ εᵢ² dμ = σ2`.
   - `∫ θᵢ dμ = 0`, `∫ εᵢ dμ = 0`: `integral_id_gaussianReal` via `integral_map`.
   - `∫ (θᵢ·εᵢ) dμ = (∫ θᵢ)(∫ εᵢ) = 0`: `ProbabilityTheory.IndepFun.integral_mul (hindep i)`
     (search `./tools/loogle.sh '"IndepFun.integral_mul"'`; needs integrability of `θᵢ`,`εᵢ`).
4. **Integrability**: `θᵢ`,`εᵢ`,`θᵢ²`,`εᵢ²`,`θᵢεᵢ` all integrable. Powers: push to the Gaussian law and
   use `memLp_id_gaussianReal'`/`MemLp.integrable_*` (see GaussianMoments' `integrable_pow_stdGaussian`
   pattern). Product `θᵢεᵢ`: `(hindep i).integrable_mul` or `MemLp.integrable_mul` (Hölder, L²×L²→L¹).
5. **Algebra**: `(s−1)²τ2 + s²σ2 = σ2*τ2/den`. With `s = τ2/den`, `s−1 = −σ2/den`:
   `(σ2²τ2 + τ2²σ2)/den² = σ2τ2·den/den² = σ2τ2/den`. `have hden : σ2+τ2 ≠ 0 := by positivity`;
   `field_simp; ring`.

## Lean guidance
- `gaussianReal 0 ⟨τ2, hτ.le⟩` — the variance is the `ℝ≥0` `⟨τ2, _⟩`; `(⟨τ2,_⟩ : ℝ≥0) = τ2` under
  coercion (`NNReal.coe_mk`). `variance_id_gaussianReal` is stated for the `ℝ≥0` variance argument.
- The cross term needs `E[θᵢ]=E[εᵢ]=0`, so `2s(s−1)·0 = 0` drops it.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; no anonymous `sorry`. Commit to `mt/empirical-bayes`
(`mt(eb): Bayes risk of Gaussian shrinkage = pσ²τ²/(σ²+τ²) (Candès L15 Prop 1)`).

## DONE
`lake build StatLean.MultipleTesting.EmpiricalBayes.BayesRisk` exits 0; 0 sorry in the file. Report
build status, sorry count, the second-moment + `IndepFun.integral_mul` lemmas used, any helpers.
