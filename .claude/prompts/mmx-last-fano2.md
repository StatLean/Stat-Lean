# Close #15 final: mapError_integral_le (FanoLowerBound.lean) — the ≤ MAP/Bayes-risk identity

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).
**DIRECTIVE: do NOT ask questions. Close the single `sorry`, or leave it UNCHANGED (do not split further) + commit a note. Aim for 0 sorry.**

## Touch-set (edit ONLY) — `StatLean/Minimaxity/Fano/FanoLowerBound.lean`
Everything else is PROVEN. Close the ONE remaining `sorry` in `mapError_integral_le` (≈ line 274):
```
∫ z, (1 - ⨆ j, (M:ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) ∂(mixture Q) ≤ (multiwayTestingError Q).toReal
```
`multiwayTestingError Q = bayesRisk (zeroOneLoss M) Q (uniformPrior M)` (`Defs.lean`);
`zeroOneLoss M j k = if j = k then 0 else 1`; `mixture Q = Q ∘ₘ uniformPrior M`.

## Strategy — `∫e ≤ avgRisk(κ)` for every Markov κ, then `∫e ≤ ⨅κ avgRisk = bayesRisk`
1. **Reduce bayesRisk to its iInf.** `bayesRisk ℓ P π = ⨅ κ, avgRisk ℓ P κ π` (Mathlib
   `Probability/Decision/Risk/Defs.lean` — it IS the definition / `bayesRisk_eq_iInf`; check the exact name with
   `./tools/loogle.sh '"bayesRisk"'`). So it suffices to show `∫e ≤ avgRisk (zeroOneLoss M) Q κ (uniformPrior M)`
   for every Markov `κ : Kernel 𝓧 (Fin M)`, then take `le_iInf` / `le_ciInf` and `ENNReal.toReal` monotonicity
   (need finiteness: `multiwayTestingError Q ≤ 1 ≠ ⊤` since it's a 0–1-loss Bayes risk).
2. **avgRisk in integral form.** Unfold `avgRisk (zeroOneLoss M) Q κ (uniformPrior M)`
   `= ∫⁻ j, ∫⁻ z, zeroOneLoss M j · ∂((κ ∘ₖ Q) j) ∂(uniformPrior M)` (cf. the proven `hB` computation in
   `EstimationToTesting.lean`'s `mul_multiwayTestingError_le`). Push to the mixture: `(uniformPrior M)` gives the
   `M⁻¹∑ⱼ`, and `∫ … d(Q j) = ∫ … rⱼ d(mixture Q)` via `Q j ≪ mixture Q` and `Measure.rnDeriv` (the file already
   has `hac : Q j ≪ mixture Q` and the `rⱼ` machinery in `mutualInformation_toReal_eq`). Result:
   `avgRisk = ∫⁻ z, (∑ⱼ (M:ℝ≥0∞)⁻¹ rⱼ(z) · (κ z){j}ᶜ) ∂(mixture Q)` where `{j}ᶜ` is the 0–1 "κ decides ≠ j" mass.
3. **Pointwise bound.** With `pⱼ(z) = M⁻¹ rⱼ(z)` (a pmf a.e., `∑ⱼ pⱼ = 1`), and `κ z` a prob measure on `Fin M`:
   `∑ⱼ pⱼ(z)·(κ z){j}ᶜ = ∑ⱼ pⱼ - ∑ⱼ pⱼ (κ z){j} = 1 - ∑ⱼ pⱼ (κ z){j} ≥ 1 - (⨆ⱼ pⱼ)·∑ⱼ(κ z){j} = 1 - ⨆ⱼ pⱼ = e(z)`
   (using `∑ⱼ pⱼ(κz){j} ≤ (⨆ pⱼ)·(κ z)(univ) = ⨆ pⱼ`; `Finset.sum_le_sum` + `le_ciSup`/`le_iSup`). Integrate:
   `avgRisk ≥ ∫ e`. Mind ℝ vs ℝ≥0∞: do the pointwise bound in ℝ≥0∞ (or in ℝ after `toReal`, with the a.e.
   finiteness `rⱼ ≠ ∞` already in the file as `htop`).
4. **Conclude:** `∫ e ≤ ⨅κ avgRisk = bayesRisk = multiwayTestingError Q` (in ℝ≥0∞), then `.toReal`.

Reuse: `EstimationToTesting.lean`'s avgRisk computation (`hB`, `bayesRisk_le_avgRisk`, `Kernel.comp_apply`),
`mutualInformation_toReal_eq`'s `hac`/`htop`/`rⱼ` setup, `Measure.lintegral_rnDeriv`/`setLIntegral`, `le_iSup`.
If the κ-quantified bound needs `Measurable`/integrability side-goals, discharge with the `measurable_of_countable`
(Fin M target) pattern already used in `EstimationToTesting.lean`.

## DONE: `lake build StatLean.Minimaxity.Fano.FanoLowerBound` green 0 sorry. `git add` ONLY that file; COMMIT.
