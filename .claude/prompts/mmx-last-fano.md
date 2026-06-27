# Close #15: condEntropy_le_fano (Fano/FanoLowerBound.lean) — discrete Fano + MAP identity

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).
**DIRECTIVE: do NOT ask questions. Reach 0 sorry, or leave EXACTLY ONE smaller named `private` residual + COMMIT.**

## Touch-set (edit ONLY) — `StatLean/Minimaxity/Fano/FanoLowerBound.lean`
The file's `mutualInformation_toReal_eq` (`I = log M − condEntropy`), `fano_real`, `fano_entropy_continuous`,
`fano_inequality` are ALL PROVEN. The ONLY `sorry` is `condEntropy_le_fano` (≈ line 188). Closing it closes
`fano_inequality` outright. Keep signatures UNCHANGED; helpers `private`.

## Goal
`condEntropy Q ≤ Real.log 2 + (multiwayTestingError Q).toReal * Real.log M`, where (in the file)
`condEntropy Q = ∫ z, (∑ j, Real.negMulLog ((M:ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)) ∂(mixture Q)`,
`multiwayTestingError Q = bayesRisk (zeroOneLoss M) Q (uniformPrior M)` (`Defs.lean`).

## Strategy (4 steps)
1. **Pointwise discrete Fano (grouping).** Prove a `private` lemma: for `p : Fin M → ℝ` a pmf (`0 ≤ pⱼ`,
   `∑ pⱼ = 1`), `∑ⱼ Real.negMulLog pⱼ ≤ Real.binEntropy e + e * Real.log (M-1)` with `e = 1 − ⨆ⱼ pⱼ` (the
   max). Proof: let `j* = argmax`, `m = p j*`. Group: `H(p) = binEntropy m + m·negMulLog(...)... ` — cleanest is
   the entropy chain rule: `∑ⱼ negMulLog pⱼ = binEntropy m + (1−m)·H(conditional on j≠j*)`, and the conditional
   pmf on the `M−1` remaining outcomes has entropy `≤ log(M−1)` by StatLean `discreteEntropy_le_log_card`
   (`ForMathlib/Entropy.lean` — READ it; `discreteEntropy p ≤ log (card ι)`). So `H(p) ≤ binEntropy(1−m) +
   (1−m)log(M−1) = binEntropy e + e·log(M−1)`. (`Real.binEntropy`, `negMulLog`, `Finset.sum`.)
2. **Integrate + Jensen.** Apply step 1 pointwise at `pⱼ = (M:ℝ)⁻¹·rⱼ(z)` (`rⱼ = (Q j).rnDeriv (mixture Q)`;
   it IS a pmf a.e.: `∑ⱼ M⁻¹ rⱼ = 1` a.e. — the file's `hsumR`/`hsum_ennreal` give `∑ rⱼ = M`). So
   `condEntropy ≤ ∫ binEntropy(e(z)) d(mixture) + log(M−1)·∫ e(z) d(mixture)`, `e(z)=1−⨆ⱼ M⁻¹rⱼ(z)`.
   Then Jensen: `∫ binEntropy(e(z)) ≤ binEntropy(∫ e(z))` via **`Real.strictConcave_binEntropy`**
   (`StrictConcaveOn ℝ (Icc 0 1) binEntropy`) → `ConcaveOn.le_map_integral` / `StrictConcaveOn.concaveOn`
   (search `ConcaveOn.le_map_integral`, `ConcaveOn.smul_le_integral`, `inner_le_weight_mul_Lp` — the integral
   Jensen for a probability measure). `e(z) ∈ [0,1]` since `⨆ⱼ pⱼ ∈ [1/M, 1]`.
3. **MAP identity `∫ e(z) d(mixture Q) = (multiwayTestingError Q).toReal`** (THE crux). `e(z) = 1 − ⨆ⱼ posteriorⱼ(z)`
   is the pointwise Bayes/MAP error; its integral is the Bayes risk of the 0–1 loss.
   - `q ≤ ∫e`: the MAP test `ψ z = (Finset.univ.argmax fun j => rⱼ z)` (or via `Measurable.find` over `Fin M`
     of the argmax — DISCRETE target, measurable like the closed `exists_measurable_nearestPoint` in
     `EstimationToTesting.lean` but argMAX) is a Markov kernel `Kernel.deterministic ψ`, so
     `bayesRisk ≤ avgRisk (zeroOneLoss M) Q (Kernel.deterministic ψ) (uniformPrior M) = ∫ e` (compute the
     avgRisk of the deterministic test mirroring `mul_multiwayTestingError_le`).
   - `∫e ≤ q`: for ANY Markov `κ : 𝓧 → Fin M`, `avgRisk … κ … ≥ ∫ e` (posterior-weighted 0–1 loss minimized by
     argmax: `∑ⱼ M⁻¹ rⱼ(z)·κ(z){≠j} = 1 − ∑ⱼ M⁻¹ rⱼ(z)·κ(z){j} ≥ 1 − ⨆ⱼ M⁻¹ rⱼ(z) = e(z)` since
     `∑ⱼ pⱼ κ{j} ≤ (⨆ pⱼ)·∑ κ{j} = ⨆ pⱼ`). Reduce `bayesRisk` to its `iInf` form (Mathlib
     `Probability/Decision/Risk/Defs.lean`: `bayesRisk ℓ P π = ⨅ κ, avgRisk …`) and take `iInf`.
   Mathlib has NO `bayesRisk_zeroOne_eq`, so this is genuine. If this whole identity resists, isolate it as ONE
   `private` lemma `integral_map_error_eq_bayesRisk` (single sorry) and prove steps 1+2+4 around it.
4. **Close.** `Real.binEntropy_le_log_two` gives `binEntropy(∫e) ≤ log 2`; `log(M−1) ≤ log M`; with `∫e = q`,
   `condEntropy ≤ log 2 + q·log M`. (`mul_le_mul`, `Real.log_le_log`.)

## DONE: `lake build StatLean.Minimaxity.Fano.FanoLowerBound` green (0 sorry, or 1 smaller named residual). `git add` ONLY that file; COMMIT.
