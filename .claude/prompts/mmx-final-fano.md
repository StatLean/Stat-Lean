# Close #15: Fano conditional-entropy crux (FanoLowerBound.lean) — HARDEST

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND `lake build` (lake on PATH; NOT lean-fasrc-build).

## Touch-set (edit ONLY) — `StatLean/Minimaxity/Fano/FanoLowerBound.lean`
Close `fano_entropy_continuous {M} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q] (hM : 2 ≤ M) :
ENNReal.ofReal (log M) ≤ mutualInformation Q + ENNReal.ofReal (log 2) + multiwayTestingError Q * ENNReal.ofReal (log M)`.
Keep signature UNCHANGED; helpers `private`. `mutualInformation Q = M⁻¹ Σ_j klDiv (Q j) (mixture Q)`
(`Fano/MutualInformation.lean`); `multiwayTestingError Q = bayesRisk (zeroOneLoss M) Q (uniformPrior M)` (`Defs.lean`).

## KEY Mathlib bricks (verified present)
- `Mathlib/Probability/Kernel/Posterior.lean`: `ProbabilityTheory.posterior (κ) (μ) : Kernel 𝓧 (Fin M)` (notation `κ†μ`),
  `compProd_posterior_eq_map_swap : (κ ∘ₘ μ) ⊗ₘ (κ†μ) = (μ ⊗ₘ κ).map Prod.swap`,
  `posterior_eq_withDensity_of_countable : ∀ᵐ x ∂(κ∘ₘμ), (κ†μ) x = μ.withDensity (fun ω ↦ (κ ω).rnDeriv (κ∘ₘμ) x)`.
- `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`: `Real.negMulLog x = -x*log x`, `negMulLog_zero/one`, `continuous`.
- `InformationTheory/KullbackLeibler/*`: `klDiv_eq_integral_llr`/`klDiv_eq_lintegral_klFun_of_ac`, `klDiv_compProd_eq_add`, `llr`.
- StatLean `ForMathlib/Entropy.lean`: `discreteEntropy`, `discreteCondEntropy_le_entropy`, `discreteEntropy_le_log_card` — READ this file; reuse its discrete Fano lemmas.
- `Real.binEntropy`, `binEntropy_le_log_two`.

## Strategy — hand-build conditional entropy, prove `I = log M − H(J|Z)`, then Fano
1. Joint law `ρ := (uniformPrior M) ⊗ₘ Q` on `Fin M × 𝓧`; `Z`-marginal `= mixture Q` (`Measure.snd_compProd`).
   Posterior `post := Q † (uniformPrior M) : Kernel 𝓧 (Fin M)` (Bayesian inverse of `J ↦ Z`).
2. Define `private noncomputable def condEntropy := ∫ z, (∑ j, Real.negMulLog ((post z {j}).toReal)) ∂(mixture Q)`
   (= `H(J|Z)`). The posterior `post z` is a `PMF`-like measure on `Fin M`.
3. **MI identity** `mutualInformation Q = ENNReal.ofReal (log M − condEntropy)`: expand
   `M⁻¹ Σ_j klDiv (Q j) (mixture)` via `klDiv_eq_integral_llr` and `posterior_eq_withDensity_of_countable`
   (the posterior density is exactly `M·(Q j).rnDeriv(mixture)` up to the uniform prior `1/M`), reorganize the
   double integral over `(j,z)` against `ρ`, and recognize `log M − H(J|Z)`. (`discreteEntropy` of uniform `= log M`.)
4. **Fano core** `H(J|Z) ≤ binEntropy q + q·log(M−1) ≤ log 2 + q·log M` with `q = multiwayTestingError Q`:
   reuse `discreteCondEntropy_le_entropy` + `discreteEntropy_le_log_card` from `Entropy.lean` applied to the
   posterior; `binEntropy_le_log_two`; `log(M−1) ≤ log M`.
5. Combine `log M = I + H(J|Z) ≤ I + log2 + q·log M` and push to the `ENNReal.ofReal` goal (`ofReal_le_ofReal`,
   `ENNReal.ofReal_add`, handle `toReal` of `mutualInformation`/`multiwayTestingError`).

This is research-grade. If step 3 (the KL↔posterior-entropy identity) genuinely resists after honest effort,
isolate the SMALLEST piece as ONE named `private` lemma (one sorry + precise TODO) — e.g.
`mutualInformation_eq_ofReal_log_card_sub_condEntropy` — and PROVE steps 4+5 + the rearrangement around it.
Do NOT bare-sorry the public lemma; ≤ 1 named residual, SMALLER than the current whole-crux one.

## DONE: `lake build StatLean.Minimaxity.Fano.FanoLowerBound` green (0 sorry, or 1 smaller named residual).
`git add` ONLY that file; commit. Report exactly what closed + the bridge lemmas used.

## DIRECTIVE
Do NOT ask the user questions. Continue from the committed reduction (the ENNReal wrapper is already proven; the conditional-entropy MI identity is the remaining core). Either reach 0 sorry or leave EXACTLY ONE smaller named private residual and COMMIT. Never leave the file unchanged.
