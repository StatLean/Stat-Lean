# Close Fano's inequality via Mathlib condDistrib (Fano/FanoLowerBound.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/Fano/FanoLowerBound.lean` (close `fano_inequality`)
Keep public signature/docstring UNCHANGED. Helpers `private`.

## KEY Mathlib tool: `ProbabilityTheory.condDistrib`
`Mathlib/Probability/Kernel/CondDistrib.lean` gives the regular conditional distribution of `J` given `Z`.
For the joint law of `(Z, J)` (J uniform on `Fin M`, Z ∼ Q J), `condDistrib J Z` is a Markov kernel
`𝓧 → Fin M` = the posterior. Conditional entropy `H(J|Z) = ∫ discreteEntropy (condDistrib J Z z) d(law Z)`.
Use `Entropy.lean` (`discreteEntropy`, `discreteEntropy_le_log_card`) for the per-z entropy, and Mathlib
`condDistrib_ae_eq_condExp` / disintegration `Measure.compProd` (`law (Z,J) = (law Z) ⊗ₘ condDistrib`).

## Proof of `fano_inequality` (Eq 15.61 ⇒ statement)
Standard Fano: `H(J|Z) ≤ h(qₑ) + qₑ·log(M−1)` where `qₑ = P[ψ(Z)≠J]` (any test ψ). Then since J⊥Z prior is
uniform, `I(Z;J) = log M − H(J|Z)`, and `h(qₑ) ≤ log 2`, so `qₑ ≥ 1 − (I + log2)/log M`. The testing error
`multiwayTestingError Q = inf_ψ qₑ`, giving the bound. Steps:
1. `I(Z;J) = H(J) − H(J|Z) = log M − H(J|Z)` (J uniform). Use `mutualInformation` def + `discreteEntropy`
   of uniform `= log M` (`discreteEntropy` of `PMF.uniformOfFintype`).
2. The data-processing core `H(J|Z) ≤ h(qₑ) + qₑ log(M−1)`: condition on `1[ψ(Z)=J]`; chain rule of entropy
   `H(J|Z) ≤ H(J, 1[ψ≠J] | Z) = H(1[ψ≠J]|Z) + H(J | Z, 1[ψ≠J]) ≤ h(qₑ) + qₑ log(M−1)`. This is the genuine
   Fano core — build it from `discreteEntropy`/`discreteCondEntropy` chain-rule lemmas in `Entropy.lean`
   (prove the chain rule there if missing — but it's touch-set-forbidden; instead build the needed pieces
   as `private` lemmas HERE using the existing Entropy API).
3. Rearrange. `Real.binEntropy`/`Real.binEntropy_le_log_two`.

If the full continuous-Z `condDistrib` entropy integral is too heavy, isolate the SMALLEST residual as one
named `private fano_entropy_core` (single sorry + precise TODO) and prove the rearrangement + MI identity
+ `h≤log2` around it. GOAL: shrink to the genuine Fano-core or close fully.
## DONE: build module green; `git add` only that file; commit. Report exactly what closed + residual.
