# Close #15: Fano continuous-Z entropy (FanoLowerBound.lean) — HIGHEST RISK

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/Fano/FanoLowerBound.lean`
Close `fano_entropy_continuous {M} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q] (hM : 2 ≤ M) :
ENNReal.ofReal (log M) ≤ mutualInformation Q + ENNReal.ofReal (log 2) + multiwayTestingError Q * ENNReal.ofReal (log M)`.
Keep signature UNCHANGED; helpers `private`.

## Strategy — `condDistrib` disintegration + StatLean discrete entropy
`mutualInformation Q = M⁻¹ Σⱼ klDiv (Q j) (mixture Q)` (def in `Fano/MutualInformation.lean`).
Available 0-sorry bricks (`ForMathlib/Entropy.lean`): `discreteEntropy`, `discreteCondEntropy_le_entropy`
(Fano-type `H(J|Z) ≤ h(q)+q·log(M−1)`-flavoured), `discreteEntropy_le_log_card` (`h(q) ≤ log 2`).
Mathlib: `ProbabilityTheory.condDistrib` (posterior `J|Z`), `compProd_map_condDistrib`,
`condExp_ae_eq_integral_condDistrib`, `PMF.uniformOfFintype` (uniform `J`), `klDiv_le_avg` (proven).
Plan:
1. Let `J` uniform on `Fin M`, joint law `ρ = (uniformPrior M) ⊗ₘ Q` on `Fin M × 𝓧`. Build the posterior
   kernel `post := condDistrib (Prod.fst) (Prod.snd) ρ : 𝓧 → Fin M` via Mathlib `condDistrib`.
2. **Identity** `mutualInformation Q = ofReal (log M) − H(J|Z)` where `H(J|Z) := ∫ discreteEntropy (post z) d(Q∘ₘunif)`:
   expand `klDiv (Q j)(mixture)` against the posterior; this is the KL-vs-entropy bridge. (`discreteEntropy` of
   uniform `= log M`.)
3. **Fano core** `H(J|Z) ≤ h(q) + q·log(M−1) ≤ log2 + q·log M` with `q = multiwayTestingError Q`
   (`discreteCondEntropy_le_entropy` + `discreteEntropy_le_log_card`).
4. Combine: `log M = I + H(J|Z) ≤ I + log2 + q·log M`. Rearrange to the ℝ≥0∞ goal.

**This is research-grade — Mathlib has NO conditional entropy / mutual information.** If step 2 (the
KL↔entropy identity) resists after honest effort, isolate the SMALLEST residual as ONE named `private`
lemma `mutualInformation_eq_log_card_sub_condEntropy` (single sorry + precise `-- TODO(mmx)`) and PROVE
steps 3+4 + the rearrangement around it. Do NOT bare-sorry the public lemma; keep exactly one named debt.

## DONE: `lake build StatLean.Minimaxity.Fano.FanoLowerBound` green (0 sorry, or exactly 1 named residual).
`git add` ONLY that file; commit. Report exactly what closed + any residual.
