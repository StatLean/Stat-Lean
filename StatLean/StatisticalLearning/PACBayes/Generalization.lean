import StatLean.StatisticalLearning.PACBayes.ChangeOfMeasure
import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

/-!
# The PAC-Bayes generalization bound

SSBD Theorem 31.1: for a `[0,1]`-valued loss, prior `P`, and `δ ∈ (0,1)`,
with probability `≥ 1 − δ` over `S ∼ Dⁿ`, **simultaneously for every**
(possibly sample-dependent) posterior `Q`,
`L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(2n/δ)) / (2(n−1)))`.

**Reference.** SSBD §31.1, Theorem 31.1 and Exercise 31.1. Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Proof chain exactly as the book: Markov on
`e^{f(S)}` for `f(S) = sup_Q (2(n−1) E_Q[Δ²] − D(Q‖P))`, change of measure +
Jensen (`ChangeOfMeasure.lean`) to kill the sup over `Q`, Fubini, the moment
lemma `E[e^{2(n−1)Δ(h)²}] ≤ 2n` from Hoeffding's two-sided tail, and Jensen
for `x²`. **Deviation from the book:** SSBD states `ln(m/δ)` from
`E[e^{2(m−1)Δ²}] ≤ m`, whose Exercise-31.1 derivation uses only the one-sided
tail `P[Δ ≥ ε] ≤ e^{−2mε²}` — but the exponent involves `Δ²`, which needs the
two-sided tail `P[|Δ| ≥ ε] ≤ 2e^{−2mε²}`; the honest constant is
`E ≤ 2m − 1 ≤ 2m`, so this file freezes `ln(2n/δ)`. The `∀ Q` inside the
event is genuine (the book's "even such that depend on `S`"): the event is
the sup-free moment inequality, from which every `Q` is handled pointwise.
-/

open MeasureTheory InformationTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] [MeasurableSpace ι]
  [DiscreteMeasurableSpace ι] [Countable ι]

/-- **Moment bound from a sub-Gaussian tail** (SSBD Exercise 31.1, honest
two-sided form): if `P[|Y| ≥ ε] ≤ 2e^{−2nε²}` for all `ε > 0` and `2 ≤ n`,
then `E[e^{2(n−1)Y²}] ≤ 2n`. (Book claims `n` from the one-sided tail; the
`Δ²` exponent needs both tails, giving `2n − 1 ≤ 2n` — see module notes.) -/
theorem integral_exp_sq_le_of_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} {n : ℕ}
    -- LEAN-ONLY: measurability of `Y` (layer-cake regularity)
    (hY : Measurable Y)
    -- USER-INPUT: two-sided sub-Gaussian tail; SSBD Ex. 31.1 (corrected)
    (htail : ∀ ε : ℝ, 0 < ε →
      μ.real {ω | ε ≤ |Y ω|} ≤ 2 * Real.exp (-2 * n * ε ^ 2))
    -- USER-INPUT: `n ≥ 2`; SSBD Thm 31.1 (`m − 1 > 0`)
    (hn : 2 ≤ n) :
    ∫ ω, Real.exp (2 * (n - 1 : ℝ) * Y ω ^ 2) ∂μ ≤ 2 * n := by
  sorry

/-- **SSBD Theorem 31.1 (PAC-Bayes)**: for a countable hypothesis index,
`[0,1]`-valued loss family `F`, prior `P`, and `δ ∈ (0,1)`, with probability
`≥ 1 − δ` over `S ∼ Dⁿ` (`n ≥ 2`), simultaneously for every posterior `Q ≪ P`
with finite KL,
`L_D(Q) ≤ L_S(Q) + √((D(Q‖P) + ln(2n/δ)) / (2(n−1)))`
(constant `2n` in place of the book's `n` — module notes). -/
theorem pac_bayes (D : Measure Z) [IsProbabilityMeasure D]
    (P : Measure ι) [IsProbabilityMeasure P] (F : ι → Z → ℝ) {n : ℕ}
    {δ : ℝ}
    -- USER-INPUT: loss range in `[0,1]`; SSBD Thm 31.1
    (hrange : ∀ k z, F k z ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: measurability of the loss family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: `n ≥ 2`; SSBD Thm 31.1 (`m − 1 > 0` in the denominator)
    (hn : 2 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 31.1
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ Q : Measure ι,
        IsProbabilityMeasure Q → Q ≪ P → klDiv Q P ≠ ⊤ →
          gibbsAvg Q (fun k => risk D F k) ≤
            gibbsAvg Q (fun k => empRisk F s k) +
              Real.sqrt (((klDiv Q P).toReal + Real.log (2 * n / δ)) /
                (2 * (n - 1 : ℝ)))} := by
  sorry

end StatLean.StatisticalLearning
