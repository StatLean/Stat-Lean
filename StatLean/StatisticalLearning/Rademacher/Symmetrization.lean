import StatLean.StatisticalLearning.Rademacher.Defs
import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.ConcentrationInequalities.Symmetrization.Empirical

/-!
# Symmetrization: representativeness ≤ 2 × expected Rademacher complexity

SSBD Lemma 26.2: `E_{S∼Dⁿ}[Rep_D(𝓕,S)] ≤ 2 E_{S∼Dⁿ}[R(𝓕∘S)]`, where
`Rep_D(𝓕,S) = sup_{f∈𝓕}(L_D(f) − L_S(f))` — the one-sided, non-absolute
ghost-sample symmetrization that powers all of Ch. 26's generalization bounds.

**Reference.** SSBD §26.1, Lemma 26.2 (Eqs. (26.6)–(26.9)). Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** The project's
`ConcentrationInequalities/Symmetrization/Empirical.lean` proves the
*absolute-value* form; SSBD's constants in Theorem 26.5 need this one-sided
non-absolute form, so it is proved here afresh by the book's argument: ghost
sample `S' ∼ Dⁿ` + Jensen (sup of expectation ≤ expectation of sup), per-
coordinate swap invariance introducing the signs, and the `σ ≍ −σ` split
giving the factor 2. The sign average is bridged to the `signVec` product
measure by `signAvg_eq_integral_signVec` (every function is a.e.-strongly
measurable for the finitely-atomic `signVec n`). Index sets are countable and
sups are `sSup`-of-image with a uniform bound `c`, per the batch sup policy.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

/-- Bridge between the finite sign average and the `signVec` product law
(LEAN-ONLY): `signAvg n g = ∫ ε, g ε ∂(signVec n)` for every `g` — the law
`signVec n` is supported on the `2ⁿ` sign atoms with equal mass, so every
function is a.e.-strongly measurable and the integral is the finite average. -/
theorem signAvg_eq_integral_signVec (g : (Fin n → ℝ) → ℝ) :
    signAvg n g = ∫ ε, g ε ∂(signVec n) := by
  sorry

/-- **SSBD Lemma 26.2** (one-sided symmetrization, countable family): for a
countable index type and a uniformly bounded measurable family `F`,
`E_{S∼Dⁿ} sup_{k∈K} (L_D(F k) − L_S(F k)) ≤ 2 E_{S∼Dⁿ} R(F ∘ S)`. -/
theorem integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad
    (F : ι → Z → ℝ) (K : Set ι) {c : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    -- USER-INPUT: nonempty family; SSBD §26.1 (implicit)
    (hK : K.Nonempty)
    -- USER-INPUT: measurability of the family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|f| ≤ c` on the family; SSBD Thm 26.5
    -- setting (supplies integrability of the sups)
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: at least one example; SSBD §26.1 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K)
        ∂(sampleLaw D n) ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  sorry

end StatLean.StatisticalLearning
