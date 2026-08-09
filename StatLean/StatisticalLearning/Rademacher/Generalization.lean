import StatLean.StatisticalLearning.Rademacher.Symmetrization
import StatLean.ConcentrationInequalities.McDiarmid.McDiarmid

/-!
# Rademacher generalization bounds

The ERM bounds in expectation and via Markov (SSBD Theorem 26.3) and the
high-probability generalization bounds (SSBD Theorem 26.5, parts 1–3, exact
constants): for a family uniformly bounded by `c`, with probability `≥ 1 − δ`,
* (1) `∀f: L_D(f) − L_S(f) ≤ 2 E_{S'} R(𝓕∘S') + c√(2 ln(2/δ)/n)`;
* (2) `∀f: L_D(f) − L_S(f) ≤ 2 R(𝓕∘S) + 4c√(2 ln(4/δ)/n)`;
* (3) ERM vs any fixed `f⋆`: `≤ 2 R(𝓕∘S) + 5c√(2 ln(8/δ)/n)`.

**Reference.** SSBD §26.1, Theorems 26.3 and 26.5, Lemma 26.4 (McDiarmid).
Transcription: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** McDiarmid comes from
`ConcentrationInequalities/McDiarmid/McDiarmid.lean` (bounded differences
`2c/n` for both `sup_k(L_D − L_S)` and `R(𝓕∘S)` as functions of the sample;
this forces the LEAN-ONLY `StandardBorelSpace Z`/`Nonempty Z` instances that
the repo's McDiarmid carries). Part 3 additionally uses one-sided Hoeffding for
the fixed competitor (SSBD Eq. (26.11)) and a union bound. Countable index +
`sSup`-image sups + uniform bound per the batch sup policy.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  {D : Measure Z} [IsProbabilityMeasure D] {n : ℕ}
  {F : ι → Z → ℝ} {K : Set ι} {c : ℝ}

/-- **SSBD Theorem 26.3 (first display)**: an ERM-style selector's expected
overfitting gap is at most twice the expected Rademacher complexity:
`E_S[L_D(A(S)) − L_S(A(S))] ≤ 2 E_S R(F∘S)` whenever `A` selects in `K`. -/
theorem integral_risk_sub_empRisk_le_two_mul_integral_empRad
    {A : Sample Z n → ι}
    -- USER-INPUT: nonempty family; SSBD §26.1 (implicit)
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    -- USER-INPUT: measurability of the family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|f| ≤ c`; SSBD Thm 26.5 setting
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: the selector stays in the family; SSBD §26.1 (ERM ∈ 𝓗)
    (hA : ∀ s, A s ∈ K)
    -- LEAN-ONLY: a.e.-strong measurability of the selected risk/empirical
    -- gap in the sample (the book's `E[…]` presupposes it)
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s) - empRisk F s (A s)) (sampleLaw D n))
    -- USER-INPUT: at least one example; SSBD §26.1 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, (risk D F (A s) - empRisk F s (A s)) ∂(sampleLaw D n) ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  sorry

/-- **SSBD Theorem 26.3 (second display)**: for an ERM selector `A` and any
competitor `kStar ∈ K`,
`E_S[L_D(A(S))] − L_D(kStar) ≤ 2 E_S R(F∘S)`. -/
theorem integral_risk_erm_sub_risk_le_two_mul_integral_empRad
    {A : Sample Z n → ι} {kStar : ι}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: `A` is an ERM selector over `K`; SSBD Thm 26.3
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: the competitor lies in the family; SSBD Thm 26.3
    (hkStar : kStar ∈ K)
    -- LEAN-ONLY: a.e.-strong measurability of the selected risk
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s)) (sampleLaw D n))
    (hn : 1 ≤ n) :
    ∫ s, risk D F (A s) ∂(sampleLaw D n) - risk D F kStar ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  sorry

/-- **SSBD Theorem 26.3 (third display, Markov)**: with probability `≥ 1 − δ`,
the ERM excess risk over the best competitor is at most
`2 E_{S'} R(F∘S')/δ`. -/
theorem measure_erm_excess_le_two_mul_integral_empRad_div
    {A : Sample Z n → ι} {kStar : ι} {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: `kStar` is a risk minimizer of the family (so the excess is
    -- nonnegative and Markov applies); SSBD Thm 26.3
    (hkStar : kStar ∈ K) (hmin : ∀ k ∈ K, risk D F kStar ≤ risk D F k)
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s)) (sampleLaw D n))
    (hn : 1 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 26.3
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | risk D F (A s) - risk D F kStar ≤
        2 * (∫ s', empRad F K s' ∂(sampleLaw D n)) / δ} := by
  sorry

/-- **SSBD Theorem 26.5, part 1**: with probability `≥ 1 − δ`, simultaneously
for every `k ∈ K`,
`L_D(F k) − L_S(F k) ≤ 2 E_{S'∼Dⁿ} R(F∘S') + c √(2 ln(2/δ)/n)`. -/
theorem rademacher_generalization_expected {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|ℓ(h,z)| ≤ c`; SSBD Thm 26.5
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hn : 1 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 26.5
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ k ∈ K,
        risk D F k - empRisk F s k ≤
          2 * (∫ s', empRad F K s' ∂(sampleLaw D n)) +
            c * Real.sqrt (2 * Real.log (2 / δ) / n)} := by
  sorry

/-- **SSBD Theorem 26.5, part 2** (data-dependent bound): with probability
`≥ 1 − δ`, simultaneously for every `k ∈ K`,
`L_D(F k) − L_S(F k) ≤ 2 R(F∘S) + 4c √(2 ln(4/δ)/n)`. -/
theorem rademacher_generalization_empirical {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hn : 1 ≤ n)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ k ∈ K,
        risk D F k - empRisk F s k ≤
          2 * empRad F K s + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / n)} := by
  sorry

/-- **SSBD Theorem 26.5, part 3** (ERM excess risk, data-dependent): for an
ERM selector `A` and any fixed `kStar ∈ K`, with probability `≥ 1 − δ`,
`L_D(A(S)) − L_D(kStar) ≤ 2 R(F∘S) + 5c √(2 ln(8/δ)/n)`. -/
theorem rademacher_erm_excess {A : Sample Z n → ι} {kStar : ι} {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: `A` is an ERM selector over `K`; SSBD Thm 26.5(3)
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: fixed competitor; SSBD Thm 26.5(3) ("for any h⋆")
    (hkStar : kStar ∈ K)
    (hn : 1 ≤ n)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s |
        risk D F (A s) - risk D F kStar ≤
          2 * empRad F K s + 5 * c * Real.sqrt (2 * Real.log (8 / δ) / n)} := by
  sorry

end StatLean.StatisticalLearning
