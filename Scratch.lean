import StatLean.StatisticalLearning.Core.SampleLaw
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal NNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ} {ℓ : H → Z → ℝ}

theorem uniformDeviation' (𝓗 : Finset H) {ε : ℝ}
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h))
    (hn : 1 ≤ n)
    (hε : 0 < ε) :
    sampleLaw D n {s | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal (2 * 𝓗.card * Real.exp (-2 * n * ε ^ 2)) := by
  sorry

theorem uc' (𝓗 : Finset H)
    (h𝓗 : 𝓗.Nonempty)
    (hrange : ∀ h ∈ 𝓗, ∀ z, ℓ h z ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ h ∈ 𝓗, Measurable (ℓ h)) :
    HasUniformConvergenceWith (↑𝓗 : Set H) ℓ
      (fun ε δ => ⌈Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2)⌉₊) := by
  intro D hD ε δ hε hδ hδ1 n hn
  haveI := hD
  have hN1 : (1 : ℝ) ≤ (𝓗.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr h𝓗
  have hlogpos : 0 < Real.log (2 * 𝓗.card / δ) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ]
    nlinarith
  have hquot : 0 < Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2) := by positivity
  -- the sample size is at least one
  have hn1 : 1 ≤ n := le_trans (Nat.ceil_pos.mpr hquot) hn
  -- the book's arithmetic: `2 N e^{-2 n ε²} ≤ δ`
  have hnR : Real.log (2 * 𝓗.card / δ) / (2 * ε ^ 2) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlog_le : Real.log (2 * 𝓗.card / δ) ≤ 2 * n * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hnR
    nlinarith
  have hinv : (2 * (𝓗.card : ℝ) / δ)⁻¹ = Real.exp (-Real.log (2 * 𝓗.card / δ)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  have hexp : Real.exp (-2 * n * ε ^ 2) ≤ (2 * (𝓗.card : ℝ) / δ)⁻¹ := by
    rw [hinv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound : 2 * (𝓗.card : ℝ) * Real.exp (-2 * n * ε ^ 2) ≤ δ := by
    have h2N : (0 : ℝ) < 2 * (𝓗.card : ℝ) := by linarith
    calc 2 * (𝓗.card : ℝ) * Real.exp (-2 * n * ε ^ 2)
        ≤ 2 * (𝓗.card : ℝ) * (2 * (𝓗.card : ℝ) / δ)⁻¹ :=
          mul_le_mul_of_nonneg_left hexp h2N.le
      _ = δ := by field_simp
  -- the bad event
  have hbad : sampleLaw D n {s | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} ≤
      ENNReal.ofReal δ := by
    refine (uniformDeviation' 𝓗 hrange hmeas hn1 hε).trans ?_
    exact ENNReal.ofReal_le_ofReal hbound
  have hcompl : {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ ⊆
      {s : Sample Z n | ∃ h ∈ 𝓗, ε < |empRisk ℓ s h - risk D ℓ h|} := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, UniformDeviationLE, not_forall,
      Finset.mem_coe, not_le] at hs
    obtain ⟨h, hh, hlt⟩ := hs
    exact ⟨h, hh, hlt⟩
  have hcover : (1 : ℝ≥0∞) ≤
      sampleLaw D n {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε} +
        sampleLaw D n {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ := by
    have h := measure_union_le (μ := sampleLaw D n)
      {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}
      {s : Sample Z n | UniformDeviationLE D (↑𝓗 : Set H) ℓ s ε}ᶜ
    rwa [Set.union_compl_self, measure_univ] at h
  rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
  refine tsub_le_iff_right.mpr ?_
  refine hcover.trans ?_
  gcongr
  exact (measure_mono hcompl).trans hbad

end StatLean.StatisticalLearning
