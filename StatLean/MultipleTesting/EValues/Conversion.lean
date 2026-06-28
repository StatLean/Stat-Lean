import StatLean.MultipleTesting.EValues.Defs
import StatLean.MultipleTesting.PValues.Defs

/-!
# E-to-p conversion — assembly (Candès, Lecture 15, Prop. 3, STAT 300C Notes)

**Main result** (`isPVariable_inv_of_isEVariable`): if `E` is an e-variable for the simple null
`μ`, then its reciprocal `1/E` is a p-variable (a *conservative* p-value):
`μ{1/E ≤ α} ≤ α` for every `α ∈ (0,1)`.

*Proof (Markov).* Fix `α ∈ (0,1)`. With `E > 0`, `1/E ≤ α ⟺ E ≥ 1/α`, so by Markov's inequality
`μ{E ≥ 1/α} ≤ α · Eμ[E] ≤ α` (using `Eμ[E] ≤ 1`).

We also record that `1/E` is [[`SuperUniform`]] (`superUniform_inv_of_isEVariable`), the form the
Benjamini–Hochberg / Holm assembly files consume — so e-values feed directly into FDR control.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The reciprocal of an e-variable is [[`SuperUniform`]] — the null-p-value hypothesis consumed by
`benjamini_hochberg_fdr_le` / the Holm assembly. Corollary of `isPVariable_inv_of_isEVariable`
extended from `(0,1)` to all `t ≥ 0`. -/
theorem superUniform_inv_of_isEVariable {E : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: E is an e-variable for the null μ; Candès L15 Def. 3
    (hE : IsEVariable E μ)
    -- LEAN-ONLY: E positive (see `isPVariable_inv_of_isEVariable`)
    (hpos : ∀ ω, 0 < E ω) :
    SuperUniform (fun ω => 1 / E ω) μ := by
  intro t ht
  -- For `t = 0`: `E > 0 ⟹ 1/E > 0`, so the event is empty.
  rcases ht.eq_or_lt with rfl | ht
  · have hempty : {ω | 1 / E ω ≤ (0 : ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, one_div]
      exact inv_pos.mpr (hpos ω)
    rw [hempty, measure_empty]
    exact zero_le _
  -- For `t > 0`: rewrite the event in `ofReal` form and apply lintegral Markov.
  have hset : {ω | 1 / E ω ≤ t} = {ω | ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal (E ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (hE.nonneg ω), one_div, inv_le_comm₀ (hpos ω) ht]
  rw [hset]
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (E ω)) μ :=
    (ENNReal.measurable_ofReal.comp hE.measurable).aemeasurable
  have hε0 : ENNReal.ofReal t⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr ht)).ne'
  have hεtop : ENNReal.ofReal t⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  calc μ {ω | ENNReal.ofReal t⁻¹ ≤ ENNReal.ofReal (E ω)}
      ≤ (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) / ENNReal.ofReal t⁻¹ :=
        meas_ge_le_lintegral_div hmeas hε0 hεtop
    _ ≤ 1 / ENNReal.ofReal t⁻¹ := ENNReal.div_le_div_right hE.expectation_le_one _
    _ = ENNReal.ofReal t := by rw [one_div, ENNReal.ofReal_inv_of_pos ht, inv_inv]

/-- **E-to-p conversion** (Candès, Lecture 15, Prop. 3, STAT 300C). If `E` is an e-variable for the
simple null `μ`, then `1/E` is a p-variable. Proof by Markov: `μ{E ≥ 1/α} ≤ α·Eμ[E] ≤ α`. -/
theorem isPVariable_inv_of_isEVariable {E : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: E is an e-variable for the null μ; Candès L15 Def. 3
    (hE : IsEVariable E μ)
    -- LEAN-ONLY: E is (pointwise) positive, so `1/E` is the genuine `(0,∞]`-valued reciprocal
    -- p-value. Lean's `1/0 = 0` convention would otherwise map the no-evidence event `E = 0`
    -- (p-value 1) to `1/E = 0`, spuriously inflating `μ{1/E ≤ α}`. E-variables arising as
    -- likelihood ratios are positive, so this is no loss of generality.
    (hpos : ∀ ω, 0 < E ω) :
    IsPVariable (fun ω => 1 / E ω) μ := by
  intro α hα _
  exact superUniform_inv_of_isEVariable hE hpos α hα.le

end StatLean.MultipleTesting
