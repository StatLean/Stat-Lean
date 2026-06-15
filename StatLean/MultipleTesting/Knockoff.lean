import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.FdpBound
import StatLean.MultipleTesting.Knockoff.Supermartingale

/-!
# Knock-off FDR control — final assembly (Lu-BDA §19, Theorem `thm:knockoff`)

The knock-off filter at level `α` (procedure in `Knockoff/Procedure.lean`) controls the false
discovery rate: `FDR ≤ α`. This file assembles the two halves:

* `knockoff_fdp_le` (`Knockoff/FdpBound.lean`, deterministic): `FDP(t*) ≤ α · V₊(t*)/(1+V₋(t*))`;
* `knockoff_ratio_stopped_le_one` (`Knockoff/Supermartingale.lean`, the supermartingale +
  optional-stopping core): `E[V₊(t*)/(1+V₋(t*))] ≤ 1`.

Then `FDR = ∫ FDP ≤ ∫ α·V₊/(1+V₋) = α·∫ V₊/(1+V₋) ≤ α` by integral monotonicity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- `α * V₊(t*)/(1+V₋(t*))` is μ-integrable: via `ratio_eq_stoppedValue` it equals
`α * stoppedValue (Yproc W H₀) (tauStar W H₀ α)`, and the stopped value is integrable from
`Submartingale.integrable_stoppedValue` applied to the negated supermartingale. -/
private lemma ratio_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Integrable (fun ω =>
      α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ))) μ := by
  haveI : SigmaFiniteFiltration μ (𝒢rev W H₀ hW.meas) := inferInstance
  -- Rewrite ratio as α * stoppedValue Yproc tauStar
  simp_rw [mul_div_assoc, ratio_eq_stoppedValue]
  -- Integrability from the negated supermartingale (= submartingale)
  have hstop_neg : Integrable (stoppedValue (-(Yproc W H₀)) (tauStar W H₀ α)) μ :=
    (knockoff_supermartingale W H₀ μ hW hmag).neg.integrable_stoppedValue
      (tauStar_isStoppingTime W H₀ α hW.meas) (tauStar_le W H₀ α)
  have hstop : Integrable (stoppedValue (Yproc W H₀) (tauStar W H₀ α)) μ := by
    have heq : stoppedValue (-(Yproc W H₀)) (tauStar W H₀ α) =
               -(stoppedValue (Yproc W H₀) (tauStar W H₀ α)) := by
      ext ω; simp [stoppedValue, Pi.neg_apply]
    rw [heq] at hstop_neg
    -- hstop_neg : Integrable (-(stoppedValue Yproc ...)) μ; negate twice
    simpa only [neg_neg] using hstop_neg.neg
  exact Integrable.const_mul hstop α

/-- **Knock-off FDR control** (Lu-BDA §19, Theorem `thm:knockoff`). For a knock-off score `W`, the
knock-off procedure at level `α` controls the false discovery rate: `FDR ≤ α`. -/
theorem knockoff_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ) (hα : 0 < α)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    -- LEAN-ONLY: no ties on null scores (`Wⱼ ≠ 0` a.s.), so the sign is well-defined; Lu-BDA §19
    (hties : ∀ j ∈ H₀, ∀ᵐ ω ∂μ, W j ω ≠ 0)
    -- USER-INPUT: a.s. distinct magnitudes (continuous knock-off statistics, no |Wᵢ| ties); Lu-BDA §19
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    FDR H₀ (knockoffRejects W α) μ ≤ α := by
  simp only [FDR]
  calc ∫ ω, FDP H₀ (knockoffRejects W α) ω ∂μ
      -- Step 1: FDP ≤ α · ratio pointwise → integrate monotonically
      ≤ ∫ ω, α * (Vplus W H₀ (tStar W α ω) ω : ℝ) /
             (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ :=
        integral_mono_of_nonneg
          -- FDP ≥ 0: numerator (Nat cast) ≥ 0, denominator max(R,1) ≥ 1 ≥ 0
          (Filter.Eventually.of_forall fun ω =>
            div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_right _ _)))
          -- α · ratio integrable
          (ratio_integrable μ α W H₀ hW hmag)
          -- FDP ≤ α · ratio a.e. (deterministic, pointwise)
          (Filter.Eventually.of_forall fun ω => knockoff_fdp_le α hα W H₀ ω)
      -- Step 2: factor α out of the integral
    _ = α * ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) /
                 (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ := by
        simp_rw [mul_div_assoc]; exact integral_const_mul α _
      -- Step 3: ∫ ratio ≤ 1, so α · ∫ ratio ≤ α · 1 = α
    _ ≤ α * 1 :=
        mul_le_mul_of_nonneg_left (knockoff_ratio_stopped_le_one μ α W H₀ hW hmag) hα.le
    _ = α := mul_one α

end StatLean.MultipleTesting
