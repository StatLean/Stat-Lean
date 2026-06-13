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

/-- **Knock-off FDR control** (Lu-BDA §19, Theorem `thm:knockoff`). For a knock-off score `W`, the
knock-off procedure at level `α` controls the false discovery rate: `FDR ≤ α`. -/
theorem knockoff_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ) (hα : 0 < α)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    -- LEAN-ONLY: no ties on null scores (`Wⱼ ≠ 0` a.s.), so the sign is well-defined; Lu-BDA §19
    (hties : ∀ j ∈ H₀, ∀ᵐ ω ∂μ, W j ω ≠ 0) :
    FDR H₀ (knockoffRejects W α) μ ≤ α := by
  sorry

end StatLean.MultipleTesting
