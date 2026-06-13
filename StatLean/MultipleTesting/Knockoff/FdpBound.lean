import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.Knockoff.Procedure

/-!
# Knock-off deterministic FDP bound (Lu-BDA §19)

`knockoff_fdp_le`: the first display of the knock-off proof, `FDP(t*) ≤ α · V₊(t*)/(1+V₋(t*))`.
Purely deterministic (counting + algebra): `V ≤ |S|`, `FDPhat(t*) ≤ α` (from `tStar`'s `min'`),
and the definitional `FDP = V₊(t*)/(#S⁺(t*) ∨ 1)` for the knock-off rejection set.
-/

open MeasureTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Deterministic FDP bound (Lu-BDA §19, first display of the proof):
`FDP(t*) ≤ α · V₊(t*)/(1 + V₋(t*))`. -/
theorem knockoff_fdp_le (α : ℝ) (hα : 0 < α) (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    FDP H₀ (knockoffRejects W α) ω
      ≤ α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) := by
  sorry

end StatLean.MultipleTesting
