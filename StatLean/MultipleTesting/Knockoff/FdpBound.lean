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

/-- Core algebraic inequality: `vp/max(sp,1) ≤ α·vp/(1+vm)` given `(sm+1)/max(sp,1) ≤ α`,
`vm ≤ sm`, `α > 0`. -/
private lemma fdp_le_core (α : ℝ) (hα : 0 < α) (vp sp vm sm : ℕ) (hvm : vm ≤ sm)
    (hfdphat : ((sm : ℝ) + 1) / max (sp : ℝ) 1 ≤ α) :
    (vp : ℝ) / max (sp : ℝ) 1 ≤ α * (vp : ℝ) / (1 + (vm : ℝ)) := by
  have hM : (0 : ℝ) < max (↑sp) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hvm1 : (0 : ℝ) < 1 + (↑vm : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos vp with rfl | hvp0
  · simp
  · have hkey : (1 : ℝ) + ↑vm ≤ α * max (↑sp) 1 := by
      have h1 : (↑sm : ℝ) + 1 ≤ α * max (↑sp) 1 := (div_le_iff₀ hM).mp hfdphat
      have h2 : (↑vm : ℝ) ≤ ↑sm := Nat.cast_le.mpr hvm
      linarith
    rw [div_le_div_iff₀ hM hvm1]
    have hvp_r : (0 : ℝ) ≤ ↑vp := Nat.cast_nonneg _
    have key : (↑vp : ℝ) * (1 + ↑vm) ≤ ↑vp * (α * max (↑sp) 1) :=
      mul_le_mul_of_nonneg_left hkey hvp_r
    linarith [show (↑vp : ℝ) * (α * max (↑sp : ℝ) 1) = α * ↑vp * max (↑sp : ℝ) 1 from by ring]

/-- Deterministic FDP bound (Lu-BDA §19, first display of the proof):
`FDP(t*) ≤ α · V₊(t*)/(1 + V₋(t*))`. -/
theorem knockoff_fdp_le (α : ℝ) (hα : 0 < α) (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    FDP H₀ (knockoffRejects W α) ω
      ≤ α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) := by
  simp only [FDP, numFalseRejections, numRejections, knockoffRejects, tStar, Vplus, Vminus]
  split_ifs with h
  · -- Nonempty: t* = cands.min' h; FDPhat(t*) ≤ α from filter membership
    have hfdphat : FDPhat W
        ((Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α) |>.min' h) ω ≤ α :=
      (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
    simp only [FDPhat] at hfdphat
    exact fdp_le_core α hα _ _ _ _ (Finset.card_le_card Finset.inter_subset_left) hfdphat
  · -- Empty: knockoffRejects = ∅, FDP = 0 ≤ nonneg RHS
    simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero, zero_div]
    exact div_nonneg (mul_nonneg hα.le (Nat.cast_nonneg _)) (by positivity)

end StatLean.MultipleTesting
