import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Asymptotic Statistics — Bochner-integral Markov utilities.

Pointwise and set-integral lemmas of Markov / Chebyshev flavour, stated for Bochner
integrals of real-valued functions. All theorem-agnostic.

## Contents

* `setIntegral_le_const_mul_of_threshold` — if `c < f` on a measurable set `S`
  and `p ≥ 0`, then `∫_S p dμ ≤ c⁻¹ · ∫_S f · p dμ`.
* `setIntegral_union_le_add_of_nonneg` — for `f ≥ 0`,
  `∫_{A ∪ B} f dμ ≤ ∫_A f dμ + ∫_B f dμ` (even for overlapping `A, B`).
-/

open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace ForMathlib

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Markov inequality for a set integral with a nonneg weight.**

On a measurable set `S` where `c < f`, if the weight `p` is nonnegative then
`∫_S p dμ ≤ c⁻¹ · ∫_S f · p dμ`.

Proof. On `S` the pointwise bound `p ≤ c⁻¹ · f · p` follows from `1 < c⁻¹ · f`
(since `c > 0` and `c < f`) and `p ≥ 0`. Monotonicity of `setIntegral` then
gives the inequality; pull `c⁻¹` out via `integral_const_mul`. -/
lemma setIntegral_le_const_mul_of_threshold
    {f p : α → ℝ} {S : Set α} {c : ℝ}
    (hc_pos : 0 < c) (hS_meas : MeasurableSet S)
    (hS_bound : ∀ x ∈ S, c < f x)
    (hp_nn : ∀ x ∈ S, 0 ≤ p x)
    (hp_int : IntegrableOn p S μ)
    (hfp_int : IntegrableOn (fun x => f x * p x) S μ) :
    ∫ x in S, p x ∂μ ≤ c⁻¹ * ∫ x in S, f x * p x ∂μ := by
  have h_pt : ∀ x ∈ S, p x ≤ c⁻¹ * (f x * p x) := by
    intro x hxS
    have hf : c < f x := hS_bound x hxS
    have hp : 0 ≤ p x := hp_nn x hxS
    have h_factor : 1 ≤ c⁻¹ * f x := by
      rw [← div_eq_inv_mul, le_div_iff₀ hc_pos, one_mul]
      exact hf.le
    calc p x = 1 * p x := (one_mul _).symm
      _ ≤ (c⁻¹ * f x) * p x := mul_le_mul_of_nonneg_right h_factor hp
      _ = c⁻¹ * (f x * p x) := by ring
  have h_step1 :
      ∫ x in S, p x ∂μ ≤ ∫ x in S, c⁻¹ * (f x * p x) ∂μ :=
    MeasureTheory.setIntegral_mono_on hp_int (hfp_int.const_mul _) hS_meas h_pt
  simpa [MeasureTheory.integral_const_mul] using h_step1

/-- **Set-integral subadditivity on a possibly-overlapping union** (nonneg weight).

For `f ≥ 0`, `∫_{A ∪ B} f dμ ≤ ∫_A f dμ + ∫_B f dμ`.

Proof. Split `A ∪ B = A ⊔ (B \ A)` (disjoint) and use `setIntegral_union` for the
equality `∫_{A ∪ B} = ∫_A + ∫_{B\A}`. Then `B \ A ⊆ B` and `f ≥ 0` give
`∫_{B\A} f ≤ ∫_B f` by `setIntegral_mono_set`. -/
lemma setIntegral_union_le_add_of_nonneg
    {f : α → ℝ} {A B : Set α}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_A : IntegrableOn f A μ) (hf_B : IntegrableOn f B μ) :
    ∫ x in A ∪ B, f x ∂μ ≤ ∫ x in A, f x ∂μ + ∫ x in B, f x ∂μ := by
  have hBdiffA_meas : MeasurableSet (B \ A) := hB_meas.diff hA_meas
  have hBdiffA_sub : B \ A ⊆ B := Set.diff_subset
  have h_union_eq : A ∪ B = A ∪ (B \ A) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    tauto
  have h_disj : Disjoint A (B \ A) := by
    rw [Set.disjoint_left]
    intro x hxA ⟨_, hxnA⟩; exact hxnA hxA
  have hf_BdiffA : IntegrableOn f (B \ A) μ :=
    hf_B.mono_set hBdiffA_sub
  have h_split : ∫ x in A ∪ B, f x ∂μ = ∫ x in A, f x ∂μ + ∫ x in B \ A, f x ∂μ := by
    rw [h_union_eq, MeasureTheory.setIntegral_union h_disj hBdiffA_meas hf_A hf_BdiffA]
  have h_mono : ∫ x in B \ A, f x ∂μ ≤ ∫ x in B, f x ∂μ := by
    refine MeasureTheory.setIntegral_mono_set hf_B ?_ ?_
    · exact Filter.Eventually.of_forall (fun x => hf_nn x)
    · exact Filter.Eventually.of_forall hBdiffA_sub
  linarith

end ForMathlib
end AsymptoticStatistics
