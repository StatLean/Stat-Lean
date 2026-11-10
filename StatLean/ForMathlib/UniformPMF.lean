/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform probability mass functions on finite sets

`PMF.uniformOn s hs` is the uniform probability mass function on a nonempty finset `s`, and
`PMF.uniform α` is the uniform probability mass function on a nonempty finite type: every point of
the support has probability the reciprocal of its cardinality. Mathlib represents these laws as
measures (`MeasureTheory.Measure.uniformOfFinset`). StatLean's sampling and randomization designs
are probability mass functions and use the constructors below.
-/

noncomputable section

namespace PMF

open scoped ENNReal

variable {α : Type*}

/-- The uniform probability mass function on a nonempty finset `s`. -/
def uniformOn (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine PMF.ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, ite_false]

open scoped Classical in
@[simp]
theorem uniformOn_apply {s : Finset α} (hs : s.Nonempty) (a : α) :
    uniformOn s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := rfl

theorem uniformOn_apply_of_mem {s : Finset α} (hs : s.Nonempty) {a : α} (ha : a ∈ s) :
    uniformOn s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

theorem uniformOn_apply_of_notMem {s : Finset α} (hs : s.Nonempty) {a : α} (ha : a ∉ s) :
    uniformOn s hs a = 0 := by
  simp [ha]

theorem mem_support_uniformOn_iff {s : Finset α} (hs : s.Nonempty) (a : α) :
    a ∈ (uniformOn s hs).support ↔ a ∈ s := by
  simp [PMF.mem_support_iff]

/-- The uniform probability mass function on a nonempty finite type. -/
def uniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOn Finset.univ Finset.univ_nonempty

@[simp]
theorem uniform_apply [Fintype α] [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniform, uniformOn_apply]

end PMF
