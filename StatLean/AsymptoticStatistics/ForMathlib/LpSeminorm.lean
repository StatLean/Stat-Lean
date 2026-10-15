/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The `L^p` seminorm without a measurability guard

`MeasureTheory.eLpNorm f p μ` is `∞` when `f` is not a.e. strongly measurable. This file
defines `eLpNorm₀`, which is given by the same formula for every function: `0` at `p = 0`,
the essential supremum at `p = ∞`, and the integral seminorm `eLpNorm'` otherwise. It only
needs an `ENorm` on the target. The two seminorms agree on a.e. strongly measurable functions
(`eLpNorm₀_eq_eLpNorm`).
-/

namespace MeasureTheory
open scoped ENNReal

/-- The `L^p` seminorm of an arbitrary function, without the a.e. strong measurability
guard of `eLpNorm`. -/
noncomputable def eLpNorm₀ {α E : Type*} [MeasurableSpace α] [ENorm E]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ

/-- At exponent two, `eLpNorm₀` is the integral seminorm `eLpNorm'`. -/
theorem eLpNorm₀_two {α E : Type*} [MeasurableSpace α] [ENorm E]
    (f : α → E) (μ : Measure α) : eLpNorm₀ f 2 μ = eLpNorm' f 2 μ := by
  norm_num [eLpNorm₀]

/-- `eLpNorm₀` agrees with `eLpNorm` on a.e. strongly measurable functions. -/
theorem eLpNorm₀_eq_eLpNorm {α E : Type*} [MeasurableSpace α] [ENorm E]
    [TopologicalSpace E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}
    (hf : AEStronglyMeasurable f μ) : eLpNorm₀ f p μ = eLpNorm f p μ := by
  simp only [eLpNorm₀, eLpNorm, hf, ite_true]

variable {α ε : Type*} [MeasurableSpace α] [ENorm ε] [TopologicalSpace ε]
  {μ : Measure α} {f : α → ε}

/-- On a.e. strongly measurable functions, `eLpNorm f 2` is the integral seminorm. -/
theorem eLpNorm_two_eq_eLpNorm' (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = eLpNorm' f 2 μ := by
  simpa only [ENNReal.toReal_ofNat] using
    eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hf

/-- The integral seminorm `eLpNorm' f 2` is bounded by `eLpNorm f 2` for every function. -/
theorem eLpNorm'_two_le_eLpNorm : eLpNorm' f 2 μ ≤ eLpNorm f 2 μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [eLpNorm_two_eq_eLpNorm' hf]
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

end MeasureTheory
