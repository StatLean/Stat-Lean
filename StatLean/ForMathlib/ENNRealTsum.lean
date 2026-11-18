/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of countable sums in `ℝ≥0∞`

`Measurable.tsum` takes the σ-algebra on the domain as an instance argument.
`ENNReal.measurable_tsum` takes it as an implicit argument, so it also applies to statements about
a sub-σ-algebra, written `Measurable[m]`.
-/

open MeasureTheory

namespace ENNReal

/-- A countable sum of measurable `ℝ≥0∞`-valued functions is measurable, for any σ-algebra on the
domain. -/
theorem measurable_tsum {α ι : Type*} {m : MeasurableSpace α} [Countable ι]
    {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable[m] (f i)) :
    Measurable[m] fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s => s.measurable_fun_sum fun i _ => h i

end ENNReal
