/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Pushforward with a zero fallback

When `f` is not a.e. measurable and `μ ≠ 0`, `Measure.map f μ` is an arbitrary Dirac mass.
`Measure.map₀ f μ` is `μ.map f` when `f` is a.e. measurable and `0` otherwise. StatLean uses it
in definitions that quantify over arbitrary functions, so that the law of a map that is not
a.e. measurable is the zero measure.
-/

open MeasureTheory
namespace MeasureTheory.Measure
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {f : α → β} {g : β → γ}

/-- The pushforward of `μ` along `f` if `f` is a.e. measurable, and `0` otherwise. -/
noncomputable def map₀ (f : α → β) (μ : Measure α) : Measure β := by
  classical
  exact if AEMeasurable f μ then μ.map f else 0

@[simp] theorem map₀_of_aemeasurable (hf : AEMeasurable f μ) : μ.map₀ f = μ.map f := by
  simp [map₀, hf]

@[simp] theorem map₀_of_measurable (hf : Measurable f) : μ.map₀ f = μ.map f :=
  map₀_of_aemeasurable hf.aemeasurable

@[simp] theorem map₀_of_not_aemeasurable (hf : ¬ AEMeasurable f μ) : μ.map₀ f = 0 := by
  simp [map₀, hf]

@[simp] theorem map₀_zero (f : α → β) : (0 : Measure α).map₀ f = 0 := by
  unfold map₀
  split_ifs <;> simp

@[simp] theorem map₀_id : μ.map₀ id = μ := by
  rw [map₀_of_aemeasurable measurable_id.aemeasurable, Measure.map_id]

@[simp] theorem map₀_id' : μ.map₀ (fun x => x) = μ := map₀_id

theorem map₀_eq_zero_iff (hf : AEMeasurable f μ) : μ.map₀ f = 0 ↔ μ = 0 := by
  rw [map₀_of_aemeasurable hf, Measure.map_eq_zero_iff hf]

theorem aemeasurable_of_map₀_ne_zero (h : μ.map₀ f ≠ 0) : AEMeasurable f μ := by
  by_contra hf
  exact h (map₀_of_not_aemeasurable hf)

theorem map₀_congr {f g : α → β} (h : f =ᵐ[μ] g) : μ.map₀ f = μ.map₀ g := by
  by_cases hf : AEMeasurable f μ
  · rw [map₀_of_aemeasurable hf, map₀_of_aemeasurable (hf.congr h), Measure.map_congr h]
  · rw [map₀_of_not_aemeasurable hf, map₀_of_not_aemeasurable]
    simpa only [← aemeasurable_congr h] using hf

theorem map₀_map_of_aemeasurable (hg : AEMeasurable g (μ.map₀ f)) (hf : AEMeasurable f μ) :
    (μ.map₀ f).map₀ g = μ.map₀ (g ∘ f) := by
  rw [map₀_of_aemeasurable hf] at hg ⊢
  rw [map₀_of_aemeasurable hg, map₀_of_aemeasurable (hg.comp_aemeasurable hf)]
  exact AEMeasurable.map_map_of_aemeasurable hg hf

instance instSFiniteMap₀ [SFinite μ] : SFinite (μ.map₀ f) := by
  unfold map₀
  split_ifs <;> infer_instance

/-- `μ.map₀ f` is a finite measure whenever `μ` is, for every function `f`. -/
instance instIsFiniteMeasureMap₀ [IsFiniteMeasure μ] : IsFiniteMeasure (μ.map₀ f) := by
  unfold map₀
  split_ifs <;> infer_instance

end MeasureTheory.Measure
