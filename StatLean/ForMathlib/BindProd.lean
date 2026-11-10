/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Products of arbitrary measures

`MeasureTheory.Measure.prod μ ν` is `μ.bind (fun x ↦ ν.map (Prod.mk x))` when `ν` is s-finite and
`0` otherwise. `Measure.bindProd μ ν` is given by the `bind` formula for all measures. StatLean
uses it in definitions that take arbitrary measures, so that their value does not drop to `0` when
the second factor is not s-finite.

`bindProd_eq_prod` identifies the two products when `ν` is s-finite, in particular for finite and
probability measures.
-/

open MeasureTheory

namespace MeasureTheory.Measure

universe u v
variable {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]

/-- The product of two arbitrary measures, `μ.bind (fun x ↦ ν.map (Prod.mk x))`. It is `μ.prod ν`
when `ν` is s-finite (`bindProd_eq_prod`). -/
noncomputable def bindProd (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ (fun x : α => map (Prod.mk x) ν)

@[simp] theorem bindProd_eq_prod (μ : Measure α) (ν : Measure β) [SFinite ν] :
    μ.bindProd ν = μ.prod ν :=
  (prod_eq_of_sfinite μ ν).symm

instance (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.bindProd ν) := by
  rw [bindProd_eq_prod]
  infer_instance

instance (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.bindProd ν) := by
  rw [bindProd_eq_prod]
  infer_instance

instance (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    SFinite (μ.bindProd ν) := by
  rw [bindProd_eq_prod]
  infer_instance

-- This explicit dictionary is intentionally semireducible.
set_option warn.classDefReducibility false in
/-- The product volume `volume.bindProd volume` on `α × β`. It is not registered as an instance,
so it does not compete with `Measure.prod.measureSpace`. -/
noncomputable def bindProdMeasureSpace {α : Type u} {β : Type v}
    [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := (volume : Measure α).bindProd (volume : Measure β)

end MeasureTheory.Measure
