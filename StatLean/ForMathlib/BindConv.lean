/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Group.Convolution
import StatLean.ForMathlib.BindProd

/-!
# Convolution of arbitrary measures

`MeasureTheory.Measure.conv μ ν` is the pushforward of `μ.prod ν` under addition, so it is `0`
when `ν` is not s-finite. `Measure.bindConv μ ν` is the pushforward of `μ.bindProd ν` under
addition. `bindConv_eq_conv` identifies the two convolutions when `ν` is s-finite.
-/

open MeasureTheory

namespace MeasureTheory.Measure

universe u
variable {M : Type u} [AddMonoid M] [MeasurableSpace M]

/-- The convolution of two arbitrary measures, the pushforward of `μ.bindProd ν` under
addition. It is `Measure.conv μ ν` when `ν` is s-finite (`bindConv_eq_conv`). -/
noncomputable def bindConv (μ ν : Measure M) : Measure M :=
  map (fun x : M × M => x.1 + x.2) (μ.bindProd ν)

@[simp] theorem bindConv_eq_conv (μ ν : Measure M) [SFinite ν] :
    μ.bindConv ν = Measure.conv μ ν := by
  rw [Measure.conv, bindConv, bindProd_eq_prod]

end MeasureTheory.Measure
