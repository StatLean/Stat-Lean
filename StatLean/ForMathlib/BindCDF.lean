/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.Probability.CDF
import StatLean.ForMathlib.BindProd

/-!
# Cumulative distribution functions of arbitrary real measures

`ProbabilityTheory.cdf μ` is the conditional CDF of the product `(dirac ()).prod μ`, which is `0`
when `μ` is not s-finite. `bindCDF μ` is the same construction with `Measure.bindProd` in place of
`Measure.prod`. StatLean uses it in definitions that take an arbitrary measure on `ℝ`.

`bindCDF_eq_cdf` identifies the two functions for s-finite measures, and `bindCDF_eq_real` gives
`bindCDF μ x = μ.real (Iic x)` for probability measures.
-/

namespace ProbabilityTheory

open MeasureTheory Filter Set
open scoped Topology

/-- The cumulative distribution function of an arbitrary measure on `ℝ`, built from the product
`(dirac ()).bindProd μ`. It is `cdf μ` when `μ` is s-finite (`bindCDF_eq_cdf`). -/
noncomputable def bindCDF (μ : Measure ℝ) : StieltjesFunction ℝ :=
  condCDF ((Measure.dirac Unit.unit).bindProd μ) Unit.unit

@[simp] theorem bindCDF_eq_cdf (μ : Measure ℝ) [SFinite μ] : bindCDF μ = cdf μ := by
  unfold bindCDF cdf
  rw [Measure.bindProd_eq_prod]

theorem bindCDF_nonneg (μ : Measure ℝ) (x : ℝ) : 0 ≤ bindCDF μ x :=
  condCDF_nonneg _ _ _

theorem bindCDF_le_one (μ : Measure ℝ) (x : ℝ) : bindCDF μ x ≤ 1 :=
  condCDF_le_one _ _ _

theorem monotone_bindCDF (μ : Measure ℝ) : Monotone (bindCDF μ) :=
  (bindCDF μ).mono

theorem tendsto_bindCDF_atBot (μ : Measure ℝ) : Tendsto (bindCDF μ) atBot (𝓝 0) :=
  tendsto_condCDF_atBot _ _

theorem tendsto_bindCDF_atTop (μ : Measure ℝ) : Tendsto (bindCDF μ) atTop (𝓝 1) :=
  tendsto_condCDF_atTop _ _

theorem bindCDF_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    bindCDF μ x = μ.real (Iic x) := by
  rw [bindCDF_eq_cdf]
  exact cdf_eq_real μ x

end ProbabilityTheory
