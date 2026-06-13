import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-exponential random variables — definition

Book definition (Lu, *Big Data Analysis* §3.2, "Sub-Exponential"): a random
variable `X` is *sub-exponential with parameter `α`* if
`E[exp(λ (X − E X))] ≤ exp(λ² α² / 2)` for all `|λ| ≤ 1/α`.

The key difference from sub-Gaussian is the **restricted range** of `λ`: the
sub-Gaussian MGF bound holds for all `λ ∈ ℝ`, whereas the sub-exponential bound
holds only on `|λ| ≤ 1/α`. Mathlib has no predicate for this restricted-range
MGF bound, so we build it here as a structure over the **centered** variable
`X − E[X]`, mirroring the shape of `ProbabilityTheory.HasSubgaussianMGF`
(an MGF-bound field plus an integrability field).

This is a concept-layer foundation: the sub-exponential tail bound
(`thm:sub-exp`), the sample-mean concentration, and the Bernstein machinery
(ch. 4) all consume `IsSubExponential`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubExponential X α μ`: the random variable `X` is sub-exponential with
parameter `α` under `μ`, i.e. its centered moment generating function satisfies
`E[exp(λ (X − E[X]))] ≤ exp(λ² α² / 2)` for every `λ` with `|λ| ≤ 1/α`
(Lu-BDA §3.2, "Sub-Exponential").

The centered variable is `fun ω => X ω − ∫ x, X x ∂μ`; the mean is the Bochner
integral (Mathlib junk value `0` for non-integrable `X`). For the degenerate
`α = 0` the range collapses to `λ = 0` (`1/0 = 0` in `ℝ`), where the bound reads
`mgf … 0 ≤ 1`. -/
structure IsSubExponential (X : Ω → ℝ) (α : ℝ≥0) (μ : Measure Ω := by volume_tac) :
    Prop where
  /-- Constitutive (Lu-BDA §3.2, Sub-Exponential): on the restricted range
  `|λ| ≤ 1/α`, the centered MGF obeys the sub-Gaussian-type bound
  `mgf (X − E X) λ ≤ exp(λ² α² / 2)`. Removing this makes the object not the
  book's sub-exponential variable. -/
  mgf_le : ∀ l : ℝ, |l| ≤ 1 / (α : ℝ) →
    mgf (fun ω => X ω - ∫ x, X x ∂μ) μ l ≤ Real.exp (l ^ 2 * (α : ℝ) ^ 2 / 2)
  /-- Regularity (LEAN-ONLY): integrability of the centered exponential on the
  range, so that `mgf` is the genuine integral rather than Mathlib's junk `0`.
  Bundled to mirror Mathlib's `HasSubgaussianMGF.integrable_exp_mul`; the book
  leaves it implicit (the MGF is assumed to exist on the range). -/
  integrable_exp_mul : ∀ l : ℝ, |l| ≤ 1 / (α : ℝ) →
    Integrable (fun ω => Real.exp (l * (X ω - ∫ x, X x ∂μ))) μ

/-- The centered MGF bound carried by `IsSubExponential`, extracted for the
range `0 ≤ l ≤ 1/α` used by the one-sided Chernoff tail (`thm:sub-exp`). -/
theorem IsSubExponential.mgf_le_of_mem_Icc {X : Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubExponential X α μ) {l : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1 / (α : ℝ)) :
    mgf (fun ω => X ω - ∫ x, X x ∂μ) μ l ≤ Real.exp (l ^ 2 * (α : ℝ) ^ 2 / 2) :=
  hX.mgf_le l (by rw [abs_of_nonneg hl₀]; exact hl₁)

end StatLean.ConcentrationInequalities
