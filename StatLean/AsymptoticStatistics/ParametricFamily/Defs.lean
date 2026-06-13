import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
Asymptotic Statistics — Parametric family of densities.

Defines `ParametricFamily`, the measurable family of densities `θ ↦ p_θ`
w.r.t. a dominating measure μ, and its square-root density `√p_θ` with
the basic measurability / positivity / `L²(μ)` facts.
-/

open MeasureTheory

namespace AsymptoticStatistics

/-- A parametric family of (μ-)densities indexed by a parameter `θ : Θ`.

We package the joint measurability/non-negativity assumptions into the structure so that
downstream lemmas can use them without reproving. -/
structure ParametricFamily
    (𝓧 : Type*) [MeasurableSpace 𝓧] (Θ : Type*) where
  /-- Density `p_θ(x)`. -/
  density : Θ → 𝓧 → ℝ
  density_meas : ∀ θ, Measurable (density θ)
  density_nonneg : ∀ θ x, 0 ≤ density θ x

/-- **PDF conditions**: the family `M` is a probability-density family with respect to
the dominating measure `μ`. Bundles the two universal regularity conditions that
typically appear as separate hypotheses in LAN-style theorems — normalisation and
integrability, each for every parameter `θ`.

We deliberately do **not** bundle ae-strict-positivity of `p_θ` here: vdV's
Theorem 7.10 (and the LAN expansion it rests on) only needs the weaker condition
that the perturbation densities `p_{θ₀ + t·u}` are strictly positive on the support
of `p_{θ₀}` (i.e. ν-a.e. where ν = μ.withDensity p_{θ₀}). Consumers requiring that
condition should take it as a separate hypothesis in ν-form, not bake it in here. -/
structure IsPDFOf
    {𝓧 : Type*} [MeasurableSpace 𝓧] {Θ : Type*}
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) : Prop where
  /-- Density integrates to 1 (normalisation). -/
  density_integral_eq_one : ∀ θ, ∫ x, M.density θ x ∂μ = 1
  /-- Density is μ-integrable. -/
  density_integrable : ∀ θ, Integrable (M.density θ) μ

namespace ParametricFamily

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*}

/-! ## Square-root density -/

/-- The square root density `√p_θ`. -/
noncomputable def sqrtDensity (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) : ℝ :=
  Real.sqrt (M.density θ x)

lemma sqrtDensity_meas (M : ParametricFamily 𝓧 Θ) (θ : Θ) :
    Measurable (M.sqrtDensity θ) :=
  (M.density_meas θ).sqrt

lemma sqrtDensity_nonneg (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) :
    0 ≤ M.sqrtDensity θ x :=
  Real.sqrt_nonneg _

lemma sqrtDensity_sq (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) :
    M.sqrtDensity θ x ^ 2 = M.density θ x := by
  unfold sqrtDensity
  exact Real.sq_sqrt (M.density_nonneg θ x)

/-- If a density `p_θ` is integrable, then its square root belongs to `L²(μ)`. -/
lemma sqrtDensity_memLp_two
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ)
    (hint : Integrable (M.density θ) μ) :
    MemLp (M.sqrtDensity θ) 2 μ := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq
      ((M.sqrtDensity_meas θ).aestronglyMeasurable)).2 ?_
  simpa [M.sqrtDensity_sq] using hint

end ParametricFamily
end AsymptoticStatistics
