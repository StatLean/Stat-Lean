import StatLean.AsymptoticStatistics.Asymptotics.ZEstimator

/-!
# Convex-linear models: automatic no-bias and Z-estimator efficiency

This file specializes the closed Z-estimator efficiency theorem (vdV
thm:25.54, `zEstimator_semiparametricallyEfficient`) to the class of
**convex-linear** models (vdV Example 25.61, book p.395).

vdV Example 25.61: a model `{P_{θ,η} : η ∈ H}` is *convex-linear* when
`H` is a convex subset of a linear space and `η ↦ P_{θ,η}` is linear.
Then for every pair `(η₁, η)` the convex combination
`η_t = t η₁ + (1-t) η` is again a parameter, and the score of the
submodel `t ↦ P_{θ,η_t}` at `t = 0` is

    ∂/∂t|_{t=0} log dP_{θ, tη₁+(1-t)η} = dP_{θ,η₁}/dP_{θ,η} − 1.

Because the efficient score `ℓ̃_{θ,η}` is orthogonal to the nuisance
tangent set, that density-ratio-minus-one direction is annihilated:

    0 = P_{θ,η} ℓ̃_{θ,η} (dP_{θ,η₁}/dP_{θ,η} − 1) = P_{θ,η₁} ℓ̃_{θ,η}.

So the no-bias condition (25.52) holds *identically* (bias `= 0`), and
the efficiency conclusion of thm:25.54 follows with no further work.

Formalization note: the abstract `(θ, η)` framework of this library
carries the model only through its Hilbert data (`OrdinaryScore`,
`NuisanceTangentSpace ⊆ L²₀(P)`), not through an explicit measure family
`P_{θ,η}`. The convex-linear hypothesis is therefore encoded through its
**tangent-space consequence**: each density-ratio-minus-one direction
`dP_{θ,η₁}/dP_{θ,η} − 1` is a legitimate nuisance score, i.e. lies in
`T_nuis`. The alternative expectation `P_{θ,η₁} ℓ̃_{θ,η}` is realized as
the `L²(P)` pairing of `ℓ̃` against the density element
`1 + (dP_{θ,η₁}/dP_{θ,η} − 1) = dP_{θ,η₁}/dP_{θ,η}` (`oneL2 P +
nuisanceDir a`), exactly `∫ ℓ̃ · (dP_{θ,η₁}/dP_{θ,η}) dP = ∫ ℓ̃ dP_{θ,η₁}`.

Headline declarations: `convexLinear_noBias_zero` (L1),
`convexLinear_zEstimator_efficient` (L2).

Reference: vdV *Asymptotic Statistics* §25.8, Example 25.61, book p.395.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Efficiency.ConvexLinearEfficiency

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.ZEstimator

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

/-- *Convex-linear model* (vdV Example 25.61, book p.395).

A model `{P_{θ,η} : η ∈ H}` is convex-linear when `H` is convex and
`η ↦ P_{θ,η}` is linear. In this abstract Hilbert framework we record
the single consequence that drives the no-bias computation: an index
type `Alt` of alternative nuisance parameters `η₁ ∈ H`, together with,
for each `η₁`, the submodel score direction
`nuisanceDir η₁ = dP_{θ,η₁}/dP_{θ,η} − 1` and the fact that this
direction is a legitimate nuisance score (`nuisanceDir_mem`, i.e. lies
in the nuisance tangent space `T_nuis`).

`nuisanceDir_mem` is `Constitutive (vdV §25.8 Ex 25.61 p.395)`: it is the
formal content of convex-linearity used in the book's display
(`Bg,η(dη/dη − 1)` is a nuisance score); removing it would make the
object not vdV's convex-linear model. -/
structure ConvexLinearModel (P : Measure Ω) [IsProbabilityMeasure P]
    (T_nuis : NuisanceTangentSpace P) where
  /-- Index type of alternative nuisance parameters `η₁ ∈ H`. -/
  Alt : Type*
  /-- The submodel score direction `dP_{θ,η₁}/dP_{θ,η} − 1` (vdV 25.61
  display, p.395) attached to each alternative `η₁`. -/
  nuisanceDir : Alt → ↥(L2ZeroMean P)
  /-- *Constitutive (vdV §25.8 Ex 25.61 p.395):* each density-ratio-minus-one
  direction is a legitimate nuisance score. This is the tangent-space
  content of convex-linearity (`η ↦ P_{θ,η}` linear ⇒ the convex-mixture
  path has score `dP_{θ,η₁}/dP_{θ,η} − 1 ∈ T_nuis`). -/
  nuisanceDir_mem : ∀ a, nuisanceDir a ∈ T_nuis

/-- The no-bias functional (25.52) for a convex-linear model: the
alternative expectation `P_{θ,η₁} ℓ̃_{θ,η}` of the efficient score.

Realized abstractly as the `L²(P)` pairing of the efficient score
`ℓ̃ = efficientScore S_θ T_nuis v` against the alternative density
element `dP_{θ,η₁}/dP_{θ,η} = 1 + nuisanceDir a` (`oneL2 P +
nuisanceDir a`):

    ⟪1 + (dP_{θ,η₁}/dP_{θ,η} − 1), ℓ̃⟫_{L²(P)}
      = ∫ ℓ̃ · (dP_{θ,η₁}/dP_{θ,η}) dP = ∫ ℓ̃ dP_{θ,η₁} = P_{θ,η₁} ℓ̃.

Reference: vdV Example 25.61, book p.395. -/
noncomputable def convexLinearBias
    {T_nuis : NuisanceTangentSpace P} [T_nuis.HasOrthogonalProjection]
    (M : ConvexLinearModel P T_nuis) (S_θ : OrdinaryScore P Θ) (v : Θ)
    (a : M.Alt) : ℝ :=
  ⟪(oneL2 P : Lp ℝ 2 P)
      + ((M.nuisanceDir a : ↥(L2ZeroMean P)) : Lp ℝ 2 P),
    ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ

/-- *vdV Example 25.61 (L1) — the no-bias condition holds with bias `= 0`
for convex-linear models.*

For a convex-linear model the alternative expectation of the efficient
score vanishes: `P_{θ,η₁} ℓ̃_{θ,η} = 0` for every alternative nuisance
parameter `η₁`. This is the display in vdV 25.61 (p.395):

    P_{θ,η₁} ℓ̃_{θ,η} = P_{θ,η} ℓ̃ + P_{θ,η} ℓ̃ (dP_{θ,η₁}/dP_{θ,η} − 1)
                     = 0 + ⟪ℓ̃, nuisanceDir a⟫ = 0,

using that `ℓ̃` is mean-zero (`ℓ̃ ∈ L²₀(P)`, so `⟪oneL2 P, ℓ̃⟫ = 0`) and
orthogonal to every nuisance score (`efficientScore_inner_nuisance_eq_zero`,
so `⟪nuisanceDir a, ℓ̃⟫ = 0`). Hence the unbiasedness condition (25.52) is
trivially satisfied, with bias identically `0`.

Reference: vdV Example 25.61, book p.395. -/
theorem convexLinear_noBias_zero
    {T_nuis : NuisanceTangentSpace P} [T_nuis.HasOrthogonalProjection]
    (M : ConvexLinearModel P T_nuis) (S_θ : OrdinaryScore P Θ) (v : Θ)
    (a : M.Alt) :
    convexLinearBias M S_θ v a = 0 := by
  -- `⟪oneL2 P, ℓ̃⟫ = 0`: `ℓ̃` is mean-zero, i.e. lies in
  -- `L2ZeroMean P = ker (integralL2 P) = ker ⟪oneL2 P, ·⟫`.
  -- `integralL2 P = innerSL ℝ (oneL2 P)`, so `⟪oneL2 P, x⟫_ℝ` and
  -- `(integralL2 P).toLinearMap x` are definitionally equal; the kernel
  -- membership `x ∈ L2ZeroMean P = ker (integralL2 P)` closes the goal.
  have h1 :
      ⟪(oneL2 P : Lp ℝ 2 P),
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ = 0 :=
    LinearMap.mem_ker.mp (efficientScore S_θ T_nuis v).property
  -- `⟪nuisanceDir a, ℓ̃⟫ = 0`: orthogonality of the efficient score to
  -- the nuisance tangent space (`efficientScore_inner_nuisance_eq_zero`).
  have h2 :
      ⟪((M.nuisanceDir a : ↥(L2ZeroMean P)) : Lp ℝ 2 P),
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ = 0 := by
    rw [← Submodule.coe_inner, real_inner_comm]
    exact efficientScore_inner_nuisance_eq_zero S_θ T_nuis v (M.nuisanceDir_mem a)
  -- Combine: `P_{θ,η₁} ℓ̃ = ⟪oneL2 P, ℓ̃⟫ + ⟪nuisanceDir a, ℓ̃⟫ = 0`.
  unfold convexLinearBias
  rw [inner_add_left, h1, h2, add_zero]

/-- *vdV Example 25.61 (L2) — Z-estimators are efficient in convex-linear
models.*

Corollary of the closed thm:25.54 (`zEstimator_semiparametricallyEfficient`).
Because the no-bias condition holds with bias `= 0` for a convex-linear
model (L1, `convexLinear_noBias_zero`), the bias-residual bundle
`EfficientScoreEqBiasResidualAssumptions` collapses (via
`toEfficientScoreEqAssumptions`) to the thm:25.54 bundle, and the
Z-estimator is semiparametrically efficient.

`h_bias` records that the empirical bias-residual sequence
`bias n X = √n · P_{θ̂_n(X),η} ℓ̃` is, at every sample point, the
alternative expectation of the efficient score (`√n · convexLinearBias`)
indexed by the nuisance estimate `η̂_n` viewed as an alternative
parameter `alt n X ∈ M.Alt`. By L1 each such value is `0`, so the
bias-residual sequence is identically `0` and thm:25.54 applies.

Reference: vdV Example 25.61 + thm:25.54, book p.392, p.395. -/
theorem convexLinear_zEstimator_efficient
    {T_nuis : NuisanceTangentSpace P} [T_nuis.HasOrthogonalProjection]
    {S_θ : OrdinaryScore P Θ} {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (M : ConvexLinearModel P T_nuis)
    {alt : ∀ n, (Fin n → Ω) → M.Alt}
    {bias : ∀ n, (Fin n → Ω) → ℝ}
    (h : EfficientScoreEqBiasResidualAssumptions
            P Θ S_θ T_nuis v T dψ estimator bias θ₀)
    (h_bias : ∀ n X, bias n X = Real.sqrt n * convexLinearBias M S_θ v (alt n X))
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  -- L1 forces the bias-residual sequence to vanish identically.
  have hz : bias = fun _ _ => (0 : ℝ) := by
    funext n X
    simp only [h_bias n X, convexLinear_noBias_zero M S_θ v (alt n X), mul_zero]
  subst hz
  -- bias `= 0` collapses the 25.59 bundle to the 25.54 bundle, then apply
  -- the closed thm:25.54 headline.
  exact zEstimator_semiparametricallyEfficient h.toEfficientScoreEqAssumptions h_ψ

end AsymptoticStatistics.Efficiency.ConvexLinearEfficiency
