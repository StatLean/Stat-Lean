import StatLean.AsymptoticStatistics.Asymptotics.ZEstimator
import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansion
import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift
import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec
import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec

/-!
# Convex-linear models: automatic no-bias and Z-estimator efficiency

This file specializes the Z-estimator efficiency theorem (vdV
thm:25.54, `zEstimator_semiparametricallyEfficient`) to the class of
**convex-linear** models (vdV Example 25.61, book p.396).

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

Reference: vdV *Asymptotic Statistics* §25.8, Example 25.61, book p.396.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Efficiency.ConvexLinearEfficiency

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec
open AsymptoticStatistics.Asymptotics.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansion
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorBiasExpansionVec
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimatorModelShift

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

/-- *Convex-linear model* (vdV Example 25.61, book p.396).

A model `{P_{θ,η} : η ∈ H}` is convex-linear when `H` is convex and
`η ↦ P_{θ,η}` is linear. In this abstract Hilbert framework we record
the single consequence that drives the no-bias computation: an index
type `Alt` of alternative nuisance parameters `η₁ ∈ H`, together with,
for each `η₁`, the submodel score direction
`nuisanceDir η₁ = dP_{θ,η₁}/dP_{θ,η} − 1` and the fact that this
direction is a legitimate nuisance score (`nuisanceDir_mem`, i.e. lies
in the nuisance tangent space `T_nuis`).

`nuisanceDir_mem` is `Constitutive (vdV §25.8 Ex 25.61 p.396)`: it is the
formal content of convex-linearity used in the book's display
(`Bg,η(dη/dη − 1)` is a nuisance score); removing it would make the
object not vdV's convex-linear model. -/
structure ConvexLinearModel (P : Measure Ω) [IsProbabilityMeasure P]
    (T_nuis : NuisanceTangentSpace P) where
  /-- Index type of alternative nuisance parameters `η₁ ∈ H`. -/
  Alt : Type*
  /-- The submodel score direction `dP_{θ,η₁}/dP_{θ,η} − 1` (vdV 25.61
  display, p.396) attached to each alternative `η₁`. -/
  nuisanceDir : Alt → ↥(L2ZeroMean P)
  /-- *Constitutive (vdV §25.8 Ex 25.61 p.396):* each density-ratio-minus-one
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

Reference: vdV Example 25.61, book p.396. -/
noncomputable def convexLinearBias
    {T_nuis : NuisanceTangentSpace P} [proj : T_nuis.HasOrthogonalProjection]
    (M : ConvexLinearModel P T_nuis) (S_θ : OrdinaryScore P Θ) (v : Θ)
    (a : M.Alt) : ℝ :=
  ⟪(oneL2 P : Lp ℝ 2 P)
      + ((M.nuisanceDir a : ↥(L2ZeroMean P)) : Lp ℝ 2 P),
    ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v :
      ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ

/-- *vdV Example 25.61 (L1) — the no-bias condition holds with bias `= 0`
for convex-linear models.*

For a convex-linear model the alternative expectation of the efficient
score vanishes: `P_{θ,η₁} ℓ̃_{θ,η} = 0` for every alternative nuisance
parameter `η₁`. This is the display in vdV 25.61 (p.396):

    P_{θ,η₁} ℓ̃_{θ,η} = P_{θ,η} ℓ̃ + P_{θ,η} ℓ̃ (dP_{θ,η₁}/dP_{θ,η} − 1)
                     = 0 + ⟪ℓ̃, nuisanceDir a⟫ = 0,

using that `ℓ̃` is mean-zero (`ℓ̃ ∈ L²₀(P)`, so `⟪oneL2 P, ℓ̃⟫ = 0`) and
orthogonal to every nuisance score (`efficientScore_inner_nuisance_eq_zero`,
so `⟪nuisanceDir a, ℓ̃⟫ = 0`). Hence the unbiasedness condition (25.52) is
trivially satisfied, with bias identically `0`.

Reference: vdV Example 25.61, book p.396. -/
theorem convexLinear_noBias_zero
    {T_nuis : NuisanceTangentSpace P} [proj : T_nuis.HasOrthogonalProjection]
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
        ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v :
          ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ = 0 :=
    LinearMap.mem_ker.mp
      (@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v).property
  -- `⟪nuisanceDir a, ℓ̃⟫ = 0`: orthogonality of the efficient score to
  -- the nuisance tangent space (`efficientScore_inner_nuisance_eq_zero`).
  have h2 :
      ⟪((M.nuisanceDir a : ↥(L2ZeroMean P)) : Lp ℝ 2 P),
        ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v :
          ↥(L2ZeroMean P)) : Lp ℝ 2 P)⟫_ℝ = 0 := by
    change ⟪M.nuisanceDir a,
      @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v⟫_ℝ = 0
    rw [real_inner_comm]
    exact @efficientScore_inner_nuisance_eq_zero Ω _ P _ Θ _ _ _
      S_θ T_nuis proj v (M.nuisanceDir a) (M.nuisanceDir_mem a)
  -- Combine: `P_{θ,η₁} ℓ̃ = ⟪oneL2 P, ℓ̃⟫ + ⟪nuisanceDir a, ℓ̃⟫ = 0`.
  unfold convexLinearBias
  rw [inner_add_left, h1, h2, add_zero]

/-- *vdV Example 25.61 (L2) — Z-estimators are efficient in convex-linear
models.*

Corollary of thm:25.54 (`zEstimator_semiparametricallyEfficient`).
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

Reference: vdV Example 25.61 + thm:25.54, book p.392, p.396. -/
theorem convexLinear_zEstimator_efficient
    {T_nuis : NuisanceTangentSpace P} [proj : T_nuis.HasOrthogonalProjection]
    {S_θ : OrdinaryScore P Θ} {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (M : ConvexLinearModel P T_nuis)
    {alt : ∀ n, (Fin n → Ω) → M.Alt}
    {bias : ∀ n, (Fin n → Ω) → ℝ}
    (h : @EfficientScoreEqBiasResidualAssumptions Ω _ P _ Θ _ _ _
            S_θ T_nuis proj v T dψ estimator bias θ₀)
    (h_bias : ∀ n X, bias n X = Real.sqrt n * convexLinearBias M S_θ v (alt n X))
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  -- L1 forces the bias-residual sequence to vanish identically.
  have hz : bias = fun _ _ => (0 : ℝ) := by
    funext n X
    simp only [h_bias n X, convexLinear_noBias_zero M S_θ v (alt n X), mul_zero]
  subst hz
  -- bias `= 0` collapses the 25.59 bundle to the 25.54 bundle, then apply
  -- the thm:25.54 efficiency theorem.
  have h0 :=
    @EfficientScoreEqBiasResidualAssumptions.toEfficientScoreEqAssumptions
      Ω _ P _ Θ _ _ _ S_θ T_nuis proj v T dψ estimator θ₀ h
  exact @zEstimator_semiparametricallyEfficient Ω _ P _ Θ _ _ _ S_θ T_nuis
    proj v T dψ estimator θ₀ h0 ψ h_ψ

/-! ## Measure-backed direct discharge of Example 25.61 -/

/-- A measure-backed alternative in a convex-linear nuisance model.

The alternative law `Q` is represented relative to the base law `P`; its
Radon--Nikodym derivative minus one is exactly the nuisance direction attached
to `alt`.  No integrability or centering conclusion is stored in the object.

Reference: vdV Example 25.61, book p.396. -/
structure ConvexLinearAlternative
    {T_nuis : NuisanceTangentSpace P}
    (M : ConvexLinearModel P T_nuis) (Q : Measure Ω) where
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the alternative nuisance
  parameter whose convex-mixture path is used in the argument. -/
  alt : M.Alt
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the alternative law has a
  density relative to the fitted base law. -/
  absContinuous : Q ≪ P
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the density-ratio-minus-one
  score of the convex-mixture path is the model's nuisance direction. -/
  rnDeriv_sub_one_ae :
    (fun ω => (Q.rnDeriv P ω).toReal - 1) =ᵐ[P]
      fun ω => ((M.nuisanceDir alt : L2ZeroMean P) : Lp ℝ 2 P) ω

/-- A scalar fitted score represented by an efficient score under a shared
measure-backed convex-linear alternative.

This is a witness interface only: the zero-integral consequence is deliberately
proved by `ConvexLinearEfficientScoreWitness.integral_eq_zero`, not stored as a
field.  Reference: vdV Example 25.61, book p.396. -/
structure ConvexLinearEfficientScoreWitness
    {T_nuis : NuisanceTangentSpace P} [proj : T_nuis.HasOrthogonalProjection]
    (M : ConvexLinearModel P T_nuis) (Q : Measure Ω)
    (S_θ : OrdinaryScore P Θ) (v : Θ) (f : Ω → ℝ) where
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the shared alternative
  measure is generated by a convex-linear nuisance displacement. -/
  alternative : ConvexLinearAlternative M Q
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the fitted score agrees
  `Q`-a.e. with the efficient score at the fitted base law. -/
  score_eq_ae : f =ᵐ[Q]
    fun ω => ((@efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v :
      L2ZeroMean P) : Lp ℝ 2 P) ω

/-- A native vector fitted score represented coordinatewise by efficient scores
under one shared measure-backed convex-linear alternative.

The Bochner zero-integral consequence is a theorem, not a structure field.
Reference: vdV Example 25.61, book p.396. -/
structure ConvexLinearEfficientScoresWitness
    {d : ℕ} {T_nuis : NuisanceTangentSpace P}
    [proj : T_nuis.HasOrthogonalProjection]
    (M : ConvexLinearModel P T_nuis) (Q : Measure Ω)
    (S_θ : OrdinaryScore P Θ) (e : Fin d → Θ)
    (f : Ω → EuclideanSpace ℝ (Fin d)) where
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): every coordinate uses the
  same convex-linear alternative law. -/
  alternative : ConvexLinearAlternative M Q
  /-- Constitutive (vdV §25.8, Example 25.61 p.396): the fitted vector score
  agrees `Q`-a.e. with the native tuple of efficient-score representatives. -/
  scores_eq_ae : f =ᵐ[Q]
    tupleEval P (fun j =>
      @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j))

namespace ConvexLinearEfficientScoreWitness

/-- The alternative-law expectation of a scalar efficient score is zero in a
measure-backed convex-linear model (vdV Example 25.61, p.396). -/
theorem integral_eq_zero
    {T_nuis : NuisanceTangentSpace P} [proj : T_nuis.HasOrthogonalProjection]
    {M : ConvexLinearModel P T_nuis} {Q : Measure Ω}
    -- `Q` is the alternative probability law in Example 25.61.
    [IsProbabilityMeasure Q]
    {S_θ : OrdinaryScore P Θ} {v : Θ} {f : Ω → ℝ}
    (h : ConvexLinearEfficientScoreWitness M Q S_θ v f) :
    ∫ ω, f ω ∂Q = 0 := by
  let ell : L2ZeroMean P :=
    @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj v
  calc
    ∫ ω, f ω ∂Q = ∫ ω, ((ell : Lp ℝ 2 P) : Ω → ℝ) ω ∂Q :=
      integral_congr_ae h.score_eq_ae
    _ = ∫ ω, (Q.rnDeriv P ω).toReal •
        ((ell : Lp ℝ 2 P) : Ω → ℝ) ω ∂P :=
      (MeasureTheory.integral_rnDeriv_smul h.alternative.absContinuous).symm
    _ = convexLinearBias M S_θ v h.alternative.alt := by
      unfold convexLinearBias
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      have hone : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => 1 :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have hadd := Lp.coeFn_add (oneL2 P)
        ((M.nuisanceDir h.alternative.alt : L2ZeroMean P) : Lp ℝ 2 P)
      filter_upwards [h.alternative.rnDeriv_sub_one_ae, hone, hadd]
        with ω hrn honeω haddω
      change (Q.rnDeriv P ω).toReal * (ell : Lp ℝ 2 P) ω =
        (ell : Lp ℝ 2 P) ω *
          ((oneL2 P : Lp ℝ 2 P) +
            ((M.nuisanceDir h.alternative.alt : L2ZeroMean P) : Lp ℝ 2 P)) ω
      rw [haddω]
      simp only [Pi.add_apply]
      rw [honeω]
      change (Q.rnDeriv P ω).toReal * (ell : Lp ℝ 2 P) ω =
        (ell : Lp ℝ 2 P) ω *
          (1 + (M.nuisanceDir h.alternative.alt : Lp ℝ 2 P) ω)
      rw [← hrn]
      ring
    _ = 0 := convexLinear_noBias_zero M S_θ v h.alternative.alt

end ConvexLinearEfficientScoreWitness

namespace ConvexLinearEfficientScoresWitness

/-- The alternative-law Bochner expectation of the native efficient-score tuple
is zero in a measure-backed convex-linear model (vdV Example 25.61, p.396). -/
theorem integral_eq_zero
    {d : ℕ} {T_nuis : NuisanceTangentSpace P}
    [proj : T_nuis.HasOrthogonalProjection]
    {M : ConvexLinearModel P T_nuis} {Q : Measure Ω}
    -- `Q` is the shared alternative probability law in Example 25.61.
    [IsProbabilityMeasure Q]
    {S_θ : OrdinaryScore P Θ} {e : Fin d → Θ}
    {f : Ω → EuclideanSpace ℝ (Fin d)}
    (h : ConvexLinearEfficientScoresWitness M Q S_θ e f) :
    ∫ ω, f ω ∂Q = 0 := by
  have hcoord (j : Fin d) :
      ConvexLinearEfficientScoreWitness M Q S_θ (e j) (fun ω => f ω j) := by
    refine ⟨h.alternative, ?_⟩
    filter_upwards [h.scores_eq_ae] with ω hω
    rw [hω]
    rfl
  have hcoord_integrable (j : Fin d) : Integrable (fun ω => f ω j) Q := by
    let ell : L2ZeroMean P :=
      @efficientScore Ω _ P _ Θ _ _ _ S_θ T_nuis proj (e j)
    have hprod :=
      (Lp.memLp ((oneL2 P : Lp ℝ 2 P) +
        ((M.nuisanceDir h.alternative.alt : L2ZeroMean P) : Lp ℝ 2 P))).integrable_mul
          (Lp.memLp (ell : Lp ℝ 2 P))
    have hrnprod : Integrable (fun ω => (Q.rnDeriv P ω).toReal •
        ((ell : Lp ℝ 2 P) : Ω → ℝ) ω) P := by
      apply hprod.congr
      have hone : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => 1 :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have hadd := Lp.coeFn_add (oneL2 P)
        ((M.nuisanceDir h.alternative.alt : L2ZeroMean P) : Lp ℝ 2 P)
      filter_upwards [h.alternative.rnDeriv_sub_one_ae, hone, hadd]
        with ω hrn honeω haddω
      simp only [Pi.mul_apply, smul_eq_mul]
      rw [haddω]
      simp only [Pi.add_apply]
      rw [honeω]
      change (1 + (M.nuisanceDir h.alternative.alt : Lp ℝ 2 P) ω) *
          (ell : Lp ℝ 2 P) ω =
        (Q.rnDeriv P ω).toReal * (ell : Lp ℝ 2 P) ω
      rw [← hrn]
      ring
    have hellQ : Integrable (((ell : Lp ℝ 2 P) : Ω → ℝ)) Q :=
      (MeasureTheory.integrable_rnDeriv_smul_iff
        h.alternative.absContinuous).mp hrnprod
    exact hellQ.congr (hcoord j).score_eq_ae.symm
  ext j
  rw [MeasureTheory.eval_integral_piLp hcoord_integrable j]
  exact ConvexLinearEfficientScoreWitness.integral_eq_zero (hcoord j)

end ConvexLinearEfficientScoresWitness

/-- Pointwise vanishing of the scalar raw moving bias when every fitted base law
and moving-model law are connected by the measure-backed convex-linear witness.

Reference: vdV Example 25.61, book p.396. -/
theorem convexLinear_rawMovingBias_zero
    {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
    (γ : QMDPath P₀)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ)
    (scoreHat : ∀ n, (Fin n → Ω) → Ω → ℝ)
    -- fitted nuisance law at each sample realization.
    (P_hat : ∀ n, (Fin n → Ω) → Measure Ω)
    -- every fitted nuisance law is a probability law.
    [∀ n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each sample realization.
    (T_hat : ∀ n X, NuisanceTangentSpace (P_hat n X))
    -- Mathlib's orthogonal projection API for every fitted tangent.
    [∀ n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score at each sample realization.
    (S_hat : ∀ n X, OrdinaryScore (P_hat n X) Θ)
    -- fitted convex-linear nuisance model at each realization.
    (M_hat : ∀ n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    (v : Θ)
    -- direct Example 25.61 witness for the moving law and fitted score.
    (hConvex : ∀ n X, ConvexLinearEfficientScoreWitness
      (M_hat n X) (γ.curve (estimator n X - θ₀)) (S_hat n X) v (scoreHat n X)) :
    ∀ n X, rawMovingBias γ estimator θ₀ scoreHat n X = 0 := by
  intro n X
  letI : IsProbabilityMeasure (γ.curve (estimator n X - θ₀)) :=
    γ.curve_isProbability _
  unfold rawMovingBias
  rw [ConvexLinearEfficientScoreWitness.integral_eq_zero (hConvex n X), mul_zero]

/-- Pointwise vanishing of the native vector raw moving bias under one shared
convex-linear alternative law per sample realization (vdV Example 25.61). -/
theorem convexLinear_rawMovingBias_zero_vec
    {d : ℕ} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
    (M : QMDModel (Omega := Ω) P₀ d)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Ω) → Ω → EuclideanSpace ℝ (Fin d))
    -- fitted nuisance law at each sample realization.
    (P_hat : ∀ n, (Fin n → Ω) → Measure Ω)
    -- every fitted nuisance law is a probability law.
    [∀ n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each sample realization.
    (T_hat : ∀ n X, NuisanceTangentSpace (P_hat n X))
    -- Mathlib's orthogonal projection API for every fitted tangent.
    [∀ n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score at each sample realization.
    (S_hat : ∀ n X, OrdinaryScore (P_hat n X) Θ)
    -- fitted convex-linear nuisance model at each realization.
    (C_hat : ∀ n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    (e : Fin d → Θ)
    -- direct Example 25.61 witness for the moving law and score tuple.
    (hConvex : ∀ n X, ConvexLinearEfficientScoresWitness
      (C_hat n X) (M.curve (estimator n X - θ₀)) (S_hat n X) e (scoreHat n X)) :
    ∀ n X, rawMovingBias_vec M estimator θ₀ scoreHat n X = 0 := by
  intro n X
  letI : IsProbabilityMeasure (M.curve (estimator n X - θ₀)) :=
    M.curve_isProbability _
  unfold rawMovingBias_vec
  rw [ConvexLinearEfficientScoresWitness.integral_eq_zero (hConvex n X), smul_zero]

/-- The scalar normalized no-bias condition (25.52), discharged directly from
the measure-backed convex-linear witness of Example 25.61. -/
theorem convexLinear_noBias_2552
    {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
    (γ : QMDPath P₀)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ)
    (scoreHat : ∀ n, (Fin n → Ω) → Ω → ℝ)
    -- fitted nuisance law at each sample realization.
    (P_hat : ∀ n, (Fin n → Ω) → Measure Ω)
    -- every fitted nuisance law is a probability law.
    [∀ n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each sample realization.
    (T_hat : ∀ n X, NuisanceTangentSpace (P_hat n X))
    -- Mathlib's orthogonal projection API for every fitted tangent.
    [∀ n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score at each sample realization.
    (S_hat : ∀ n X, OrdinaryScore (P_hat n X) Θ)
    -- fitted convex-linear nuisance model at each realization.
    (M_hat : ∀ n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    (v : Θ)
    -- direct Example 25.61 witness for the moving law and fitted score.
    (hConvex : ∀ n X, ConvexLinearEfficientScoreWitness
      (M_hat n X) (γ.curve (estimator n X - θ₀)) (S_hat n X) v (scoreHat n X)) :
    TendstoInProbZero
      (fun n : ℕ => Measure.pi (fun _ : Fin n => P₀))
      (fun n X =>
        (1 + |Real.sqrt n * (estimator n X - θ₀)|)⁻¹ *
          rawMovingBias γ estimator θ₀ scoreHat n X) := by
  have hz := convexLinear_rawMovingBias_zero γ estimator θ₀ scoreHat
    P_hat T_hat S_hat M_hat v hConvex
  rw [show (fun (n : ℕ) (X : Fin n → Ω) =>
      (1 + |Real.sqrt n * (estimator n X - θ₀)|)⁻¹ *
        rawMovingBias γ estimator θ₀ scoreHat n X) =
      (fun _ _ => (0 : ℝ)) by
    funext n X
    rw [hz n X, mul_zero]]
  intro ε hε
  simp [not_le.mpr hε]

/-- The native vector normalized no-bias condition (25.52), discharged directly
from the shared measure-backed convex-linear witness of Example 25.61. -/
theorem convexLinear_noBias_2552_vec
    {d : ℕ} {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
    (M : QMDModel (Omega := Ω) P₀ d)
    (estimator : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (scoreHat : ∀ n, (Fin n → Ω) → Ω → EuclideanSpace ℝ (Fin d))
    -- fitted nuisance law at each sample realization.
    (P_hat : ∀ n, (Fin n → Ω) → Measure Ω)
    -- every fitted nuisance law is a probability law.
    [∀ n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each sample realization.
    (T_hat : ∀ n X, NuisanceTangentSpace (P_hat n X))
    -- Mathlib's orthogonal projection API for every fitted tangent.
    [∀ n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score at each sample realization.
    (S_hat : ∀ n X, OrdinaryScore (P_hat n X) Θ)
    -- fitted convex-linear nuisance model at each realization.
    (C_hat : ∀ n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    (e : Fin d → Θ)
    -- direct Example 25.61 witness for the moving law and score tuple.
    (hConvex : ∀ n X, ConvexLinearEfficientScoresWitness
      (C_hat n X) (M.curve (estimator n X - θ₀)) (S_hat n X) e (scoreHat n X)) :
    TendstoInProbZero
      (fun n : ℕ => Measure.pi (fun _ : Fin n => P₀))
      (fun n X =>
        (1 + ‖Real.sqrt n • (estimator n X - θ₀)‖)⁻¹ •
          rawMovingBias_vec M estimator θ₀ scoreHat n X) := by
  have hz := convexLinear_rawMovingBias_zero_vec M estimator θ₀ scoreHat
    P_hat T_hat S_hat C_hat e hConvex
  rw [show (fun (n : ℕ) (X : Fin n → Ω) =>
      (1 + ‖Real.sqrt n • (estimator n X - θ₀)‖)⁻¹ •
        rawMovingBias_vec M estimator θ₀ scoreHat n X) =
      (fun _ _ => (0 : EuclideanSpace ℝ (Fin d))) by
    funext n X
    rw [hz n X, smul_zero]]
  intro ε hε
  simp [not_le.mpr hε]

/-! ## Direct efficiency theorems -/

/-- *vdV Example 25.61 — direct scalar Z-estimator efficiency headline.*

The interface exposes the primitive estimating-equation, empirical-replacement,
QMD-transport, efficient-score, and measure-backed convex-linearity inputs.  It
does not assume a cross-moment identity, equation (25.52), raw-bias vanishing,
asymptotic linearity, a Taylor conclusion, or a Bartlett identity.

Proof idea: build `RawMovingBiasExpansionHyp.ofEfficientScore`; derive (25.52)
with `convexLinear_noBias_2552`; obtain asymptotic linearity from
`rawMovingBias_asympLinear_2554`; construct the EIF using
`eif_from_efficientScore`; finish with
`estimator_semiparametricallyEfficient_of_asympLinear_eif`.

Reference: vdV Example 25.61 and Theorem 25.54, book pp.396 and 392. -/
theorem convexLinear_zEstimator_efficient_2561
    -- measurable observation space of the statistical experiment.
    {Omega : Type} [MeasurableSpace Omega]
    -- truth law of the statistical experiment.
    (P : Measure Omega)
    -- the truth law in vdV Theorem 25.54 and Example 25.61.
    [IsProbabilityMeasure P]
    -- Hilbert encoding of the parameter space used by score operators.
    {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta]
    -- ordinary score operator at the truth.
    (S_theta : OrdinaryScore P Theta)
    -- nuisance tangent space at the truth.
    (T_nuis : NuisanceTangentSpace P)
    -- Mathlib's orthogonal projection API for the nuisance tangent.
    [proj : T_nuis.HasOrthogonalProjection]
    -- scalar parameter direction.
    (v : Theta)
    -- QMD path realizing the ordinary-score direction.
    (gamma : QMDPath P)
    -- Z-estimator sequence and truth value.
    (estimator : forall n, (Fin n -> Omega) -> Real) (theta0 : Real)
    -- fitted estimating score and empirical-process class.
    (scoreHat : forall n, (Fin n -> Omega) -> Omega -> Real)
    (F : Set (Omega -> Real))
    -- vdV §25.8 estimating equation at the fitted score.
    (score_eq : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => (Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreHat n X (X i)))
    -- vdV Lemma 19.24 random-index replacement primitives.
    (B0 : RandomIndexScoreReplacementHyp P scoreHat
      (fun omega => ((@efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v : Lp Real 2 P) : Omega -> Real) omega) F)
    -- vdV §25.8 DQM plus condition (25.53) moving-law transport primitives.
    (hTransport : HellingerScoreTransportHyp P gamma estimator theta0 scoreHat
      (fun omega => ((@efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v : Lp Real 2 P) : Omega -> Real) omega))
    -- the supplied QMD path has ordinary score `S_theta v`.
    (hScore : gamma.score = S_theta v)
    -- vdV Theorem 25.54 nonsingularity of efficient information.
    (hI : 0 < @efficientInformation Omega _ P _ Theta _ _ _
      S_theta T_nuis proj v)
    -- finite-prefix measurability for the all-`n` tightness predicate.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- fitted nuisance law at each sample realization.
    (P_hat : forall n, (Fin n -> Omega) -> Measure Omega)
    -- every fitted nuisance law is a probability law.
    [forall n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each realization.
    (T_hat : forall n X, NuisanceTangentSpace (P_hat n X))
    -- fitted tangent projections required by Mathlib's Hilbert API.
    [forall n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score and convex-linear nuisance model.
    (S_hat : forall n X, OrdinaryScore (P_hat n X) Theta)
    (M_hat : forall n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    -- direct Example 25.61 witness under the actual moving law.
    (hConvex : forall n X, ConvexLinearEfficientScoreWitness
      (M_hat n X) (gamma.curve (estimator n X - theta0))
      (S_hat n X) v (scoreHat n X))
    -- total tangent space and scalar pathwise derivative.
    (T : Submodule Real ↥(L2ZeroMean P)) (dpsi : T →L[Real] Real)
    -- the efficient-score representer belongs to the total tangent.
    (h_mem : (1 / @efficientInformation Omega _ P _ Theta _ _ _
      S_theta T_nuis proj v) •
        @efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v ∈ T)
    -- derivative representation matching the efficient-score EIF.
    (h_dpsi : forall g : T, dpsi g =
      (1 / @efficientInformation Omega _ P _ Theta _ _ _
        S_theta T_nuis proj v) *
        ⟪@efficientScore Omega _ P _ Theta _ _ _ S_theta T_nuis proj v,
          (g : ↥(L2ZeroMean P))⟫_ℝ)
    -- target functional and its value at the truth.
    (psi : Measure Omega -> Real) (hpsi : psi P = theta0) :
    SemiparametricallyEfficientAt estimator psi P T := by
  have hRaw := RawMovingBiasExpansionHyp.ofEfficientScore (proj := proj)
    S_theta T_nuis v score_eq B0 hTransport hScore hI
  have h52 := convexLinear_noBias_2552 gamma estimator theta0 scoreHat
    P_hat T_hat S_hat M_hat v hConvex
  have hAL := rawMovingBias_asympLinear_2554 hRaw hEstimator_meas h52
  have hEIF := @eif_from_efficientScore Omega _ P _ Theta _ _ _
    S_theta T_nuis proj v T h_mem dpsi h_dpsi
  refine estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF ?_
  rw [hpsi]
  simpa only [one_div] using hAL

/-- *vdV Example 25.61 — direct native vector Z-estimator efficiency headline.*

This is the native finite-dimensional mirror of
`convexLinear_zEstimator_efficient_2561`.  It assumes no cross-moment matrix,
equation (25.52), raw-bias vanishing, asymptotic linearity, Bartlett identity,
or Taylor conclusion.

Proof idea: build `RawMovingBiasExpansionHyp_vec.ofEfficientScores`; derive
(25.52) with `convexLinear_noBias_2552_vec`; obtain native asymptotic linearity
from `rawMovingBias_asympLinear_2554_vec`; construct the vector EIF using
`eif_from_efficientScore_vec`; finish with
`estimator_semiparametricallyEfficient_of_asympLinear_eif_vec`.

Reference: vdV Example 25.61 and Theorem 25.54, book pp.396 and 392. -/
theorem convexLinear_zEstimator_efficient_2561_vec
    -- native dimension and measurable observation space.
    {d : Nat} {Omega : Type} [MeasurableSpace Omega]
    -- truth law of the statistical experiment.
    (P : Measure Omega)
    -- the truth law in vdV Theorem 25.54 and Example 25.61.
    [IsProbabilityMeasure P]
    -- Hilbert encoding of the parameter space used by score operators.
    {Theta : Type*} [NormedAddCommGroup Theta] [InnerProductSpace Real Theta]
    [CompleteSpace Theta]
    -- ordinary score operator and nuisance tangent at the truth.
    (S_theta : OrdinaryScore P Theta) (T_nuis : NuisanceTangentSpace P)
    -- Mathlib's orthogonal projection API for the nuisance tangent.
    [proj : T_nuis.HasOrthogonalProjection]
    -- native parameter directions.
    (e : Fin d -> Theta)
    -- native QMD model realizing those score coordinates.
    (M : QMDModel (Omega := Omega) P d)
    -- native Z-estimator sequence and truth value.
    (estimator : forall n, (Fin n -> Omega) -> EuclideanSpace Real (Fin d))
    (theta0 : EuclideanSpace Real (Fin d))
    -- fitted native estimating score and coordinatewise classes.
    (scoreHat : forall n,
      (Fin n -> Omega) -> Omega -> EuclideanSpace Real (Fin d))
    (F : Fin d -> Set (Omega -> Real))
    -- vdV §25.8 native estimating equation at the fitted score.
    (score_eq : TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X => (Real.sqrt n)⁻¹ • ∑ i : Fin n, scoreHat n X (X i)))
    -- vdV Lemma 19.24 coordinatewise replacement primitives.
    (B0 : RandomIndexScoreReplacementHyp_vec P d scoreHat
      (tupleEval P (fun k => @efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e k))) F)
    -- vdV §25.8 DQM plus condition (25.53) moving-law transport primitives.
    (hTransport : HellingerScoreTransportHypVec P M estimator theta0 scoreHat
      (tupleEval P (fun k => @efficientScore Omega _ P _ Theta _ _ _
        S_theta T_nuis proj (e k))))
    -- native QMD score coordinates realize the ordinary scores.
    (hScore : forall k, (fun omega => M.score omega k) =ᵐ[P]
      fun omega => ((S_theta (e k) : Lp Real 2 P) : Omega -> Real) omega)
    -- vdV Theorem 25.54 positive-definite efficient information.
    (hPD : (@efficientInformationMatrix Omega _ P _ Theta _ _ _ d
      S_theta T_nuis proj e).PosDef)
    -- finite-prefix measurability for the all-`n` tightness predicate.
    (hEstimator_meas : forall n, Measurable (estimator n))
    -- fitted nuisance law at each sample realization.
    (P_hat : forall n, (Fin n -> Omega) -> Measure Omega)
    -- every fitted nuisance law is a probability law.
    [forall n X, IsProbabilityMeasure (P_hat n X)]
    -- fitted nuisance tangent space at each realization.
    (T_hat : forall n X, NuisanceTangentSpace (P_hat n X))
    -- fitted tangent projections required by Mathlib's Hilbert API.
    [forall n X, (T_hat n X).HasOrthogonalProjection]
    -- fitted ordinary score and convex-linear nuisance model.
    (S_hat : forall n X, OrdinaryScore (P_hat n X) Theta)
    (C_hat : forall n X, ConvexLinearModel (P_hat n X) (T_hat n X))
    -- shared vector witness under the actual native moving law.
    (hConvex : forall n X, ConvexLinearEfficientScoresWitness
      (C_hat n X) (M.curve (estimator n X - theta0))
      (S_hat n X) e (scoreHat n X))
    -- total tangent space and native pathwise derivative.
    (T : Submodule Real ↥(L2ZeroMean P))
    (Dpsi : T →L[Real] EuclideanSpace Real (Fin d))
    -- every coordinate of the vector EIF belongs to the tangent.
    (h_mem : forall j, @candidateVecEIF Omega _ P _ Theta _ _ _ d
      S_theta T_nuis proj e j ∈ T)
    -- coordinate derivative representation matching the vector EIF.
    (h_Dpsi : forall (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dpsi) g =
        ⟪@candidateVecEIF Omega _ P _ Theta _ _ _ d
          S_theta T_nuis proj e j, (g : ↥(L2ZeroMean P))⟫_ℝ)
    -- native target functional and its value at the truth.
    (psi : Measure Omega -> EuclideanSpace Real (Fin d))
    (hpsi : psi P = theta0) :
    SemiparametricallyEfficientAt_vec estimator psi P T := by
  have hRaw := RawMovingBiasExpansionHyp_vec.ofEfficientScores (proj := proj)
    S_theta T_nuis e score_eq B0 hTransport hScore hPD
  have h52 := convexLinear_noBias_2552_vec M estimator theta0 scoreHat
    P_hat T_hat S_hat C_hat e hConvex
  have hAL := rawMovingBias_asympLinear_2554_vec hRaw hEstimator_meas h52
  have hEIF := @eif_from_efficientScore_vec Omega _ P _ Theta _ _ _ d
    S_theta T_nuis proj e T Dpsi hPD h_mem h_Dpsi
  refine estimator_semiparametricallyEfficient_of_asympLinear_eif_vec hEIF ?_
  rw [hpsi]
  simpa only [candidateVecEIF] using hAL

end AsymptoticStatistics.Efficiency.ConvexLinearEfficiency
