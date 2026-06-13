import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

/-!
Gaussian shift experiment: the parametric family `h ↦ N(h, Σ)` on `EuclideanSpace ℝ (Fin k)`.

In van der Vaart §7.10 this is the "limit experiment" to which the local LAN family
`P^n_{θ + h/√n}` becomes weakly equivalent. The relevant facts for us are:

1. It is a parametric family of probability measures on `Θ := EuclideanSpace ℝ (Fin k)`.
2. Its log-likelihood ratio has the closed form
   `log d N(h, Σ) / d N(0, Σ) (x) = ⟨h, Σ⁻¹ x⟩ - ½ ⟨h, Σ⁻¹ h⟩`.

Mathlib at this commit does not yet provide a direct `multivariateGaussian` primitive
(only `gaussianReal` and the abstract `IsGaussian` typeclass), so we package the family
as a bundled existence predicate and keep the characterizing properties as separate
`Prop`-valued predicates. When Mathlib gains a multivariate Gaussian, the existence
result (`exists_gaussianShiftFamily`) becomes constructive.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AsymptoticStatistics
namespace GaussianShift

variable {k : ℕ}

/-! ## Linear action of a matrix on `EuclideanSpace`

A utility used to pre-compose kernels with "multiply by `J`" in Theorem 7.10. It is
continuous (hence measurable) because linear maps between finite-dimensional normed
spaces are continuous, and `EuclideanSpace.equiv` is a continuous linear equivalence.

Lives here rather than in `ForMathlib/` because its only current consumer is the Gaussian
shift family; promote to `ForMathlib` if a second consumer appears. -/

noncomputable def matrixAction
    (J : Matrix (Fin k) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm
    (Matrix.mulVecLin J ((EuclideanSpace.equiv (Fin k) ℝ) x))

lemma matrixAction_continuous (J : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (matrixAction J) := by
  unfold matrixAction
  refine (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp ?_
  exact (Matrix.mulVecLin J).continuous_of_finiteDimensional.comp
    (EuclideanSpace.equiv (Fin k) ℝ).continuous

lemma matrixAction_measurable (J : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (matrixAction J) :=
  (matrixAction_continuous J).measurable

/-- Spelling of `matrixAction` via `WithLp.equiv`, for use-site compatibility
with inner-product formulas that spell out the equiv manually. -/
lemma matrixAction_eq_withLp
    (J : Matrix (Fin k) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    matrixAction J x =
      (WithLp.equiv 2 (Fin k → ℝ)).symm (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x)) :=
  rfl

/-- **Bridge**: `matrixAction J` coincides with the Mathlib `toEuclideanCLM J`
applied to the same argument. Both compute `toLp (J *ᵥ ofLp x)`; their definitions
differ only in which intermediate API (mulVecLin vs toEuclideanCLM) performs the
same matrix action. -/
lemma matrixAction_eq_toEuclideanCLM (J : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    matrixAction J x = Matrix.toEuclideanCLM (𝕜 := ℝ) J x := by
  rfl

/-- A family of probability measures `family : EuclideanSpace ℝ (Fin k) → Measure _`
**is Gaussian shift with covariance `cov`** when each `family h` is a probability
Gaussian measure, has mean `h`, and covariance `cov`. The log-likelihood ratio's
closed form is recorded as a separate proposition `HasGaussianShiftLogLikelihoodRatio`
below. -/
structure IsGaussianShift
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (cov : Matrix (Fin k) (Fin k) ℝ) : Prop where
  posDef : Matrix.PosDef cov
  isProb : ∀ h, IsProbabilityMeasure (family h)
  isGaussian : ∀ h, IsGaussian (family h)
  /-- Mean `h`: for every `u`, `∫ ⟨u, x⟩ d(family h)(x) = ⟨u, h⟩`. -/
  mean_eq (h u : EuclideanSpace ℝ (Fin k)) :
    (∫ x, ⟪u, x⟫ ∂(family h)) = ⟪u, h⟫
  /-- Covariance `cov`. Stated via the bilinear integral on centred variables. -/
  cov_eq (h u v : EuclideanSpace ℝ (Fin k)) :
    (∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫ ∂(family h)) =
      ⟪u, (WithLp.equiv 2 _).symm (cov.mulVec ((WithLp.equiv 2 _) v))⟫

/-- Closed-form log-likelihood ratio of the Gaussian shift family:
`log d N(h, cov)/d N(0, cov) (x) = ⟨h, cov⁻¹ x⟩ - ½ ⟨h, cov⁻¹ h⟩`. -/
def HasGaussianShiftLogLikelihoodRatio
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (cov : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ (h x : EuclideanSpace ℝ (Fin k)),
    Real.log (((family h).rnDeriv (family 0) x).toReal) =
      ⟪h, (WithLp.equiv 2 _).symm (cov⁻¹.mulVec ((WithLp.equiv 2 _) x))⟫
      - (1/2) * ⟪h, (WithLp.equiv 2 _).symm (cov⁻¹.mulVec ((WithLp.equiv 2 _) h))⟫

/-- **Gaussian tilted linear pushforward identity**, parametric in a base Gaussian `ν`.

For a Gaussian-shift family `family h ∼ N(h, C)` and a reference Gaussian
`ν ∼ N(0, J)`, the push-forward of `family h` by the linear action of `J` (i.e.
`matrixAction J`) equals `ν` re-weighted by the exponential tilt
`exp(⟨h, y⟩ - ½ ⟨h, J h⟩)`.

This single identity bundles (i) Gaussian push-forward by a linear map (in our setting
`J_*(N(h, J⁻¹)) = N(J h, J)`) and (ii) Radon–Nikodym change-of-base between two
Gaussians with the same covariance (`N(J h, J) = N(0, J).withDensity exp(·)`). It is
exactly the Gaussian-specific fact consumed by Theorem 7.10's `gaussianShift_bind_eq_limit`
(Step 7). Pairs with the measure-theoretic bridges `Measure.bind_map_eq_bind_comap` and
`Measure.withDensity_bind_condDistrib` to close Step 7.

Formally an assumption at this stage (Mathlib lacks multivariate Gaussian density and
linear-pushforward lemmas); once they land, this predicate becomes a theorem derivable
from `IsGaussian ν`, `ν` having mean 0 and covariance `J`, plus the tight-integrability
machinery. The design mirrors `HasGaussianShiftLogLikelihoodRatio` — a `Prop` predicate
threaded as a hypothesis and discharged at the call site. -/
def HasTiltedLinearPushforward
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (ν : Measure (EuclideanSpace ℝ (Fin k)))
    (J : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ h : EuclideanSpace ℝ (Fin k),
    (family h).map (matrixAction J) =
      ν.withDensity (fun y : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (⟪h, y⟫ -
          (1/2 : ℝ) * ⟪h, matrixAction J h⟫)))

/-- **Any Gaussian shift family equals the canonical multivariate Gaussian**
pointwise. In other words, `IsGaussianShift` uniquely determines the family
(at each parameter) as the concrete `ProbabilityTheory.multivariateGaussian h C`.

This is the Gaussian uniqueness-by-parameters fact: two Gaussian measures with the
same mean and covariance are equal (`ProbabilityTheory.IsGaussian.ext`). The proof
re-derives mean / covariance from the `IsGaussianShift` fields and compares them
against `integral_id_multivariateGaussian` / `covarianceBilin_multivariateGaussian`.

Consumed by Theorem 7.10 Step 7 (`hTilt` discharge): lets us substitute the abstract
`gauss h` supplied to `LAN_representation` with the concrete Mathlib term, so the
Gaussian linear-pushforward / Radon–Nikodym identities can be stated against a
specific measure. -/
theorem IsGaussianShift.eq_multivariateGaussian
    {family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k))}
    {C : Matrix (Fin k) (Fin k) ℝ} (hFamily : IsGaussianShift family C)
    (h : EuclideanSpace ℝ (Fin k)) :
    family h = ProbabilityTheory.multivariateGaussian h C := by
  haveI : IsProbabilityMeasure (family h) := hFamily.isProb h
  haveI : ProbabilityTheory.IsGaussian (family h) := hFamily.isGaussian h
  have hCps : C.PosSemidef := hFamily.posDef.posSemidef
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x) (family h) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have hMemLp : MeasureTheory.MemLp
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2 (family h) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · -- Means agree, both equal to `h`.
    simp only [id_eq]
    rw [ProbabilityTheory.integral_id_multivariateGaussian]
    refine ext_inner_left ℝ fun u => ?_
    rw [← integral_inner hInt]
    exact hFamily.mean_eq h u
  · -- Covariance bilinear forms agree.
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
    rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hCps,
      ProbabilityTheory.covarianceBilin_apply_eq_cov hMemLp]
    -- Reduce `covariance` to the centred inner-product integral (as in `exists_gaussianShift`).
    have hMean : ∀ w : EuclideanSpace ℝ (Fin k),
        (∫ x, ⟪w, x⟫ ∂(family h)) = ⟪w, h⟫ := hFamily.mean_eq h
    have hCovAsInt :
        ProbabilityTheory.covariance
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫)
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪v, x⟫) (family h)
          = ∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫ ∂(family h) := by
      simp_rw [ProbabilityTheory.covariance, hMean u, hMean v, ← inner_sub_right]
    rw [hCovAsInt, hFamily.cov_eq h u v]
    -- Finally, bridge `⟪u, (WithLp.equiv _).symm (C.mulVec (WithLp.equiv _ v))⟫`
    -- with `u.ofLp ⬝ᵥ C.mulVec v.ofLp` (coordinatewise, same trick as `cov_eq`).
    rw [show (u.ofLp ⬝ᵥ C.mulVec v.ofLp)
          = ∑ i, u.ofLp i * (C.mulVec v.ofLp) i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change C.mulVec v.ofLp i * u.ofLp i = u.ofLp i * C.mulVec v.ofLp i
    ring

/-- **`multivariateGaussian · C` is a Gaussian shift family with covariance `C`**, for
every positive-definite `C`. This is the concrete witness that downstream callers use
directly when they need `N(h, C)` rather than an abstract Gaussian-shift provider. -/
theorem isGaussianShift_multivariateGaussian
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : Matrix.PosDef C) :
    IsGaussianShift (fun h => ProbabilityTheory.multivariateGaussian h C) C := by
  have hCps : C.PosSemidef := hC.posSemidef
  refine
    { posDef := hC
      isProb := fun _ => inferInstance
      isGaussian := fun _ => inferInstance
      mean_eq := ?_
      cov_eq := ?_ }
  · intro h u
    have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.integrable_id
    rw [integral_inner hInt, ProbabilityTheory.integral_id_multivariateGaussian]
  · intro h u v
    have hMemLp : MeasureTheory.MemLp
        (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.memLp_two_id
    have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.integrable_id
    -- Mean under the Gaussian measure, specialised to both `u` and `v`.
    have hMean : ∀ w : EuclideanSpace ℝ (Fin k),
        (∫ x, ⟪w, x⟫ ∂ProbabilityTheory.multivariateGaussian h C) = ⟪w, h⟫ := by
      intro w
      rw [integral_inner hInt, ProbabilityTheory.integral_id_multivariateGaussian]
    -- Rewrite the target covariance-like integral as the covariance of the real-valued
    -- random variables `⟪u, ·⟫` and `⟪v, ·⟫` under the Gaussian.
    have hCovEq :
        ProbabilityTheory.covariance
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫)
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪v, x⟫)
            (ProbabilityTheory.multivariateGaussian h C)
          = ∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫
              ∂ProbabilityTheory.multivariateGaussian h C := by
      simp_rw [ProbabilityTheory.covariance, hMean u, hMean v, ← inner_sub_right]
    rw [← hCovEq, ← ProbabilityTheory.covarianceBilin_apply_eq_cov hMemLp,
      ProbabilityTheory.covarianceBilin_multivariateGaussian hCps]
    -- Finally, identify `u.ofLp ⬝ᵥ C.mulVec v.ofLp` with the `WithLp.equiv`-spelling
    -- inner product. Reduce both sides to `∑ i, u.ofLp i * (C.mulVec v.ofLp) i`.
    rw [show (u.ofLp ⬝ᵥ C.mulVec v.ofLp)
          = ∑ i, u.ofLp i * (C.mulVec v.ofLp) i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `⟪a, b⟫ = b * a` on `ℝ`, by definition of the real inner product.
    change u.ofLp i * C.mulVec v.ofLp i = C.mulVec v.ofLp i * u.ofLp i
    ring

/-- **Existence of a Gaussian shift family** with covariance `C` for every positive-definite
`C`. Realised by Mathlib's `ProbabilityTheory.multivariateGaussian h C`.

The closed-form log-likelihood ratio (`HasGaussianShiftLogLikelihoodRatio`) is *not*
bundled into this existence statement because it is not consumed downstream and its
derivation requires an explicit multivariate Gaussian density, which Mathlib does not
yet expose. If it becomes needed we will add a separate existence lemma that tightens
this one. -/
theorem exists_gaussianShift
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : Matrix.PosDef C) :
    ∃ family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)),
      IsGaussianShift family C :=
  ⟨fun h => ProbabilityTheory.multivariateGaussian h C,
    isGaussianShift_multivariateGaussian C hC⟩

/-- **Discharge of `HasTiltedLinearPushforward` for a Gaussian shift family.**

Given an abstract Gaussian-shift family `gauss h ~ N(h, J⁻¹)` and the positive-definite
covariance `J`, the tilted linear push-forward identity holds against the base
`multivariateGaussian 0 J`:
```
(gauss h).map (matrixAction J) =
  (multivariateGaussian 0 J).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫ - (1/2) * ⟪h, matrixAction J h⟫))).
```

Proof: Both sides equal `multivariateGaussian (toEuclideanCLM J h) J`.

* LHS: `gauss h = multivariateGaussian h J⁻¹` (`IsGaussianShift.eq_multivariateGaussian`).
  Apply `multivariateGaussian_map_toEuclideanCLM` with `A = J`, then collapse
  `J * J⁻¹ * Jᴴ = 1 * J = J` using `Matrix.PosDef.isUnit` + `Matrix.PosDef.isHermitian`.
* RHS: Rewrite the tilt `⟨h, matrixAction J h⟩` as `h.ofLp ⬝ᵥ J *ᵥ h.ofLp` via
  `Matrix.inner_toEuclideanCLM`, then apply `multivariateGaussian_withDensity_exp_shift`.

Lets Theorem 7.10 Step 7 discharge its `hTilt` provider internally once
`π.map snd = multivariateGaussian 0 J` has been identified. -/
theorem hasTiltedLinearPushforward_of_isGaussianShift
    {gauss : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k))}
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : Matrix.PosDef J)
    (hGauss : IsGaussianShift gauss J⁻¹) :
    HasTiltedLinearPushforward gauss
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) J := by
  intro h
  have hJ_ps : J.PosSemidef := hJ.posSemidef
  have hJinv_ps : J⁻¹.PosSemidef := hJ.inv.posSemidef
  have hJ_herm : Jᴴ = J := hJ.isHermitian.eq
  have hJ_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit
  -- LHS: `(gauss h).map (matrixAction J) = multivariateGaussian (J h) J`.
  have h_lhs : (gauss h).map (matrixAction J)
      = ProbabilityTheory.multivariateGaussian
          (Matrix.toEuclideanCLM (𝕜 := ℝ) J h) J := by
    rw [hGauss.eq_multivariateGaussian h,
      show (matrixAction J : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
          = Matrix.toEuclideanCLM (𝕜 := ℝ) J from
        funext (matrixAction_eq_toEuclideanCLM J),
      ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM (A := J)
        (μ := h) (S := J⁻¹) hJinv_ps,
      show J * J⁻¹ * Jᴴ = J from by
        rw [Matrix.mul_nonsing_inv _ hJ_unit, one_mul, hJ_herm]]
  -- Tilt equivalence: `⟪h, matrixAction J h⟫ = h.ofLp ⬝ᵥ J *ᵥ h.ofLp`.
  have h_tilt_eq : (1/2 : ℝ) * ⟪h, matrixAction J h⟫
      = (h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2 := by
    rw [matrixAction_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
    ring
  -- RHS: apply `multivariateGaussian_withDensity_exp_shift`.
  simp_rw [h_tilt_eq]
  rw [ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hJ_ps h]
  exact h_lhs

end GaussianShift
end AsymptoticStatistics
