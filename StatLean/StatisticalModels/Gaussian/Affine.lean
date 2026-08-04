import StatLean.StatisticalModels.Gaussian.BlockIndex
import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianConv

/-!
# Affine images of multivariate Gaussians — and the affine-noise kernel

The transformation calculus of the Gaussian slice:

* `affineNoiseKernel ν A b` — the kernel `x ↦ law of (A x + b + ξ)`, `ξ ∼ ν` — built
  compositionally (deterministic ×ₖ constant, then mapped), so measurability is inherited,
  never hand-proved; this is the shape of every Gaussian conditional kernel;
* `charFun_map_matrix` — the characteristic function of a linear image:
  `φ_{Aμ}(t) = φ_μ(Aᵀ t)` (matrix form, adjoint-free);
* `multivariateGaussian_map_const_add` — translation;
* **`multivariateGaussian_map_affine` (G2.4, the slice's workhorse)** — the affine image of
  a Gaussian is Gaussian with mean `A m + b` and covariance `A S Aᵀ`.

Sums of independent Gaussians are already available —
`AsymptoticStatistics.ForMathlib.MultivariateGaussianConv` (imported, reused, not restated).

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, §2.4 (linear transformations of normal vectors) (verify §) (`And58 §2.4`).

**Proof formalization notes.** All Gaussian identities go through characteristic functions
(`charFun_multivariateGaussian` + `Measure.ext_of_charFun`) — never densities (the pin has
no Lebesgue-density lemma for `multivariateGaussian`) and never the `CFC.sqrt` definition.
`Aᵀ` transposes across the real inner product by `Matrix.toEuclideanLin`-vs-`dotProduct`
algebra; the PSD side condition `(A S Aᵀ).PosSemidef` is
`Matrix.PosSemidef.mul_mul_conjTranspose_same`-shaped.

**Bibliographic comments.** Classical (Anderson 1958 and earlier); nothing original.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The **affine-noise kernel** `x ↦ law of (A x + b + ξ)`, `ξ ∼ ν` — compositional
construction, measurability inherited. -/
noncomputable def affineNoiseKernel {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
    [AddCommMonoid E₂] [MeasurableAdd₂ E₂] (ν : Measure E₂) (A : E₁ → E₂)
    -- LEAN-ONLY: measurability of the affine part
    (hA : Measurable A) (b : E₂) : Kernel E₁ E₂ :=
  ((Kernel.deterministic A hA) ×ₖ Kernel.const E₁ ν).map fun p => p.1 + b + p.2

@[simp]
theorem affineNoiseKernel_apply {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
    [AddCommMonoid E₂] [MeasurableAdd₂ E₂] (ν : Measure E₂) [SFinite ν] {A : E₁ → E₂}
    (hA : Measurable A) (b : E₂) (x : E₁) :
    affineNoiseKernel ν A hA b x = ν.map fun z => A x + b + z := by
  sorry

instance {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂] [AddCommMonoid E₂]
    [MeasurableAdd₂ E₂] (ν : Measure E₂) [IsProbabilityMeasure ν] {A : E₁ → E₂}
    (hA : Measurable A) (b : E₂) : IsMarkovKernel (affineNoiseKernel ν A hA b) := by
  sorry

/-- Characteristic function of a linear image, matrix (adjoint-free) form:
`φ_{Aμ}(t) = φ_μ(Aᵀ t)`. -/
theorem charFun_map_matrix [DecidableEq ι₁] [DecidableEq ι₂]
    (μ : Measure (EuclideanSpace ℝ ι₁)) (A : Matrix ι₂ ι₁ ℝ) (t : EuclideanSpace ℝ ι₂) :
    charFun (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x) t
      = charFun μ (Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t) := by
  sorry

/-- Translation of a multivariate Gaussian. -/
theorem multivariateGaussian_map_const_add [DecidableEq ι₁] (m : EuclideanSpace ℝ ι₁)
    (S : Matrix ι₁ ι₁ ℝ)
    -- USER-INPUT: genuine covariance parameter; And58 §2.4
    (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι₁) :
    (multivariateGaussian m S).map (fun x => c + x) = multivariateGaussian (c + m) S := by
  sorry

/-- **G2.4, affine image of a Gaussian** (`And58 §2.4`): the image of `N(m, S)` under
`x ↦ A x + b` is `N(A m + b, A S Aᵀ)`. -/
theorem multivariateGaussian_map_affine [DecidableEq ι₁] [DecidableEq ι₂]
    (m : EuclideanSpace ℝ ι₁) (S : Matrix ι₁ ι₁ ℝ)
    -- USER-INPUT: genuine covariance parameter; And58 §2.4
    (hS : S.PosSemidef) (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂) :
    (multivariateGaussian m S).map
        (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = multivariateGaussian (Matrix.toEuclideanLin (𝕜 := ℝ) A m + b) (A * S * Aᵀ) := by
  sorry

end StatLean.StatisticalModels
