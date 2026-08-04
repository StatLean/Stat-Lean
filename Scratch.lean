import StatLean.StatisticalModels.Gaussian.Marginal
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

#check @ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
#check @MeasureTheory.Measure.integral_compProd
#check @Matrix.PosDef.fromBlocks₁₁

noncomputable def condMeanMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) :
    Matrix ι₂ ι₁ ℝ :=
  S₁₂ᵀ * S₁₁⁻¹

noncomputable def condCovMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ) : Matrix ι₂ ι₂ ℝ :=
  S₂₂ - S₁₂ᵀ * S₁₁⁻¹ * S₁₂

/-- LEAN-ONLY -/
private theorem meas_toEuclideanLin (A : Matrix ι₂ ι₁ ℝ) :
    Measurable fun x : EuclideanSpace ℝ ι₁ => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) A).continuous_of_finiteDimensional).measurable

/-- LEAN-ONLY: translation of `multivariateGaussian`, with no PSD hypothesis (the
non-PSD fallback is a Dirac, which translates too). -/
private theorem multivariateGaussian_map_add_left (m : EuclideanSpace ℝ ι₂)
    (S : Matrix ι₂ ι₂ ℝ) (c : EuclideanSpace ℝ ι₂) :
    (multivariateGaussian m S).map (fun x => c + x) = multivariateGaussian (c + m) S := by
  by_cases hS : S.PosSemidef
  · exact multivariateGaussian_map_const_add m S hS c
  · rw [multivariateGaussian_of_not_posSemidef _ hS,
      multivariateGaussian_of_not_posSemidef _ hS]
    exact Measure.map_dirac' (measurable_const_add c) m

noncomputable def gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ) :
    Kernel (EuclideanSpace ℝ ι₁) (EuclideanSpace ℝ ι₂) :=
  affineNoiseKernel (multivariateGaussian 0 (condCovMatrix S₁₁ S₁₂ S₂₂))
    (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) x)
    (meas_toEuclideanLin _)
    (m₂ - Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁)

@[simp]
theorem gaussianCondKernel_apply (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    (x : EuclideanSpace ℝ ι₁) :
    gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ x
      = multivariateGaussian
          (m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (x - m₁))
          (condCovMatrix S₁₁ S₁₂ S₂₂) := by
  rw [gaussianCondKernel, affineNoiseKernel_apply, multivariateGaussian_map_add_left]
  congr 1
  rw [add_zero, map_sub]
  abel

instance (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂) (S₁₁ : Matrix ι₁ ι₁ ℝ)
    (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ) :
    IsMarkovKernel (gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂) := by
  rw [gaussianCondKernel]; infer_instance

/-- G3.1 -/
theorem posSemidef_condCovMatrix {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₁₂ : Matrix ι₁ ι₂ ℝ}
    {S₂₂ : Matrix ι₂ ι₂ ℝ}
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    (h₁₁ : S₁₁.PosDef) :
    (condCovMatrix S₁₁ S₁₂ S₂₂).PosSemidef := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have := (Matrix.PosDef.fromBlocks₁₁ (A := S₁₁) S₁₂ S₂₂ h₁₁).mp (by rwa [hconj])
  rwa [hconj] at this

/-- G3.2 -/
theorem dotProduct_fromBlocks_split (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ)
    (h₁₁ : S₁₁.PosDef) (t₁ : ι₁ → ℝ) (t₂ : ι₂ → ℝ) :
    Sum.elim t₁ t₂ ⬝ᵥ (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ Sum.elim t₁ t₂
      = (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂) ⬝ᵥ S₁₁ *ᵥ (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂)
          + t₂ ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂) *ᵥ t₂ := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have h := Matrix.schur_complement_eq₁₁ (A := S₁₁) S₁₂ S₂₂ t₁ t₂ h₁₁.isHermitian
  rw [hconj] at h
  simp only [star_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  rw [condCovMatrix]
  exact h

end StatLean.StatisticalModels
