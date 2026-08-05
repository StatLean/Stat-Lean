import StatLean.StatisticalModels.Gaussian.Conditioning

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- LEAN-ONLY -/
private theorem euclideanInner_eq_dotProduct' {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y :=
  dotProduct_comm _ _

/-- LEAN-ONLY -/
private theorem inner_toEuclideanLin_left' (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁)
    (t : EuclideanSpace ℝ ι₂) :
    ⟪Matrix.toEuclideanLin (𝕜 := ℝ) A x, t⟫_ℝ
      = ⟪x, Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t⟫_ℝ := by
  rw [euclideanInner_eq_dotProduct', euclideanInner_eq_dotProduct']
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_comm _ _

/-- LEAN-ONLY: transpose of the regression matrix. -/
private theorem transpose_condMeanMatrix {S₁₁ : Matrix ι₁ ι₁ ℝ} (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (h₁₁ : S₁₁.PosDef) : (condMeanMatrix S₁₁ S₁₂)ᵀ = S₁₁⁻¹ * S₁₂ := by
  have hsymm : S₁₁ᵀ = S₁₁ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact h₁₁.isHermitian
  rw [condMeanMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hsymm]

/-- LEAN-ONLY: the coordinate vector of a sum-index point is the `Sum.elim` of its blocks. -/
private theorem elim_ofLp (t : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    Sum.elim (WithLp.ofLp (blockFst t)) (WithLp.ofLp (blockSnd t)) = WithLp.ofLp t := by
  funext k; cases k <;> rfl

theorem compProd_gaussianCondKernel' (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    (h₁₁ : S₁₁.PosDef) :
    multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂
      = (multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)) := by
  have hSc : (condCovMatrix S₁₁ S₁₂ S₂₂).PosSemidef := posSemidef_condCovMatrix hJ h₁₁
  have hS : S₁₁.PosSemidef := h₁₁.posSemidef
  have hmeas : Measurable ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm :=
    (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm.measurable
  have key : (multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂).map
        ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm
      = multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) := by
    haveI : IsProbabilityMeasure
        ((multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂).map
          ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have hcont : Continuous fun x : EuclideanSpace ℝ (ι₁ ⊕ ι₂) =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I) := by fun_prop
    have hint : Integrable (fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
        Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm p, t⟫_ℝ : ℂ) * Complex.I))
        (multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂) :=
      Integrable.mono' (integrable_const 1)
        (hcont.measurable.comp hmeas).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by simp [Complex.norm_exp_ofReal_mul_I])
    rw [charFun_apply, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable,
      Measure.integral_compProd hint]
    have hinner : ∀ a : EuclideanSpace ℝ ι₁,
        ∫ b, Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm (a, b), t⟫_ℝ : ℂ)
              * Complex.I) ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a)
          = Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
                  - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
                  : ℝ) : ℂ) * Complex.I
                - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                      *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
            * Complex.exp ((⟪a, blockFst t
                  + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ)
                * Complex.I) := by
      intro a
      have hsplit : ∀ b : EuclideanSpace ℝ ι₂,
          Complex.exp ((⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm (a, b), t⟫_ℝ : ℂ)
              * Complex.I)
            = Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
              * Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I) := by
        intro b
        rw [← Complex.exp_add]
        congr 1
        simp only [sumMeasEquivProd_symm_apply, inner_sum_split (blockPair a b) t,
          blockFst_blockPair, blockSnd_blockPair]
        push_cast
        ring
      simp_rw [hsplit]
      have hcm : ∫ b, Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
            * Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
            ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a)
          = Complex.exp ((⟪a, blockFst t⟫_ℝ : ℂ) * Complex.I)
            * ∫ b, Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
                ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a) :=
        integral_const_mul _ _
      rw [hcm,
        show (∫ b, Complex.exp ((⟪b, blockSnd t⟫_ℝ : ℂ) * Complex.I)
              ∂(gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a))
            = charFun (gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ a) (blockSnd t) from
          (charFun_apply _).symm,
        gaussianCondKernel_apply, charFun_multivariateGaussian hSc,
        ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hA : ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) a⟫_ℝ
          = ⟪a, Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ := by
        rw [real_inner_comm, inner_toEuclideanLin_left', transpose_condMeanMatrix S₁₂ h₁₁]
      have hlin : ⟪blockSnd t,
            m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (a - m₁)⟫_ℝ
          = ⟪blockSnd t, m₂⟫_ℝ
            - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
            + ⟪a, Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ := by
        rw [map_sub, inner_add_right, inner_sub_right, hA]
        ring
      rw [hlin, inner_add_right]
      push_cast
      ring
    simp_rw [hinner]
    have hcm' : ∫ a, Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
              - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
              : ℝ) : ℂ) * Complex.I
            - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                  *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
          * Complex.exp ((⟪a, blockFst t
                + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
          ∂(multivariateGaussian m₁ S₁₁)
        = Complex.exp (((⟪blockSnd t, m₂⟫_ℝ
              - ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
              : ℝ) : ℂ) * Complex.I
            - ((WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
                  *ᵥ WithLp.ofLp (blockSnd t) : ℝ) : ℂ) / 2)
          * ∫ a, Complex.exp ((⟪a, blockFst t
                + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
              ∂(multivariateGaussian m₁ S₁₁) :=
      integral_const_mul _ _
    rw [hcm',
      show (∫ a, Complex.exp ((⟪a, blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)⟫_ℝ : ℂ) * Complex.I)
            ∂(multivariateGaussian m₁ S₁₁))
          = charFun (multivariateGaussian m₁ S₁₁)
              (blockFst t + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t)) from
        (charFun_apply _).symm,
      charFun_multivariateGaussian hS, charFun_multivariateGaussian hJ, ← Complex.exp_add]
    congr 1
    have hAm : ⟪blockSnd t, Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) m₁⟫_ℝ
        = ⟪Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t), m₁⟫_ℝ := by
      rw [real_inner_comm, inner_toEuclideanLin_left', transpose_condMeanMatrix S₁₂ h₁₁,
        real_inner_comm]
    have htm : ⟪t, blockPair m₁ m₂⟫_ℝ = ⟪blockFst t, m₁⟫_ℝ + ⟪blockSnd t, m₂⟫_ℝ := by
      simp [inner_sum_split t (blockPair m₁ m₂)]
    have hofLp : WithLp.ofLp (blockFst t
          + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
        = WithLp.ofLp (blockFst t) + (S₁₁⁻¹ * S₁₂) *ᵥ WithLp.ofLp (blockSnd t) := by
      simp [Matrix.toLpLin_apply]
    have hquad : WithLp.ofLp t ⬝ᵥ (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ WithLp.ofLp t
        = WithLp.ofLp (blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
            ⬝ᵥ S₁₁ *ᵥ WithLp.ofLp (blockFst t
              + Matrix.toEuclideanLin (𝕜 := ℝ) (S₁₁⁻¹ * S₁₂) (blockSnd t))
          + WithLp.ofLp (blockSnd t) ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂)
              *ᵥ WithLp.ofLp (blockSnd t) := by
      rw [hofLp, ← elim_ofLp t]
      exact dotProduct_fromBlocks_split S₁₁ S₁₂ S₂₂ h₁₁ _ _
    rw [htm, hquad, inner_add_left, hAm]
    push_cast
    ring
  rw [← key, Measure.map_map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).measurable hmeas,
    show (⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        ∘ ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) = id from
      funext fun p => (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).apply_symm_apply p,
    Measure.map_id]

end StatLean.StatisticalModels
