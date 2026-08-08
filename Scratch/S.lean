import StatLean.StatisticalModels.Longitudinal.Sandwich

set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace StatLean.StatisticalModels.Longitudinal
open StatLean.StatisticalModels
variable {N m q : ℕ}

section Helpers
variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]

private theorem toEuclideanLin_comp (A : Matrix ι₃ ι₂ ℝ) (B : Matrix ι₂ ι₁ ℝ)
    (x : EuclideanSpace ℝ ι₁) :
    Matrix.toEuclideanLin (𝕜 := ℝ) A (Matrix.toEuclideanLin (𝕜 := ℝ) B x)
      = Matrix.toEuclideanLin (𝕜 := ℝ) (A * B) x := by
  simp [Matrix.toLpLin_apply]

private theorem toEuclideanLin_one_apply (x : EuclideanSpace ℝ ι₁) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix ι₁ ι₁ ℝ) x = x := by
  simp

private noncomputable def matCLM (A : Matrix ι₂ ι₁ ℝ) :
    EuclideanSpace ℝ ι₁ →L[ℝ] EuclideanSpace ℝ ι₂ :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (𝕜 := ℝ) A)

private theorem matCLM_apply (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁) :
    matCLM A x = Matrix.toEuclideanLin (𝕜 := ℝ) A x := rfl

variable {N' : ℕ} (μs : Fin N' → Measure (EuclideanSpace ℝ ι₁))
  [∀ k, IsProbabilityMeasure (μs k)]

private theorem memLp_coord (hL2 : ∀ k, MemLp id 2 (μs k)) (k : Fin N') :
    MemLp (fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k) 2 (Measure.pi μs) := by
  simpa [Function.comp_def] using (hL2 k).comp_measurePreserving (measurePreserving_eval μs k)

private theorem integrable_coord (h1 : ∀ k, Integrable id (μs k)) (k : Fin N') :
    Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k) (Measure.pi μs) := by
  simpa [Function.comp_def] using
    (measurePreserving_eval μs k).integrable_comp_of_integrable (h1 k)

private theorem integral_coord (k : Fin N') :
    ∫ x : Fin N' → EuclideanSpace ℝ ι₁, x k ∂(Measure.pi μs) = meanVec (μs k) := by
  have h := (measurePreserving_eval μs k).map_eq
  rw [meanVec, ← h]
  exact (integral_map (φ := fun x : Fin N' → EuclideanSpace ℝ ι₁ => x k)
    (f := fun y : EuclideanSpace ℝ ι₁ => y) (measurable_pi_apply k).aemeasurable
    (by fun_prop)).symm

private theorem continuous_wsum (A : Fin N' → Matrix ι₃ ι₁ ℝ) :
    Continuous fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k) := by
  refine continuous_finset_sum Finset.univ fun k _ => ?_
  exact (matCLM (A k)).continuous.comp (continuous_apply k)

/-- Mean of the pushforward of a weighted sum of independent coordinates plus a constant. -/
private theorem meanVec_map_wsum_add (A : Fin N' → Matrix ι₃ ι₁ ℝ) (b : EuclideanSpace ℝ ι₃)
    (h1 : ∀ k, Integrable id (μs k)) :
    meanVec ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (meanVec (μs k))) + b := by
  have hterm : ∀ k, Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) (Measure.pi μs) := fun k =>
    (matCLM (A k)).integrable_comp (integrable_coord μs h1 k)
  have hG : Integrable (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) (Measure.pi μs) :=
    integrable_finset_sum _ fun k _ => hterm k
  have hcont : Continuous fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b :=
    (continuous_wsum A).add continuous_const
  rw [meanVec, integral_map (f := fun y : EuclideanSpace ℝ ι₃ => y) hcont.aemeasurable
    (by fun_prop)]
  have hsplit : ∫ x : Fin N' → EuclideanSpace ℝ ι₁,
        ((∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b) ∂(Measure.pi μs)
      = (∫ x : Fin N' → EuclideanSpace ℝ ι₁,
          (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) ∂(Measure.pi μs))
        + ∫ _x : Fin N' → EuclideanSpace ℝ ι₁, b ∂(Measure.pi μs) :=
    integral_add hG (integrable_const b)
  rw [hsplit, integral_const, integral_finset_sum _ fun k _ => hterm k]
  simp only [probReal_univ, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k))
      = (fun x : Fin N' → EuclideanSpace ℝ ι₁ => matCLM (A k) (x k)) from rfl,
    (matCLM (A k)).integral_comp_comm (integrable_coord μs h1 k), integral_coord μs k,
    matCLM_apply]

/-- Covariance of the pushforward of a weighted sum of independent coordinates plus a
constant — the constant drops out. -/
private theorem covMatrix_map_wsum_add (A : Fin N' → Matrix ι₃ ι₁ ℝ) (b : EuclideanSpace ℝ ι₃)
    (hL2 : ∀ k, MemLp id 2 (μs k)) :
    covMatrix ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = ∑ k, A k * covMatrix (μs k) * (A k)ᵀ := by
  have hmeasG : Measurable fun x : Fin N' → EuclideanSpace ℝ ι₁ =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k) := (continuous_wsum A).measurable
  haveI hprob : IsProbabilityMeasure ((Measure.pi μs).map fun x =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) :=
    Measure.isProbabilityMeasure_map hmeasG.aemeasurable
  have hL2ν : MemLp id 2 ((Measure.pi μs).map fun x =>
      ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmeasG.aemeasurable]
    simpa [Function.comp_def] using memLp_finset_sum Finset.univ fun k (_ : k ∈ Finset.univ) =>
      (matCLM (A k)).comp_memLp' (memLp_coord μs hL2 k)
  have hmap : ((Measure.pi μs).map fun x =>
        (∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)) + b)
      = ((Measure.pi μs).map fun x =>
          ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k)).map
        fun z => Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix ι₃ ι₃ ℝ) z + b := by
    rw [Measure.map_map (by fun_prop) hmeasG]
    congr 1
    funext x
    simp
  rw [hmap, covMatrix_map_affine _ 1 b hL2ν, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, covMatrix_map_sum_pi μs A hL2]

end Helpers


section Main
variable (D : Fin N → Matrix (Fin m) (Fin q) ℝ) (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)

private theorem sum_weight_apply (β₀ : EuclideanSpace ℝ (Fin q)) :
    ∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹)
        (Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
      = Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V) β₀ := by
  simp only [toEuclideanLin_comp, geeBread, map_sum, LinearMap.sum_apply]

private theorem geeBread_transpose (hVsymm : ∀ i, (V i)ᵀ = V i) :
    (geeBread D V)ᵀ = geeBread D V := by
  simp only [geeBread, Matrix.transpose_sum, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hVsymm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Matrix.mul_assoc]

private theorem geeScoreTotal_eq (β₀ : EuclideanSpace ℝ (Fin q)) :
    geeScoreTotal D V β₀ = fun y : Fin N → EuclideanSpace ℝ (Fin m) =>
      (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹) (y i))
        + (-Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V) β₀) := by
  funext y
  rw [← sub_eq_add_neg, ← sum_weight_apply D V β₀, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => map_sub _ _ _

private theorem geeEstimatorMap_eq :
    geeEstimatorMap D V = fun y : Fin N → EuclideanSpace ℝ (Fin m) =>
      (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ)
        ((geeBread D V)⁻¹ * ((D i)ᵀ * (V i)⁻¹)) (y i)) + (0 : EuclideanSpace ℝ (Fin q)) := by
  funext y
  rw [add_zero, geeEstimatorMap, map_sum]
  exact Finset.sum_congr rfl fun i _ => toEuclideanLin_comp _ _ _

theorem tst1 (β₀ : EuclideanSpace ℝ (Fin q))
    (hB : IsUnit (geeBread D V).det) (y : Fin N → EuclideanSpace ℝ (Fin m)) :
    geeEstimatorMap D V y
      = β₀ + Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V)⁻¹ (geeScoreTotal D V β₀ y) := by
  simp only [geeScoreTotal_eq D V β₀]
  rw [← sub_eq_add_neg, map_sub, toEuclideanLin_comp, Matrix.nonsing_inv_mul _ hB,
    toEuclideanLin_one_apply, geeEstimatorMap]
  abel

theorem tst2 (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m))) [∀ i, IsProbabilityMeasure (Qs i)]
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    (hL1 : ∀ i, Integrable id (Qs i)) :
    meanVec ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = 0 := by
  rw [geeScoreTotal_eq D V β₀, meanVec_map_wsum_add Qs _ _ hL1]
  simp only [hmean]
  rw [sum_weight_apply]
  abel

theorem tst3 (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m))) [∀ i, IsProbabilityMeasure (Qs i)]
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    (hL1 : ∀ i, Integrable id (Qs i)) (hB : IsUnit (geeBread D V).det) :
    meanVec ((Measure.pi Qs).map (geeEstimatorMap D V)) = β₀ := by
  have hsum : ∑ i, (geeBread D V)⁻¹ * ((D i)ᵀ * (V i)⁻¹) * D i
      = (geeBread D V)⁻¹ * geeBread D V := by
    rw [geeBread, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_assoc]
  rw [geeEstimatorMap_eq D V, meanVec_map_wsum_add Qs _ _ hL1, add_zero]
  simp only [hmean, toEuclideanLin_comp]
  rw [← LinearMap.sum_apply, ← map_sum, hsum, Matrix.nonsing_inv_mul _ hB,
    toEuclideanLin_one_apply]

theorem tst4 (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m))) [∀ i, IsProbabilityMeasure (Qs i)]
    (hcov : ∀ i, covMatrix (Qs i) = Covs i) (hL2 : ∀ i, MemLp id 2 (Qs i))
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    covMatrix ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = geeMeat D V Covs := by
  rw [geeScoreTotal_eq D V β₀, covMatrix_map_wsum_add Qs _ _ hL2, geeMeat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcov, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hVsymm,
    Matrix.transpose_transpose, ← Matrix.mul_assoc]

theorem tst5 (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m))) [∀ i, IsProbabilityMeasure (Qs i)]
    (hcov : ∀ i, covMatrix (Qs i) = Covs i) (hL2 : ∀ i, MemLp id 2 (Qs i))
    (hVsymm : ∀ i, (V i)ᵀ = V i) (hB : IsUnit (geeBread D V).det) :
    covMatrix ((Measure.pi Qs).map (geeEstimatorMap D V))
      = (geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹ := by
  have hBt : ((geeBread D V)⁻¹)ᵀ = (geeBread D V)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, geeBread_transpose D V hVsymm]
  rw [geeEstimatorMap_eq D V, covMatrix_map_wsum_add Qs _ _ hL2, geeMeat, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcov, Matrix.transpose_mul, hBt, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    hVsymm, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

end Main

end StatLean.StatisticalModels.Longitudinal
