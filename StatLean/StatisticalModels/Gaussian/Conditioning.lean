import StatLean.StatisticalModels.Gaussian.Marginal
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Gaussian conditioning — the block conditional law

**The slice headline (G3.4).** For a joint Gaussian on the sum index `ι₁ ⊕ ι₂` with mean
blocks `(m₁, m₂)` and covariance `fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂` (one off-diagonal block
carried; its transpose is definitional), the conditional law of the second block given the
first is the Gaussian kernel
$$x \mapsto N\big(m₂ + S₂₁ S₁₁^{-1}(x - m₁),\; S₂₂ - S₂₁ S₁₁^{-1} S₁₂\big),$$
in the exact disintegration sense: `first marginal ⊗ₘ kernel = joint`. Mathlib has no
Gaussian conditioning in any form — this is the load-bearing substrate for BLUP/mixed
models (M-B2) and any finite-dimensional Gaussian regression.

* `condMeanMatrix` / `condCovMatrix` — the regression matrix `S₂₁ S₁₁⁻¹` and the Schur
  complement;
* `gaussianCondKernel` — the conditional kernel (constructed compositionally; its
  `@[simp]` spec is the contract), unconditionally Markov (the degenerate-parameter
  fallback of `multivariateGaussian` is a Dirac — still a probability);
* `posSemidef_condCovMatrix` (G3.1) — the Schur complement is a genuine covariance;
* `dotProduct_fromBlocks_split` (G3.2) — completing the square in the quadratic form, the
  charFun engine;
* **`compProd_gaussianCondKernel` (G3.4)** — the headline disintegration identity;
* `condKernel_ae_eq_gaussianCondKernel` (G3.5) — the abstract disintegration kernel of the
  joint agrees a.e. with the explicit Gaussian kernel (uniqueness of disintegration).

PSD-degenerate `S₁₁` (pseudoinverse form) is a named future debt (D-G1); the conditional-
expectation corollary is deferred with it.

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, Thm 2.5.1 (the conditional normal law) (verify §) (`And58 Thm 2.5.1`);
M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Wiley, 1983, Prop. 3.13
(verify §).

**Proof formalization notes.** charFun-only, on the sum space (the area doctrine): the
charFun of the compProd is computed by `MeasureTheory.integral_compProd` (bounded
integrand), the inner Gaussian charFun contributes the affine-mean phase, the outer
integral is the `S₁₁`-charFun at the shifted argument `t₁ + S₁₁⁻¹S₁₂ t₂`, and G3.2/the
mean split reassemble the joint block charFun; conclude by `Measure.ext_of_charFun`
transported through `ext_of_map_sumMeasEquivProd`. `S₁₁.PosDef` is USER-INPUT (the
classical nondegeneracy of the conditioning block); the joint PSD is USER-INPUT.

**Bibliographic comments.** The conditional normal distribution is 19th-century
(Galton–Pearson regression); the matrix form with the Schur complement is standard since
Anderson (1958). The disintegration (`compProd`) formulation is the modern
regular-conditional-probability reading.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- The Gaussian regression matrix `S₂₁ S₁₁⁻¹` (And58 Thm 2.5.1). -/
noncomputable def condMeanMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) :
    Matrix ι₂ ι₁ ℝ :=
  S₁₂ᵀ * S₁₁⁻¹

/-- The **Schur complement** `S₂₂ − S₂₁ S₁₁⁻¹ S₁₂` — the conditional covariance
(And58 Thm 2.5.1). -/
noncomputable def condCovMatrix (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ) : Matrix ι₂ ι₂ ℝ :=
  S₂₂ - S₁₂ᵀ * S₁₁⁻¹ * S₁₂

omit [DecidableEq ι₂] in
/-- LEAN-ONLY: a matrix acts measurably on Euclidean space (linear on a
finite-dimensional space, hence continuous). -/
private theorem measurable_toEuclideanLin (A : Matrix ι₂ ι₁ ℝ) :
    Measurable fun x : EuclideanSpace ℝ ι₁ => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) A).continuous_of_finiteDimensional).measurable

omit [Fintype ι₁] [DecidableEq ι₁] in
/-- LEAN-ONLY: translation of `multivariateGaussian` with **no** PSD side condition — the
degenerate-parameter fallback is a Dirac mass, which translates as well. -/
private theorem multivariateGaussian_map_add_left (m : EuclideanSpace ℝ ι₂)
    (S : Matrix ι₂ ι₂ ℝ) (c : EuclideanSpace ℝ ι₂) :
    (multivariateGaussian m S).map (fun x => c + x) = multivariateGaussian (c + m) S := by
  by_cases hS : S.PosSemidef
  · exact multivariateGaussian_map_const_add m S hS c
  · rw [multivariateGaussian_of_not_posSemidef _ hS,
      multivariateGaussian_of_not_posSemidef _ hS]
    exact Measure.map_dirac' (measurable_const_add c) m

/-- The **Gaussian conditional kernel**
`x ↦ N(m₂ + S₂₁S₁₁⁻¹(x − m₁), S₂₂ − S₂₁S₁₁⁻¹S₁₂)` (And58 Thm 2.5.1). Constructed
compositionally (the `@[simp]` spec below is the frozen contract). -/
noncomputable def gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ) :
    Kernel (EuclideanSpace ℝ ι₁) (EuclideanSpace ℝ ι₂) :=
  affineNoiseKernel (multivariateGaussian 0 (condCovMatrix S₁₁ S₁₂ S₂₂))
    (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) x)
    (measurable_toEuclideanLin _)
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

/-- **G3.1, the Schur complement is PSD** (Schur 1917; And58 Thm 2.5.1): under a genuine
joint covariance with nondegenerate conditioning block, the conditional covariance is a
covariance. -/
theorem posSemidef_condCovMatrix {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₁₂ : Matrix ι₁ ι₂ ℝ}
    {S₂₂ : Matrix ι₂ ι₂ ℝ}
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    (condCovMatrix S₁₁ S₁₂ S₂₂).PosSemidef := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have h := (Matrix.PosDef.fromBlocks₁₁ (A := S₁₁) S₁₂ S₂₂ h₁₁).mp (by rwa [hconj])
  rwa [hconj] at h

/-- **G3.2, completing the square** — the block quadratic form splits into the marginal
form at the shifted argument plus the Schur form (the charFun engine). -/
theorem dotProduct_fromBlocks_split (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: nondegenerate symmetric conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) (t₁ : ι₁ → ℝ) (t₂ : ι₂ → ℝ) :
    Sum.elim t₁ t₂ ⬝ᵥ (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ Sum.elim t₁ t₂
      = (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂) ⬝ᵥ S₁₁ *ᵥ (t₁ + (S₁₁⁻¹ * S₁₂) *ᵥ t₂)
          + t₂ ⬝ᵥ (condCovMatrix S₁₁ S₁₂ S₂₂) *ᵥ t₂ := by
  haveI : Invertible S₁₁ := h₁₁.isUnit.invertible
  have hconj : S₁₂ᴴ = S₁₂ᵀ := Matrix.conjTranspose_eq_transpose_of_trivial S₁₂
  have h := Matrix.schur_complement_eq₁₁ (A := S₁₁) S₁₂ S₂₂ t₁ t₂ h₁₁.isHermitian
  rw [hconj] at h
  simp only [star_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    condCovMatrix]
  exact h

/-- **G3.4, HEADLINE — Gaussian conditioning as exact disintegration** (And58 Thm 2.5.1;
Eaton Prop. 3.13): the first block marginal composed with the Gaussian conditional kernel
is the joint block Gaussian. Mathlib has no Gaussian conditioning; this is the substrate
theorem for BLUP and Gaussian regression. -/
theorem compProd_gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    multivariateGaussian m₁ S₁₁ ⊗ₘ gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂
      = (multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)) := by
  sorry

/-- **G3.5, uniqueness corollary**: the abstract disintegration kernel of the joint law
agrees a.e. with the explicit Gaussian conditional kernel. -/
theorem condKernel_ae_eq_gaussianCondKernel (m₁ : EuclideanSpace ℝ ι₁)
    (m₂ : EuclideanSpace ℝ ι₂) (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ)
    (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: genuine joint covariance; And58 Thm 2.5.1
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef)
    -- USER-INPUT: nondegenerate conditioning block; And58 Thm 2.5.1
    (h₁₁ : S₁₁.PosDef) :
    ∀ᵐ x ∂(multivariateGaussian m₁ S₁₁),
      ((multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
            (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))).condKernel x
        = gaussianCondKernel m₁ m₂ S₁₁ S₁₂ S₂₂ x := by
  sorry

end StatLean.StatisticalModels
