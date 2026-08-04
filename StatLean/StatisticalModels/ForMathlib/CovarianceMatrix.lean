import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance

/-!
# Mean vector and covariance matrix of a law on Euclidean space

The canonical second-moment objects for measures on `EuclideanSpace ℝ ι`, the shared substrate
of the Gaussian, mixed-effects and GEE slices:

* `meanVec μ` — the Bochner mean vector `∫ x ∂μ`;
* `covMatrix μ` — the covariance matrix `Σᵢⱼ = cov(xᵢ, xⱼ)`;
* `crossCovMatrix μ f g` — the cross-covariance matrix of two vector statistics;

with the calculus: positive semidefiniteness, the values on `multivariateGaussian`, the affine
pushforward law `Σ ↦ A Σ Aᵀ`, additivity for independent summands (product form and
finite-product form), and the cross-covariance rules.

Every statement carries `MemLp` second-moment hypotheses as USER-INPUT: Mathlib's `covariance`
junk-values to `0` without integrability, so the lemmas would be silently vacuous, not false.

The library has three prior ad-hoc special cases (`HypothesisTesting.covMatrix` on
`Fin k`-Euclidean space, `sampleCovMatrix`, `marginalCovMatrix`); this file is the general
carrier. Deduplication of those is a documented laptop follow-up — no other area is touched
here.

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, Wiley,
1958, Ch. 2 (moments of random vectors; the affine transformation law) (verify §)
(`And58 Ch. 2`).

**Proof formalization notes.** PSD generalizes the `Fin k` argument used privately at
`HypothesisTesting/Bootstrap/Multivariate.lean` (quadratic form = variance of `⟪u, ·⟫ ≥ 0`).
Affine pushforward is coordinate bilinearity of `covariance` (`covariance_add_left`-family)
plus `integral_map`; the Gaussian values are `integral_id_multivariateGaussian` and
`covariance_eval_multivariateGaussian`. Independent additivity kills cross terms with the
independence-vanishing lemma for `covariance` under `Measure.prod` coordinates.

**Bibliographic comments.** The covariance-matrix calculus is 19th-century (Bravais, Pearson);
its systematic matrix form is Anderson (1958). Nothing here is original.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂]
  {Ω : Type*} [MeasurableSpace Ω]

/-- The **mean vector** `∫ x ∂μ` of a law on Euclidean space (And58 Ch. 2). -/
noncomputable def meanVec (μ : Measure (EuclideanSpace ℝ ι)) : EuclideanSpace ℝ ι :=
  ∫ x, x ∂μ

/-- The **covariance matrix** `Σᵢⱼ = cov(xᵢ, xⱼ)` of a law on Euclidean space
(And58 Ch. 2). Junk-values to `0` entries without second moments. -/
noncomputable def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => cov[fun x => x i, fun x => x j; μ]

/-- The **cross-covariance matrix** of two vector statistics on a common sample space
(the BLUP/Godambe workhorse). -/
noncomputable def crossCovMatrix (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) : Matrix ι₁ ι₂ ℝ :=
  Matrix.of fun i j => cov[fun ω => f ω i, fun ω => g ω j; μ]

@[simp]
theorem covMatrix_apply (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = cov[fun x => x i, fun x => x j; μ] := rfl

@[simp]
theorem crossCovMatrix_apply (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) (i : ι₁) (j : ι₂) :
    crossCovMatrix μ f g i j = cov[fun ω => f ω i, fun ω => g ω j; μ] := rfl

/-- The covariance matrix is symmetric. -/
theorem covMatrix_transpose (μ : Measure (EuclideanSpace ℝ ι)) :
    (covMatrix μ)ᵀ = covMatrix μ := by
  sorry

/-- Cross-covariance transposes to the swapped cross-covariance. -/
theorem crossCovMatrix_transpose (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι₁)
    (g : Ω → EuclideanSpace ℝ ι₂) :
    (crossCovMatrix μ f g)ᵀ = crossCovMatrix μ g f := by
  sorry

/-- **Positive semidefiniteness** of the covariance matrix (And58 Ch. 2): the quadratic form
`uᵀ Σ u` is the variance of `⟪u, x⟫`. -/
theorem posSemidef_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    -- USER-INPUT: second moments; And58 Ch. 2
    (hL2 : MemLp id 2 μ) :
    (covMatrix μ).PosSemidef := by
  sorry

/-- Mean vector of the multivariate Gaussian. -/
theorem meanVec_multivariateGaussian [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ)
    -- USER-INPUT: a genuine covariance parameter; And58 Ch. 2
    (hS : S.PosSemidef) :
    meanVec (multivariateGaussian m S) = m := by
  sorry

/-- Covariance matrix of the multivariate Gaussian. -/
theorem covMatrix_multivariateGaussian [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ)
    -- USER-INPUT: a genuine covariance parameter; And58 Ch. 2
    (hS : S.PosSemidef) :
    covMatrix (multivariateGaussian m S) = S := by
  sorry

/-- **Mean of an affine pushforward**: `E[A x + b] = A (E x) + b` (And58 Ch. 2). -/
theorem meanVec_map_affine [DecidableEq ι₁] (μ : Measure (EuclideanSpace ℝ ι₁))
    [IsProbabilityMeasure μ]
    (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂)
    -- USER-INPUT: first moments; And58 Ch. 2
    (h1 : Integrable id μ) :
    meanVec (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = Matrix.toEuclideanLin (𝕜 := ℝ) A (meanVec μ) + b := by
  sorry

/-- **Covariance of an affine pushforward**: `Cov(A x + b) = A Σ Aᵀ` (And58 Ch. 2). -/
theorem covMatrix_map_affine [DecidableEq ι₁] (μ : Measure (EuclideanSpace ℝ ι₁))
    [IsProbabilityMeasure μ]
    (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂)
    -- USER-INPUT: second moments; And58 Ch. 2
    (hL2 : MemLp id 2 μ) :
    covMatrix (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = A * covMatrix μ * Aᵀ := by
  sorry

/-- **Additivity under independence (product form)**: the covariance of a sum of linear images
of the two independent coordinates of a product law is the sum of the transported covariances
— cross terms vanish (And58 Ch. 2). -/
theorem covMatrix_map_add_prod [DecidableEq ι₁] [DecidableEq ι₂]
    (μ : Measure (EuclideanSpace ℝ ι₁))
    (ν : Measure (EuclideanSpace ℝ ι₂)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ι₃ : Type*} [Fintype ι₃]
    (A : Matrix ι₃ ι₁ ℝ) (B : Matrix ι₃ ι₂ ℝ)
    -- USER-INPUT: second moments of both factors; And58 Ch. 2
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    covMatrix ((μ.prod ν).map fun p =>
        Matrix.toEuclideanLin (𝕜 := ℝ) A p.1 + Matrix.toEuclideanLin (𝕜 := ℝ) B p.2)
      = A * covMatrix μ * Aᵀ + B * covMatrix ν * Bᵀ := by
  sorry

/-- **Additivity under independence (finite-product form)**: covariance of a sum of linear
images of independent coordinates under `Measure.pi` (the L2/M1 workhorse). -/
theorem covMatrix_map_sum_pi [DecidableEq ι₁] {N : ℕ}
    (μs : Fin N → Measure (EuclideanSpace ℝ ι₁))
    [∀ k, IsProbabilityMeasure (μs k)]
    {ι₃ : Type*} [Fintype ι₃] (A : Fin N → Matrix ι₃ ι₁ ℝ)
    -- USER-INPUT: second moments of every factor; And58 Ch. 2
    (hL2 : ∀ k, MemLp id 2 (μs k)) :
    covMatrix ((Measure.pi μs).map fun x =>
        ∑ k, Matrix.toEuclideanLin (𝕜 := ℝ) (A k) (x k))
      = ∑ k, A k * covMatrix (μs k) * (A k)ᵀ := by
  sorry

/-- Cross-covariance of a statistic with itself under the image law. -/
theorem crossCovMatrix_self (μ : Measure Ω) {f : Ω → EuclideanSpace ℝ ι₁}
    -- LEAN-ONLY: measurability for the image-law rewrite
    (hf : AEMeasurable f μ) :
    crossCovMatrix μ f f = covMatrix (μ.map f) := by
  sorry

end StatLean.StatisticalModels
