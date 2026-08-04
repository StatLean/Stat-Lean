import StatLean.StatisticalModels.MixedEffects.Defs
import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix
import StatLean.StatisticalModels.Gaussian.Affine

/-!
# Marginal moments and the Gaussian marginal of the linear mixed model

The two marginal theorems of the LMM:

* **M1 (no Gaussianity)** — under mean-zero, second-moment latent effects and noise:
  `E Y = Xβ` and `Cov Y = Z·Cov(b)·Zᵀ + Cov(ε)` — pure covariance calculus, valid for
  arbitrary latent laws;
* **M2 (Gaussian case)** — with `b ∼ N(0, Gm)` and `ε ∼ N(0, Rm)`:
  `Y ∼ N(Xβ, Z Gm Zᵀ + Rm)` (`LW82` Eq. (1.2)) — the affine-image and convolution calculus
  of the Gaussian slice.

**Reference.** `LW82` Eq. (1.2); `FLW Ch. 8` (verify §); `MSN Ch. 6` (verify §).

**Proof formalization notes.** M1 instantiates the G-B1 covariance calculus
(`covMatrix_map_add_prod` at `A = Z`, `B = 1`, plus the constant shift `Xβ` through
`covMatrix_map_affine`/`meanVec_map_affine`). M2 rewrites `lmmLaw` as an affine image of the
product Gaussian and applies `multivariateGaussian_map_affine` + the ForMathlib Gaussian
convolution (`MultivariateGaussianConv`, reused). *Book vs Lean:* M1's moment-only
hypotheses have no Gaussianity — stronger than the books' statements.

**Bibliographic comments.** The marginal covariance `Z G Zᵀ + R` is the variance-components
decomposition of Henderson (1950) and Laird–Ware (1982).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.MixedEffects

open StatLean.StatisticalModels

variable {n p q : ℕ} (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))

instance (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure G] [IsProbabilityMeasure R] :
    IsProbabilityMeasure (lmmLaw D β G R) := by
  sorry

/-- **M1a, marginal mean without Gaussianity**: centered latent effects and noise give
`E Y = Xβ` (`LW82` Eq. (1.2), moment form). -/
theorem meanVec_lmmLaw (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure G]
    [IsProbabilityMeasure R]
    -- USER-INPUT: centered latent effects and noise, first moments; LW82 Eq. (1.1)
    (hG : meanVec G = 0) (hR : meanVec R = 0)
    (hG1 : Integrable id G) (hR1 : Integrable id R) :
    meanVec (lmmLaw D β G R) = Matrix.toEuclideanLin (𝕜 := ℝ) D.X β := by
  sorry

/-- **M1b, marginal covariance without Gaussianity**: `Cov Y = Z·Cov(b)·Zᵀ + Cov(ε)` —
the variance-components decomposition, for arbitrary latent laws (`LW82` Eq. (1.2), moment
form; `Hen50`). -/
theorem covMatrix_lmmLaw (G : Measure (EuclideanSpace ℝ (Fin q)))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure G]
    [IsProbabilityMeasure R]
    -- USER-INPUT: second moments of latent effects and noise; LW82 Eq. (1.1)
    (hG2 : MemLp id 2 G) (hR2 : MemLp id 2 R) :
    covMatrix (lmmLaw D β G R) = D.Z * covMatrix G * D.Zᵀ + covMatrix R := by
  sorry

/-- **M2, the Gaussian marginal** (`LW82` Eq. (1.2)): with Gaussian latent effects and
noise, `Y ∼ N(Xβ, Z Gm Zᵀ + Rm)`. -/
theorem lmmLaw_multivariateGaussian (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; LW82 Eq. (1.1)
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    lmmLaw D β (multivariateGaussian 0 Gm) (multivariateGaussian 0 Rm)
      = multivariateGaussian (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β)
          (D.Z * Gm * D.Zᵀ + Rm) := by
  sorry

/-- The marginal covariance is positive semidefinite (sanity corollary of M1b). -/
theorem posSemidef_variance_components (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; LW82 Eq. (1.1)
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    (D.Z * Gm * D.Zᵀ + Rm).PosSemidef := by
  sorry

end StatLean.StatisticalModels.MixedEffects
