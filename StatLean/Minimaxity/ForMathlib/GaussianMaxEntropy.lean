import StatLean.Minimaxity.Fano.MutualInformation
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Gaussian maximum-entropy mutual-information bound — Lemma 15.17 (Wainwright §15.3.4)

When the observation conditioned on the index is Gaussian, the mutual information admits a
log-determinant bound coming from the maximum-entropy property of the multivariate Gaussian:
```
I(Z; J) ≤ ½ ( log det cov(Z) − (1/M) Σⱼ log det Σʲ )      (Lemma 15.17, Eq. (15.42)),
```
where `Σʲ = cov(Z | J = j)` and `cov(Z)` is the covariance of the mixture. This refines the
convexity bound (Eq. (15.34)) and is the key tool for the PCA lower bound (Example 15.19).

⚠ **Research-grade (◆◆).** The proof rests on the Gaussian maximum-entropy theorem (Exercise 15.14)
and concavity of `log det`. Time-boxed; if it resists, escalate (named-lemma debt) per CLAUDE.md §2.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Lemma 15.17.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Gaussian maximum-entropy mutual-information bound** (Wainwright Lemma 15.17, Eq. (15.42)):
if `Z | J = j ∼ 𝒩(0, Σʲ)`, then `I(Z; J) ≤ ½(log det cov(Z) − (1/M) Σⱼ log det Σʲ)`, where
`cov(Z) = (1/M) Σⱼ Σʲ` is the covariance of the zero-mean Gaussian mixture.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Lemma 15.17. -/
theorem gaussian_mutualInfo_le {M d : ℕ} [NeZero M]
    (Q : Kernel (Fin M) (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel Q]
    (S : Fin M → Matrix (Fin d) (Fin d) ℝ) (covZ : Matrix (Fin d) (Fin d) ℝ)
    -- USER-INPUT: `Z | J = j ∼ 𝒩(0, Σʲ)`; Wainwright §15.3.4, Lemma 15.17.
    (hQ : ∀ j, Q j = multivariateGaussian 0 (S j))
    -- USER-INPUT: `cov(Z) = (1/M) Σⱼ Σʲ` (mixture covariance, zero means); Wainwright §15.3.4.
    (hcov : covZ = (M : ℝ)⁻¹ • ∑ j, S j) :
    mutualInformation Q
      ≤ ENNReal.ofReal
          (2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det)) := by
  sorry

end StatLean.Minimaxity
