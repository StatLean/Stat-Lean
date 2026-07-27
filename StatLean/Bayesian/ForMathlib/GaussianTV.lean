import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
import StatLean.Minimaxity.ForMathlib.PinskerInequality
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity

/-!
# Total-variation bound between equal-covariance Gaussians

For a positive definite covariance `S`, the Kullback–Leibler divergence between two
Gaussians with the same covariance and different means is the Mahalanobis half-square,
and Pinsker's inequality turns it into a mean-Lipschitz total-variation bound:

* `klDiv_multivariateGaussian_same_cov` —
  `KL(N(a,S) ‖ N(b,S)) = ⟪a − b, S⁻¹(a − b)⟫ / 2`;
* `tvDist_multivariateGaussian_le` —
  `tvDist (N(a,S)) (N(b,S)) ≤ (⟪a − b, S⁻¹(a − b)⟫ / 4) ^ (1/2)`.

This is the brick behind the efficient-centering corollary of the Bernstein–von Mises
theorem (vdV Chapter 10, remark after Lemma 10.3, p. 144): replacing the centering
`Δ_{n,θ₀}` by any asymptotically equivalent sequence `√n(θ̂_n − θ₀)` changes the Gaussian
approximation by at most a multiple of the difference of the centers.

**Proof formalization notes.** Whitening: push both Gaussians through
`toEuclideanCLM (CFC.sqrt S⁻¹)` (KL is invariant under measurable-equivalence pushforward,
`klDiv_map_eq_of_comp` in `GaussianKLMulti`), reducing to the scalar-covariance case
`klDiv_multivariateGaussian_smul_one` at `c = 1`. Pinsker is
`StatLean.Minimaxity.pinsker_tv_le_kl : tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1/2)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped RealInnerProductSpace ENNReal
open StatLean.Minimaxity

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Equal-covariance Gaussian KL divergence** (Mahalanobis half-square): for positive
definite `S`,
`KL(N(a,S) ‖ N(b,S)) = ofReal (⟪a − b, S⁻¹ (a − b)⟫ / 2)`. -/
theorem klDiv_multivariateGaussian_same_cov
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (KL between singular Gaussians is degenerate)
    (hS : S.PosDef) (a b : EuclideanSpace ℝ ι) :
    klDiv (multivariateGaussian a S) (multivariateGaussian b S)
      = ENNReal.ofReal (⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ / 2) := by
  sorry

/-- **Mean-shift total-variation bound for equal-covariance Gaussians** (Pinsker route):
`tvDist (N(a,S)) (N(b,S)) ≤ (⟪a − b, S⁻¹(a − b)⟫ / 4) ^ (1/2)`. In particular the TV
distance tends to `0` whenever `a − b → 0`. -/
theorem tvDist_multivariateGaussian_le
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (feeds the KL identity above)
    (hS : S.PosDef) (a b : EuclideanSpace ℝ ι) :
    tvDist (multivariateGaussian a S) (multivariateGaussian b S)
      ≤ (ENNReal.ofReal (⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ / 4))
          ^ (1 / 2 : ℝ) := by
  sorry

end StatLean.Bayesian
