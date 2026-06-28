import StatLean.Minimaxity.Fano.LocalPacking
import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
import StatLean.Minimaxity.ForMathlib.Packing.SparsePacking
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Example: minimax risk for sparse linear regression (Wainwright Example 15.16)

For the Gaussian linear model `y = Xθ* + w`, `w ∼ 𝒩(0, σ²Iₙ)`, with the regression vector `θ*` known
a priori to be `s`-sparse, the minimax risk over the sparse Euclidean unit ball
`S_d(s) = B₀(s) ∩ B₂(1) = {θ : ‖θ‖₀ ≤ s, ‖θ‖₂ ≤ 1}` (Eq. 15.40) in squared Euclidean error is lower
bounded as
```
M(S_d(s); ‖·‖₂) ≳ (σ²/γ₂ₛ²) · s·log((d−s)/s) / n            (Example 15.16),
```
where `γ₂ₛ = max_{|T|=2s} σ_max(X_T)/√n` is the `2s`-restricted maximum singular value of the design.

The proof is the local-packing / Fano method (as in Example 15.14, `LinearRegression.lean`) applied to a
`1/2`-packing of `S_d(s)` (`exists_sparse_packing`, Exercise 5.8) rescaled into the ball: the pairwise
KL divergences are controlled by `γ₂ₛ` acting on the (at most `2s`-sparse) packing differences, and the
equal-covariance multivariate Gaussian KL `klDiv_multivariateGaussian_smul_one` evaluates them.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.16.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- The `s`-sparse Euclidean unit ball `S_d(s) = B₀(s) ∩ B₂(1) = {θ : ‖θ‖₀ ≤ s, ‖θ‖₂ ≤ 1}`
(Wainwright Eq. 15.40), the parameter set over which the sparse-regression minimax risk is taken. A
vector is `s`-sparse when at most `s` coordinates are nonzero. -/
def SparseBall (d s : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {θ | (Finset.univ.filter fun i => θ i ≠ 0).card ≤ s ∧ ‖θ‖ ≤ 1}

/-- **Crux: local packing data for sparse linear regression.** A `1/2`-packing of the `s`-sparse unit
ball (Wainwright Example 5.8, `exists_sparse_packing`) of log-cardinality `≥ (s/2)log((d−s)/s) − s·log2`,
rescaled into `S_d(s)`, gives a `δ`-separated family (in `‖·‖₂`) whose pairwise KL divergences satisfy
the (15.35a) bound — via the `2s`-restricted singular value `γ` acting on the `≤ 2s`-sparse differences
and the equal-covariance multivariate Gaussian KL `klDiv_multivariateGaussian_smul_one` — and whose
cardinality satisfies (15.35b).

The separation/rate constant is loosened (CLAUDE.md §1) to fit the `(s/2)log((d−s)/s) − s·log2`
Gilbert–Varshamov sparse-packing brick. -/
private lemma sparse_linreg_local_packing_data {n d s : ℕ} (hn : 1 ≤ n) (hs : 0 < s) (hds : 8 * s ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ≥0) (hγ : γ ≠ 0)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    -- USER-INPUT: `γ` is the `2s`-restricted singular value `γ₂ₛ = max_{|T|=2s} σ_max(X_T)/√n`; Wainwright Ex 15.16.
    (hγbd : ∀ θ : EuclideanSpace ℝ (Fin d),
        (Finset.univ.filter fun i => θ i ≠ 0).card ≤ 2 * s → ‖A θ‖ ≤ Real.sqrt (n : ℝ) * (γ : ℝ) * ‖θ‖)
    (P : Kernel (SparseBall d s) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.16.
    (hP : ∀ θ, P θ = multivariateGaussian (A (θ : EuclideanSpace ℝ (Fin d)))
            ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ (M : ℕ) (_ : NeZero M) (θfam : Fin M → SparseBall d s) (hθ : Measurable θfam) (c : ℝ),
      IsSeparatedFamily Subtype.val θfam
          (ENNReal.ofReal (Real.sqrt ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s)
            / (10240 * (γ : ℝ) ^ 2 * n)))) ∧
      (∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) *
            (ENNReal.ofReal (Real.sqrt ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s)
              / (10240 * (γ : ℝ) ^ 2 * n)))).toReal ^ 2)) ∧
      2 * (c ^ 2 * (n : ℝ) *
          (ENNReal.ofReal (Real.sqrt ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s)
            / (10240 * (γ : ℝ) ^ 2 * n)))).toReal ^ 2 + Real.log 2)
        ≤ Real.log (M : ℝ) := by
  sorry

/-- **Minimax risk for sparse linear regression** (Wainwright Example 15.16): for the fixed-design
Gaussian model with design map `A : ℝᵈ → ℝⁿ`, noise variance `v`, and `2s`-restricted singular value
`γ`, the minimax risk over the `s`-sparse unit ball `S_d(s)` in squared Euclidean error is at least
`c·(v/γ²)·s·log((d−s)/s)/n`, witnessed by a `1/2`-packing of `S_d(s)` rescaled into the ball.

The leading constant is loosened from the book's (CLAUDE.md §1), forced by the
`(s/2)log((d−s)/s) − s·log2` sparse-packing brick; the result holds for `8s ≤ d` (so the cardinality
slack is absorbed).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3, Example 15.16. -/
theorem sparse_linear_regression_minimax_rate {n d s : ℕ} (hn : 1 ≤ n) (hs : 0 < s) (hds : 8 * s ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ≥0) (hγ : γ ≠ 0)
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    -- USER-INPUT: `γ` is the `2s`-restricted singular value `γ₂ₛ = max_{|T|=2s} σ_max(X_T)/√n`; Wainwright Ex 15.16.
    (hγbd : ∀ θ : EuclideanSpace ℝ (Fin d),
        (Finset.univ.filter fun i => θ i ≠ 0).card ≤ 2 * s → ‖A θ‖ ≤ Real.sqrt (n : ℝ) * (γ : ℝ) * ‖θ‖)
    (P : Kernel (SparseBall d s) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    -- USER-INPUT: `y ∼ 𝒩(Aθ, v Iₙ)` (fixed-design Gaussian model); Wainwright §15.3.3, Ex 15.16.
    (hP : ∀ θ, P θ = multivariateGaussian (A (θ : EuclideanSpace ℝ (Fin d)))
            ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    ENNReal.ofReal ((v : ℝ) * (s : ℝ) * Real.log (((d : ℝ) - s) / s) / (20480 * (γ : ℝ) ^ 2 * n))
      ≤ minimaxRiskDist (· ^ 2) Subtype.val P := by
  obtain ⟨M, hMne, θfam, hθ, c, hsep, h35a, h35b⟩ :=
    sparse_linreg_local_packing_data hn hs hds v hv γ hγ A hγbd P hP
  sorry

end StatLean.Minimaxity
