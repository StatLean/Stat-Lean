import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

/-!
# Gaussian shift, inner-projection, and tail bricks

Mathlib-level facts about the standard Gaussian on `EuclideanSpace ℝ ι` and its
mean-shifts `N(θ, I) = stdGaussian.map (· + θ)`, packaged for the Dirichlet–Laplace
posterior-contraction proof.

* `stdGaussian_map_add_add` — shifting by `a` then by `b` equals shifting by `a + b`.
* `stdGaussianShift_withDensity` — the Gaussian likelihood ratio (Girsanov/Esscher):
  `N(θ, I) = N(θ₀, I).withDensity exp(⟪θ−θ₀, y−θ₀⟫ − ‖θ−θ₀‖²/2)`.
* `stdGaussian_map_inner` — a linear form `⟪c, ·⟫` pushes the standard Gaussian to
  the one-dimensional Gaussian `N(0, ‖c‖²)`.
* `gaussianReal_measure_ge_le` / `stdGaussianShift_inner_ge_le` — the sub-Gaussian
  upper tail `P(X ≥ t) ≤ exp(−t²/2v)`, in the one-dimensional form and in its
  shifted inner-projection form.

**Reference.** Mathlib-level bricks (no book statement of their own) consumed by the
Dirichlet–Laplace posterior-contraction proof (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398;
tag `BPPD §X.Y`): they supply the Gaussian shift/tail machinery for the midpoint
tests and the denominator lower bound (BPPD §6).

**Proof formalization notes.** `stdGaussianShift_withDensity` re-bases the existing
`ProbabilityTheory.stdGaussian_withDensity_exp_shift` (Girsanov at `a = θ − θ₀`)
through `stdGaussian_map_add_add`; `stdGaussian_map_inner` specializes
`ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal` at the identity
covariance; the two tail bounds transport the event through the shift and the inner
projection and finish with Mathlib's one-dimensional Gaussian sub-Gaussian tail
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`.

**Bibliographic comments.** The exponential-tilt (Esscher/Girsanov) shift of a
Gaussian and its sub-Gaussian upper tail are classical (Esscher 1932; Cramér 1938).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Two mean-shifts compose.** Shifting the standard Gaussian by `a` and then by
`b` is the same as shifting it by `a + b`. -/
theorem stdGaussian_map_add_add (a b : EuclideanSpace ℝ ι) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (· + a)).map (· + b)
      = (stdGaussian (EuclideanSpace ℝ ι)).map (· + (a + b)) := by
  sorry

/-- **Gaussian likelihood ratio (Girsanov / Esscher).** The mean-shift `N(θ, I)` is
`N(θ₀, I)` re-weighted by the density `exp(⟪θ − θ₀, y − θ₀⟫ − ‖θ − θ₀‖² / 2)` — i.e.
the pointwise Radon–Nikodym derivative `dN(θ, I)/dN(θ₀, I)`. This is the DL posterior
integrand (`dlLR θ₀ θ`), stated here density-side without referencing the concept
layer. -/
theorem stdGaussianShift_withDensity (θ₀ θ : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (· + θ)
      = ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ₀)).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (⟪θ - θ₀, y - θ₀⟫ - ‖θ - θ₀‖ ^ 2 / 2))) := by
  sorry

/-- **A linear form pushes the standard Gaussian to a one-dimensional Gaussian.**
For `y ∼ stdGaussian` on `EuclideanSpace ℝ ι`, the scalar `⟪c, y⟫` is `N(0, ‖c‖²)`. -/
theorem stdGaussian_map_inner (c : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => ⟪c, y⟫)
      = gaussianReal 0 (‖c‖₊ ^ 2) := by
  sorry

/-- **Sub-Gaussian upper tail of a centered one-dimensional Gaussian.**
For `X ∼ N(0, v)` and a nonnegative threshold `t`,
`P(X ≥ t) ≤ exp(−t² / (2v))`. (Holds degenerately at `v = 0`, where the right side
is `1`.) -/
theorem gaussianReal_measure_ge_le (v : ℝ≥0) (t : ℝ)
    -- LEAN-ONLY: tail domain requires a nonnegative threshold; genuine caller input
    (ht : 0 ≤ t) :
    gaussianReal 0 v {x : ℝ | t ≤ x}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (v : ℝ)))) := by
  sorry

/-- **Shifted inner-projection tail.** For `y ∼ N(θ', I)` the linear form
`⟪c, y − θ'⟫` is `N(0, ‖c‖²)`, so its upper tail is `exp(−t² / (2‖c‖²))` for
`t ≥ 0`. This is the error bound of the DL midpoint tests (BPPD §6). -/
theorem stdGaussianShift_inner_ge_le (θ' c : EuclideanSpace ℝ ι) (t : ℝ)
    -- LEAN-ONLY: tail domain requires a nonnegative threshold; genuine caller input
    (ht : 0 ≤ t) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (· + θ'))
        {y : EuclideanSpace ℝ ι | t ≤ ⟪c, y - θ'⟫}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * ‖c‖ ^ 2))) := by
  sorry

end StatLean.Bayesian
