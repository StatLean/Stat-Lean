import StatLean.ComputationalStatistics.Resampling.CategoricalCounts
import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import Mathlib.Probability.Variance
import Mathlib.Probability.Moments.Covariance

/-!
# Moments of multinomial category counts

First and second moments of the count vector `V_j = #{i | Aᵢ = j}` of `n`
i.i.d. `categorical q` draws:

* `integral_categoricalCount` — `E[V_j] = n·q_j`;
* `variance_categoricalCount` — `Var(V_j) = n·q_j·(1 − q_j)`;
* `covariance_categoricalCount` — `Cov(V_j, V_k) = −n·q_j·q_k` for `j ≠ k`.

Noted absent from the repo by the 2026-08-10 survey; they are the moment
inputs for resampling-scheme comparisons (e.g. multinomial vs. residual
resampling variances) in later rounds.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 p. 84 (the multinomial resampling vector);
moments are the classical multinomial moments.  (`ECS ch. 4`.)

**Proof formalization notes.**

* Each count is a sum of indicator functions of the independent coordinates,
  so the proofs are `iIndepFun_pi` + Bernoulli-moment algebra; no multinomial
  pmf manipulation is needed.
* Counts are `ℕ`-valued; the statements coerce to `ℝ`.

**Bibliographic comments.** Classical; see also Johnson–Kotz–Balakrishnan,
*Discrete Multivariate Distributions*, Wiley, 1997, ch. 35.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {m n : ℕ} {q : Fin m → ℝ}

/-- **Multinomial count mean**: `E[V_j] = n·q_j`. -/
theorem integral_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) (j : Fin m) :
    ∫ a, (categoricalCounts a j : ℝ) ∂(Measure.pi fun _ : Fin n => categorical q)
      = n * q j := by
  sorry

/-- **Multinomial count variance**: `Var(V_j) = n·q_j·(1 − q_j)`. -/
theorem variance_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) (j : Fin m) :
    variance (fun a => (categoricalCounts a j : ℝ))
        (Measure.pi fun _ : Fin n => categorical q)
      = n * q j * (1 - q j) := by
  sorry

/-- **Multinomial count covariance**: `Cov(V_j, V_k) = −n·q_j·q_k` for
distinct categories. -/
theorem covariance_categoricalCount
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) {j k : Fin m}
    -- USER-INPUT: distinct categories; ECS ch. 4
    (hjk : j ≠ k) :
    covariance (fun a => (categoricalCounts a j : ℝ))
        (fun a => (categoricalCounts a k : ℝ))
        (Measure.pi fun _ : Fin n => categorical q)
      = -(n * q j * q k) := by
  sorry

end StatLean.ComputationalStatistics
