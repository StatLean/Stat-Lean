import StatLean.Bayesian.Conjugacy.NormalNormal

/-!
# Linear-shrinkage and James–Stein risk

The optimality side of the normal hierarchy. The linear-shrinkage estimator `c·X` has frequentist
risk `∑ᵢ((1−c)²θᵢ² + c²σ²)` and Bayes risk (under `θ ∼ N(0, τ²)`) `p·((1−c)²τ² + c²σ²)`, minimized
at the oracle weight `c* = τ²/(σ²+τ²)` — the empirical-Bayes shrinkage factor whose Bayes risk
`p·σ²τ²/(σ²+τ²)` is proved in `StatLean.MultipleTesting.empiricalBayes_risk` (Candès, STAT 300C;
cited, not imported — the DAG forbids importing that area's concept files). The James–Stein
estimator `(1 − (p−2)σ²/‖X‖²)·X` strictly dominates the MLE `X` in dimension `p ≥ 3` (the Stein
effect).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Note 2.8.2 (the Stein effect), p. 96; Example 4.2.3 (truncated
James–Stein); §10.5 (empirical-Bayes justifications of the Stein effect), p. 484.

**Proof formalization notes.** The linear-shrinkage risk is a coordinatewise Gaussian
bias²+variance computation (`integral_id_gaussianReal`, `variance_id_gaussianReal` per coordinate,
`Measure.pi` Fubini); the Bayes risk integrates it against `N(0,τ²)`; the argmin is a real
quadratic-in-`c` minimization (`nlinarith`/completing the square). The James–Stein risk identity
uses the Gaussian integration-by-parts (Stein's lemma) built from
`ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal` and the pinned interval/improper IBP; the
`p ≥ 3` hypothesis is what makes `E‖X‖⁻²` finite. Dominance is the risk identity plus positivity.

**Bibliographic comments.** The inadmissibility of the sample mean in dimension `≥ 3` is C. Stein
("Inadmissibility of the usual estimator for the mean of a multivariate normal distribution,"
*Proc. Third Berkeley Symp.* 1 (1956), 197–206); the explicit dominating estimator and its risk are
W. James and C. Stein ("Estimation with quadratic loss," *Proc. Fourth Berkeley Symp.* 1 (1961),
361–379). The empirical-Bayes reading — shrinkage toward a data-estimated prior mean — is B. Efron
and C. Morris (1973) and underlies Robert §10.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.Bayesian

/-- The **linear-shrinkage estimator** `x ↦ c·x` (shrinkage toward the origin). -/
noncomputable def linearShrinkage (c : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ := fun i => c * x i

/-- The **James–Stein estimator** `x ↦ (1 − (p−2)σ²/‖x‖²)·x` (James and Stein 1961). -/
noncomputable def jamesSteinEstimator (σ2 : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - ((p : ℝ) - 2) * σ2 / (∑ j, (x j) ^ 2)) * x i

/-- **Frequentist risk of linear shrinkage** (3D.1): `R(θ, c·X) = ∑ᵢ((1−c)²θᵢ² + c²σ²)`. -/
theorem normalMeans_linearShrinkage_risk (c : ℝ) {p : ℕ} (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = ∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)) := by
  sorry

/-- **Bayes risk of linear shrinkage** (3D.2) under `θ ∼ N(0, τ²)`: `p·((1−c)²τ² + c²σ²)`. The
minimized value `p·σ²τ²/(σ²+τ²)` is `StatLean.MultipleTesting.empiricalBayes_risk`. -/
theorem normalMeans_linearShrinkage_bayesRisk (c : ℝ) (p : ℕ) (τ2 σ2 : ℝ≥0) :
    (∫ θ, (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
      = (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  sorry

/-- **The oracle weight minimizes the Bayes risk** (3D.2): `c* = τ²/(σ²+τ²)` is the argmin. -/
theorem normalMeans_linearShrinkage_bayesRisk_argmin (p : ℕ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate variances; Robert §10.4.2
    (hσ : σ2 ≠ 0) (hτ : τ2 ≠ 0) (c : ℝ) :
    (p : ℝ) * ((1 - (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (τ2 : ℝ)
        + ((τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (σ2 : ℝ))
      ≤ (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  sorry

/-- **James–Stein risk identity** (3D.4, stretch): the risk of the James–Stein estimator falls
below the MLE risk `p·σ²` by `(p−2)²σ⁴·E‖X‖⁻²` (Stein's lemma; James–Stein 1961). -/
theorem jamesStein_risk_difference {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = (p : ℝ) * (σ2 : ℝ) - ((p : ℝ) - 2) ^ 2 * (σ2 : ℝ) ^ 2
          * (∫ x, 1 / (∑ i, (x i) ^ 2) ∂(Measure.pi fun i => gaussianReal (θ i) σ2)) := by
  sorry

/-- **James–Stein dominates the MLE** (3D.4, stretch): in dimension `p ≥ 3` the James–Stein risk is
strictly below the MLE risk `p·σ²` for every `θ` (the Stein effect). -/
theorem jamesStein_dominates_mle {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      < (p : ℝ) * (σ2 : ℝ) := by
  sorry

end StatLean.Bayesian
