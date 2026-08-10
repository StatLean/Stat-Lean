import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import StatLean.ComputationalStatistics.ForMathlib.PiMoments
import StatLean.ComputationalStatistics.Resampling.CategoricalCounts

/-!
# Finite-sample bootstrap identities

The exact (non-asymptotic) moment identities of Efron's nonparametric
bootstrap, conditionally on the data: a bootstrap sample is `n` i.i.d. draws
from the empirical measure `𝔽ₙ` (ECS ch. 4), and

* `bootstrap_linearStatistic_expectation` — `E*[(1/n)·Σⱼ g(Yⱼ*)] = (1/n)·Σᵢ g(xᵢ)`;
* `bootstrapMean_expectation` — `E*[X̄*] = x̄` (the mean case);
* `variance_id_empiricalMeasure` — `Var_{𝔽ₙ}(id) = (1/n)·Σᵢ (xᵢ − x̄)²`;
* `bootstrapMean_variance` — `Var*(X̄*) = (1/n²)·Σᵢ (xᵢ − x̄)²` (ECS §4.2);
* `bootstrapSqMean_expectation`, `bootstrapBiasCorrection_sqMean` — the ideal
  bootstrap bias correction (ECS §4.1, eqs. (4.3)–(4.4)) computed in closed
  form for the squared mean (ECS Exercise 4.1): `T₁ = x̄² − (1/n²)·Σᵢ(xᵢ−x̄)²`;
* `resampleLaw_eq_map_indexResampling` — resampling values = resampling
  indices uniformly;
* `bootstrapCounts_multinomial` — the Efron resampling counts are
  `Multinomial(n; 1/n, …, 1/n)` (ECS ch. 4, p. 84).

Everything here is *conditional on the data*: `x` is a parameter and the only
randomness is the resampling law `Measure.pi (fun _ : Fin n => empiricalMeasure x)`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 pp. 83–86: the ECDF as population, the
resampling vector and its multinomial law (p. 84), bias correction
(§4.1, eqs. (4.1)–(4.5)), variance estimation (§4.2, eqs. (4.6)–(4.7)).
(`ECS §4.1–4.2`.)

**Proof formalization notes.**

* The resampling law coincides with `StatLean.HypothesisTesting.bootstrapLaw`
  (concept layer of another area, hence not importable here); the asymptotic
  bootstrap theory lives there, the finite-sample identities live here, and
  the two files cross-reference in prose only.
* The identities are `ForMathlib/PiMoments.lean` at `P = empiricalMeasure x`
  plus `Core/EmpiricalMeasure.lean` sum conversions; no new probabilistic
  content, which is exactly the point — the empirical measure *is* a
  probability measure and the generic i.i.d. lemmas apply verbatim.
* "Ideal bootstrap" means the exact conditional expectation `E*`, not its
  Monte Carlo approximation by `m` resamples (ECS §4.2, eq. (4.7)); the
  Monte Carlo layer is `MonteCarlo/Estimation.lean` applied at
  `P = resampling law` and needs no new theorems.

**Bibliographic comments.** B. Efron, "Bootstrap methods: another look at the
jackknife," *Ann. Statist.* **7** (1979), 1–26 (the resampling vector is his
§2); Efron–Tibshirani, *An Introduction to the Bootstrap*, Chapman & Hall,
1993, ch. 10 (bias correction).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {n : ℕ} {x : Fin n → 𝓧} {g : 𝓧 → ℝ}

/-- **Bootstrap expectation of a linear statistic** (ECS ch. 4, p. 84): the
plug-in average of `g` over a bootstrap sample has conditional expectation the
sample average of `g`. -/
theorem bootstrap_linearStatistic_expectation [NeZero n]
    -- LEAN-ONLY: strong measurability, needed to integrate against Diracs
    (hg : StronglyMeasurable g) :
    ∫ y, mcEstimate g y ∂(Measure.pi fun _ : Fin n => empiricalMeasure x)
      = mcEstimate g x := by
  sorry

/-- **Plug-in variance of `g` under the empirical measure**:
`Var_{𝔽ₙ}(g) = (1/n)·Σᵢ (g(xᵢ) − ḡ)²` (the divide-by-`n` sample variance of
`g`-values). -/
theorem variance_empiricalMeasure [NeZero n]
    -- LEAN-ONLY: strong measurability, needed to integrate against Diracs
    (hg : StronglyMeasurable g) :
    variance g (empiricalMeasure x)
      = (n : ℝ)⁻¹ * ∑ i, (g (x i) - mcEstimate g x) ^ 2 := by
  sorry

/-- **Bootstrap variance of a linear statistic** (ECS §4.2): conditionally on
the data, `Var*((1/n)·Σⱼ g(Yⱼ*)) = (1/n²)·Σᵢ (g(xᵢ) − ḡ)²`. -/
theorem bootstrap_linearStatistic_variance [NeZero n]
    -- LEAN-ONLY: strong measurability, needed to integrate against Diracs
    (hg : StronglyMeasurable g) :
    variance (mcEstimate g) (Measure.pi fun _ : Fin n => empiricalMeasure x)
      = ((n : ℝ) ^ 2)⁻¹ * ∑ i, (g (x i) - mcEstimate g x) ^ 2 := by
  sorry

section RealData

variable {y : Fin n → ℝ}

/-- **The bootstrap sample mean is conditionally unbiased for the sample
mean** (ECS ch. 4): `E*[X̄*] = x̄`. -/
theorem bootstrapMean_expectation [NeZero n] :
    ∫ z, mcEstimate id z ∂(Measure.pi fun _ : Fin n => empiricalMeasure y)
      = mcEstimate id y := by
  sorry

/-- **Bootstrap variance of the sample mean** (ECS §4.2):
`Var*(X̄*) = (1/n²)·Σᵢ (yᵢ − ȳ)²`. -/
theorem bootstrapMean_variance [NeZero n] :
    variance (mcEstimate id) (Measure.pi fun _ : Fin n => empiricalMeasure y)
      = ((n : ℝ) ^ 2)⁻¹ * ∑ i, (y i - mcEstimate id y) ^ 2 := by
  sorry

/-- **Ideal bootstrap expectation of the squared mean** (ECS §4.1 and
Exercise 4.1): `E*[(X̄*)²] = x̄² + (1/n²)·Σᵢ (yᵢ − ȳ)²`. -/
theorem bootstrapSqMean_expectation [NeZero n] :
    ∫ z, (mcEstimate id z) ^ 2
        ∂(Measure.pi fun _ : Fin n => empiricalMeasure y)
      = (mcEstimate id y) ^ 2
          + ((n : ℝ) ^ 2)⁻¹ * ∑ i, (y i - mcEstimate id y) ^ 2 := by
  sorry

/-- **The ideal bootstrap bias-corrected squared mean** (ECS §4.1,
eq. (4.4)): `T₁ = 2·T(𝔽ₙ) − E*[T(𝔽ₙ⁽¹⁾)]` evaluates, for `T` the squared
mean, to `x̄² − (1/n²)·Σᵢ (yᵢ − ȳ)²`. -/
theorem bootstrapBiasCorrection_sqMean [NeZero n] :
    2 * (mcEstimate id y) ^ 2
        - ∫ z, (mcEstimate id z) ^ 2
            ∂(Measure.pi fun _ : Fin n => empiricalMeasure y)
      = (mcEstimate id y) ^ 2
          - ((n : ℝ) ^ 2)⁻¹ * ∑ i, (y i - mcEstimate id y) ^ 2 := by
  sorry

end RealData

/-- **Value resampling is uniform index resampling** (ECS §2.5): the bootstrap
resampling law is the pushforward of uniform i.i.d. index draws through the
data. -/
theorem resampleLaw_eq_map_indexResampling [NeZero n] :
    (Measure.pi fun _ : Fin n => empiricalMeasure x)
      = (Measure.pi fun _ : Fin n => categorical fun _ : Fin n => (n : ℝ)⁻¹).map
          (fun a => x ∘ a) := by
  sorry

/-- **The Efron resampling counts are multinomial** (ECS ch. 4, p. 84): the
counts of uniform i.i.d. index draws have the multinomial law
`ℳ_n(n; 1/n, …, 1/n)`. -/
theorem bootstrapCounts_multinomial [NeZero n] :
    ((Measure.pi fun _ : Fin n => categorical fun _ : Fin n => (n : ℝ)⁻¹).map
        categoricalCounts)
      = StatLean.Bayesian.multinomialKernel n n (fun _ => (n : ℝ)⁻¹) := by
  sorry

end StatLean.ComputationalStatistics
