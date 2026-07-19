import StatLean.HypothesisTesting.Bootstrap.Defs
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Bootstrap consistency: the sequence-class criterion

The bootstrap replaces the unknown law `P` by an estimate `Phat n` (typically the empirical
measure of the sample) inside the sampling distribution `J n` of a root. Consistency asks
that this substitution be asymptotically harmless. Following the sequence-class approach,
smoothness of `J` in its measure argument is expressed by a set of sequences `C_P` of laws:
along **every** sequence in `C_P` the sampling distribution functions converge to one and the
same continuous limit `Jlim`. The only stochastic ingredient is then that the estimated
sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`.

This file contains:

* `IsCDF` — the distribution-function predicate every `J n Q` is assumed to satisfy;
* `StrictIncAt` — strict increase of a distribution function at a point;
* `normalCDF`, `stdNormalCDF`, `stdNormalQuantile` — the Gaussian limit-law vocabulary used
  throughout the bootstrap cluster;
* `tendsto_supCDFDist_bootstrap` — almost sure uniform closeness of the bootstrap sampling
  distribution to the true one;
* `tendsto_bootstrapQuantile` — almost sure convergence of the bootstrap quantile;
* `tendsto_bootstrapCoverage` — asymptotic coverage of the bootstrap confidence set;
* `tendstoInMeasure_rowMean_triangular` — the triangular-array weak law used by the
  nonparametric-mean applications downstream.

**Reference.** Classical bootstrap consistency theory; original sources in the bibliographic
comments below.

**Designed deviation (metric-free formulation).** The reference tradition often describes
smoothness of `J` in `P` through a metric `d` on the space of laws (`d(P_n, P) → 0` implies
`J_n(P_n) ⇒ J(P)`). We deliberately keep the **sequence-class** form: `C_P` is an abstract set
of sequences, supplied as data together with its defining convergence property. This is the
weaker and more general of the two devices (any metric criterion produces such a class), it
avoids committing the library to one metric on measures, and it removes every measurability
requirement in the measure argument of `J`.

**Proof formalization notes.**
* The sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` is theorem-level data. Its distribution
  function properties enter as the hypothesis `∀ n Q, IsCDF (J n Q)`; no measurability of
  `Q ↦ J n Q x` is ever assumed, which is what makes the almost-sure statements meaningful
  for a random `Phat n ω`.
* The uniform conclusion is the Polya step: pointwise convergence of distribution functions to
  a **continuous** limit upgrades to convergence in sup-distance. That upgrade is the sibling
  `PolyaUniformCDF` brick of this area (uniform convergence of monotone functions to a
  continuous limit); it is applied here to each fixed sequence in `C_P` and then transported
  to the random sequence on the almost sure event.
* The confidence set is the one attached to the root: `θ(P)` is covered exactly when the root
  evaluated at the true parameter does not exceed the estimated `1 − α` quantile. The coverage
  statement is phrased directly in that form, so no separate parameter-set machinery is needed.
* `IsCDF` deliberately omits `[0,1]`-valuedness: monotonicity together with the two tail limits
  forces it, so recording it as a field would be redundant.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Its first consistency theory is due to
P. J. Bickel and D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.*
**9** (1981), 1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap,"
*Ann. Statist.* **9** (1981), 1187–1195). The formulation of consistency through classes of
converging sequences of laws follows R. Beran ("Bootstrap methods in statistics," *Jahresber.
Deutsch. Math.-Verein.* **86** (1984), 14–30) and D. N. Politis, J. P. Romano and M. Wolf,
*Subsampling*, Springer, 1999.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StatLean.HypothesisTesting

variable {𝓧 Ω : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Ω]

/-! ## Distribution-function vocabulary -/

/-- A real function is a **distribution function**: nondecreasing, right-continuous, with
limit `0` at `−∞` and limit `1` at `+∞`. (`[0,1]`-valuedness is a consequence, not a field.) -/
structure IsCDF (F : ℝ → ℝ) : Prop where
  /-- Constitutive: a distribution function is nondecreasing. -/
  mono : Monotone F
  /-- Constitutive: a distribution function is right-continuous. -/
  right_continuous : ∀ x : ℝ, ContinuousWithinAt F (Set.Ici x) x
  /-- Constitutive: a distribution function vanishes at `−∞`. -/
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  /-- Constitutive: a distribution function tends to `1` at `+∞`. -/
  tendsto_atTop : Tendsto F atTop (𝓝 1)

/-- `F` is **strictly increasing at** `x₀`: strictly smaller to the left, strictly larger to
the right. This is the exact regularity that makes the `x₀`-level quantile unique, and it is
what quantile convergence needs on top of continuity of the limit law. -/
def StrictIncAt (F : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (∀ y, y < x₀ → F y < F x₀) ∧ (∀ z, x₀ < z → F x₀ < F z)

/-- The **normal distribution function** with mean `m` and variance `v`. -/
noncomputable def normalCDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianReal m v (Set.Iic x)).toReal

/-- The **standard normal distribution function** `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := normalCDF 0 1 x

/-- The **standard normal quantile** `z_p = Φ⁻¹(p)`, via the generalized inverse. -/
noncomputable def stdNormalQuantile (p : ℝ) : ℝ := cdfPseudoInverse stdNormalCDF p

/-! ## Consistency of the bootstrap sampling distribution -/

section Consistency

variable {ℙ : Measure Ω} {P : Measure 𝓧} {J : ℕ → Measure 𝓧 → ℝ → ℝ}
  {C_P : Set (ℕ → Measure 𝓧)} {Jlim : ℝ → ℝ} {Phat : ℕ → Ω → Measure 𝓧} {R : ℕ → Ω → ℝ} {α : ℝ}

/-- **Bootstrap consistency, uniform (sup-distance) form.**

If the sampling distribution functions converge, along every sequence of the class `C_P`, to a
common continuous limit `Jlim`, if the constant sequence at the true law `P` belongs to `C_P`,
and if the estimated sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`, then the
bootstrap sampling distribution is uniformly close to the true one, almost surely:
`sup_x |J n P x − J n (Phat n ω) x| → 0`. -/
theorem tendsto_supCDFDist_bootstrap
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class; this
    -- is what ties the class to the law actually generating the sample
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: along every sequence of the class the sampling distribution functions
    -- converge pointwise to the common limit
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: the common limit law is continuous; this is the exact continuity requirement
    -- that turns pointwise convergence into uniform convergence
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: the estimated sequence of laws belongs to the class almost surely; the only
    -- stochastic ingredient of the criterion
    (hPhat_mem : ∀ᵐ ω ∂ℙ, (fun n => Phat n ω) ∈ C_P) :
    ∀ᵐ ω ∂ℙ, Tendsto (fun n => supCDFDist (J n P) (J n (Phat n ω))) atTop (𝓝 0) := by
  sorry

/-- **Bootstrap quantile consistency.**

Under the hypotheses of `tendsto_supCDFDist_bootstrap`, if the limit law is in addition
strictly increasing at its `1 − α` quantile, then the estimated `1 − α` quantile converges
almost surely to the quantile of the limit law. -/
theorem tendsto_bootstrapQuantile
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂ℙ, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the limit law is strictly increasing at the quantile being estimated; without
    -- it the quantile is not uniquely determined and need not converge
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α))) :
    ∀ᵐ ω ∂ℙ, Tendsto (fun n => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) atTop
      (𝓝 (cdfPseudoInverse Jlim (1 - α))) := by
  sorry

/-- **Asymptotic coverage of the bootstrap confidence set.**

The bootstrap confidence set for the parameter of interest consists of those parameter values
whose root does not exceed the estimated `1 − α` quantile; the true parameter is covered
exactly when `R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 − α)`, where `R n` is the root
evaluated at the true parameter. Its coverage probability converges to the nominal level. -/
theorem tendsto_bootstrapCoverage [IsProbabilityMeasure ℙ]
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂ℙ, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: strict increase of the limit law at the estimated quantile
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α)))
    -- USER-INPUT: at the data-generating law the field `J` is the exact sampling distribution
    -- function of the root; this is what makes `J` the object being bootstrapped
    (hJP : ∀ (n : ℕ) (x : ℝ), J n P x = (ℙ {ω | R n ω ≤ x}).toReal)
    -- LEAN-ONLY: the root is measurable; needed for the coverage event to carry its measure
    (hRmeas : ∀ n, Measurable (R n))
    -- LEAN-ONLY: the estimated critical value is measurable in the sample; no measurability in
    -- the measure argument of `J` is assumed, so this is recorded directly
    (hqmeas : ∀ n, Measurable fun ω => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) :
    Tendsto (fun n => (ℙ {ω | R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 - α)}).toReal)
      atTop (𝓝 (1 - α)) := by
  sorry

end Consistency

/-! ## A weak law of large numbers for triangular arrays -/

/-- **Weak law of large numbers for a triangular array.**

Let `Y n 0, …, Y n (n−1)` be a triangular array of independent random variables, the entries of
row `n` all having distribution function `G n`. If `G n` converges in distribution to the law
`ν` (with distribution function `Glim`) and the first absolute moments converge to the — finite
— first absolute moment of `ν`, then the row averages converge in probability to the mean of
`ν`. This is the moment-convergence tool behind the nonparametric-mean applications. -/
theorem tendstoInMeasure_rowMean_triangular {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {Y : ℕ → ℕ → Ω → ℝ} {G : ℕ → ℝ → ℝ} {Glim : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- LEAN-ONLY: the array entries are measurable; the distribution-function hypotheses below
    -- would otherwise refer to outer measures of non-measurable sets
    (hYmeas : ∀ n i, Measurable (Y n i))
    -- USER-INPUT: the entries within each row are independent
    (hindep : ∀ n : ℕ, iIndepFun (fun i : Fin n => Y n i) ℙ)
    -- USER-INPUT: the entries of row `n` all have distribution function `G n`
    (hGrow : ∀ n : ℕ, ∀ i < n, ∀ x : ℝ, G n x = (ℙ {ω | Y n i ω ≤ x}).toReal)
    -- USER-INPUT: `Glim` is the distribution function of the limit law `ν`
    (hGlim : ∀ x : ℝ, Glim x = (ν (Set.Iic x)).toReal)
    -- USER-INPUT: the row laws converge in distribution to `ν`, i.e. their distribution
    -- functions converge at every continuity point of the limit
    (hGconv : ∀ x : ℝ, ContinuousAt Glim x → Tendsto (fun n => G n x) atTop (𝓝 (Glim x)))
    -- USER-INPUT: the limit law has a finite first absolute moment
    (hint : Integrable (fun t : ℝ => t) ν)
    -- USER-INPUT: convergence of the first absolute moments to that of the limit law; this is
    -- the uniform-integrability substitute that upgrades weak convergence to a weak law
    (habs : Tendsto (fun n => ∫ ω, |Y n 0 ω| ∂ℙ) atTop (𝓝 (∫ t, |t| ∂ν))) :
    TendstoInMeasure ℙ (fun n ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, Y n i ω)) atTop
      (fun _ => ∫ t, t ∂ν) := by
  sorry

end StatLean.HypothesisTesting
