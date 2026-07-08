import StatLean.Bayesian.EmpiricalBayes.Defs
import StatLean.Bayesian.ForMathlib.GaussianDeriv

/-!
# Tweedie's formula

The most important empirical-Bayes theorem: for a Gaussian likelihood `X ∣ θ ∼ N(θ, v)` with any
prior `G`, the posterior mean of `θ` given the observation is
$$\mathbb E[\theta \mid X = x] = x + v\,\frac{d}{dx}\log f_G(x),$$
where `f_G(x) = ∫ N(x; θ, v)\,G(dθ)` is the marginal density — the posterior mean depends on `G`
only through the *marginal*, which is directly estimable from data. This connects empirical Bayes,
shrinkage, density estimation, and modern large-scale inference.

**Reference.** Not in Robert. B. Efron, *Large-Scale Inference*, Cambridge University Press, 2010,
§1.5, eq. (1.24)–(1.26); B. Efron, "Tweedie's formula and selection bias," *J. Amer. Statist.
Assoc.* 106 (2011), 1602–1614; the formula is credited to M. C. K. Tweedie (via H. Robbins 1956).

**Proof formalization notes.** The Gaussian score identity `(θ−x)·pdf = v·∂ₓ pdf`
(`ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal`) rewrites the numerator
`∫ θ·pdf dG = x·f_G(x) + v·f_G'(x)`; dividing by `f_G(x) > 0` and using `f_G'/f_G = (log f_G)'`
yields the formula. Moving `∂ₓ` inside `∫ · dG(θ)` (`hasDerivAt_gaussianMarginalPDF`) needs a
`G`-integrable envelope for the score, which holds when the prior has a finite first moment
(`Integrable (fun θ => θ) G`) — a genuine analytic side-condition (USER-INPUT, Efron §1.5), not
derivable from the setup. The variance companion needs a finite second moment.

**Bibliographic comments.** Tweedie's formula is the exponential-family posterior-mean identity
attributed by Robbins (1956) to M. C. K. Tweedie; its empirical-Bayes and selection-bias
applications are Efron's (2011). It is the continuous analogue of Robbins's Poisson rule and the
basis of g-modeling (Efron 2016) and of the general-maximum-likelihood empirical Bayes of Jiang and
Zhang (2009).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The **Gaussian marginal density** `f_G(x) = ∫ N(x; θ, v) G(dθ)` (Efron §1.5). -/
noncomputable def gaussianMarginalPDF (G : Measure ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  ∫ θ, gaussianPDFReal θ v x ∂G

/-- **Tweedie's estimator** `x + v·(log f_G)'(x)` (Efron eq. (1.26)). -/
noncomputable def tweedieEstimator (G : Measure ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  x + (v : ℝ) * deriv (fun y => Real.log (gaussianMarginalPDF G v y)) x

/-- **Differentiation of the marginal under the integral**: the spatial derivative of the Gaussian
marginal density is the `G`-average of the pointwise Gaussian score (Efron §1.5). -/
theorem hasDerivAt_gaussianMarginalPDF (G : Measure ℝ) [IsFiniteMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior first moment (integrable Gaussian-score envelope); Efron §1.5
    (hmean : Integrable (fun θ => θ) G) (x : ℝ) :
    HasDerivAt (gaussianMarginalPDF G v)
      (∫ θ, (θ - x) / (v : ℝ) * gaussianPDFReal θ v x ∂G) x := by
  sorry

/-- **Tweedie's formula** (3F.9): the posterior mean of the Gaussian location equals
`x + v·(log f_G)'(x)` (Efron eq. (1.26)). -/
theorem tweedie_normal_posteriorMean (G : Measure ℝ) [IsProbabilityMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior first moment; Efron §1.5
    (hmean : Integrable (fun θ => θ) G)
    -- USER-INPUT: nondegenerate marginal at `x`; Efron §1.5
    (x : ℝ) (hpos : 0 < gaussianMarginalPDF G v x) :
    (∫ θ, θ * gaussianPDFReal θ v x ∂G) / gaussianMarginalPDF G v x = tweedieEstimator G v x := by
  sorry

/-- **Tweedie's variance formula** (3F.10, stretch): the posterior variance is
`v + v²·(log f_G)''(x)` (Efron §1.5). -/
theorem tweedie_normal_posteriorVariance (G : Measure ℝ) [IsProbabilityMeasure G] (v : ℝ≥0)
    -- USER-INPUT: nondegenerate variance; Efron §1.5
    (hv : v ≠ 0)
    -- USER-INPUT: finite prior second moment; Efron §1.5
    (hsq : Integrable (fun θ => θ ^ 2) G)
    -- USER-INPUT: nondegenerate marginal at `x`; Efron §1.5
    (x : ℝ) (hpos : 0 < gaussianMarginalPDF G v x) :
    (∫ θ, (θ - tweedieEstimator G v x) ^ 2 * gaussianPDFReal θ v x ∂G) / gaussianMarginalPDF G v x
      = (v : ℝ) + (v : ℝ) ^ 2 * deriv (deriv (fun y => Real.log (gaussianMarginalPDF G v y))) x := by
  sorry

end StatLean.Bayesian
