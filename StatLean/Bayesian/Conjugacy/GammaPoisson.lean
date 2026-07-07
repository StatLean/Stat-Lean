import StatLean.Bayesian.Conjugacy.Defs
import StatLean.Bayesian.Conjugacy.Criterion
import StatLean.Bayesian.ForMathlib.IIDKernel
import Mathlib.Probability.Distributions.Gamma

/-!
# Gamma-Poisson conjugacy

For a Poisson rate `λ ~ Gamma(a, r)` (shape `a`, rate `r`) and iid counts
`y₁, …, yₙ ~ Poisson(λ)`:
$$\lambda \mid y_{1:n} \sim \mathrm{Gamma}\Big(a + \sum_i y_i,\ r + n\Big)
  \qquad \text{predictive-a.e.}$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Table 3.3.1 (Poisson 𝒫(θ) + Gamma 𝒢(α,β) → 𝒢(α+x, β+1),
single observation), p. 121; Table 4.2.1 (posterior mean `(α+x)/(β+1)`), p. 176; Appendix
A.2/A.12, pp. 519–521. The `n`-sample form `𝒢(α+Σyᵢ, β+n)` follows by sufficiency (§4.2.2).

**Proof formalization notes.** The pinned `gammaMeasure a r` is shape/RATE, exactly matching
Robert's `𝒢(α, β)` with `β` a rate, so the update reads `Gamma(a + S, r + n)` with no
reparameterization. The rate clamp `Real.toNNReal` is invisible under the Gamma prior (its pdf
vanishes on `θ ≤ 0`); the Poisson kernel is Markov for every real parameter since
`poissonPMFReal` sums to `1` at every `ℝ≥0` rate (pinned `poissonPMFRealSum`; at rate `0` the law
is the Dirac mass at `0`). Pointwise algebra: `gammaPDF a r θ · ∏ᵢ e^{−θ}θ^{yᵢ}/yᵢ! =
C(y) · gammaPDF (a + Σyᵢ) (r + n) θ` on `θ > 0` (`Real.rpow_natCast`, `rpow_add`,
`Real.exp_add`), fed to the criterion via `iidKernel_withDensity`.

**Bibliographic comments.** The Gamma prior for Poisson intensities is the count-data workhorse
of Bayesian practice, from actuarial credibility theory (Bühlmann 1967) to empirical-Bayes
shrinkage of rates (Robbins 1956; Efron–Morris 1975 in the Gaussian analogue). Robert's
Table 3.3.1 lists it among the Raiffa–Schlaifer (1961) natural conjugate pairs; the
negative-binomial marginal it induces is the classical overdispersed count model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The Poisson kernel is Markov for every real parameter (rate clamped at `0`). -/
instance : IsMarkovKernel poissonKernel := sorry

/-- Pointwise pdf algebra: Gamma pdf times an iid Poisson likelihood is an explicit constant times
the updated Gamma pdf; both sides vanish on `θ ≤ 0`. -/
theorem gammaPDF_mul_prod_poissonDensity {a r : ℝ}
    -- USER-INPUT: positive Gamma shape and rate; Robert Appendix A.2
    (ha : 0 < a) (hr : 0 < r) {n : ℕ} (y : Fin n → ℕ) (θ : ℝ) :
    gammaPDF a r θ * ∏ i, poissonDensity θ (y i)
      = ENNReal.ofReal
          ((r ^ a * Real.Gamma (a + ∑ i, (y i : ℝ)))
            / (Real.Gamma a * (r + n) ^ (a + ∑ i, (y i : ℝ)) * ∏ i, (Nat.factorial (y i) : ℝ)))
          * gammaPDF (a + ∑ i, (y i : ℝ)) (r + n) θ := sorry

/-- **Gamma-Poisson posterior** (Robert Table 3.3.1, `n`-sample form): iid Poisson counts update
`Gamma(a, r)` to `Gamma(a + ∑ yᵢ, r + n)`, predictive-a.e. -/
theorem gamma_poisson_posterior_ae {a r : ℝ}
    -- USER-INPUT: positive Gamma shape and rate; Robert Appendix A.2
    (ha : 0 < a) (hr : 0 < r)
    -- LEAN-ONLY: instance plumbing, derivable from ha/hr via `isProbabilityMeasure_gammaMeasure`
    [IsFiniteMeasure (gammaMeasure a r)] (n : ℕ) :
    ∀ᵐ y ∂(iidKernel poissonKernel n ∘ₘ gammaMeasure a r),
      ((iidKernel poissonKernel n)†(gammaMeasure a r)) y
        = gammaMeasure (a + ∑ i, (y i : ℝ)) (r + n) := sorry

end StatLean.Bayesian
