import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.Process.LinearProcess
import StatLean.TimeSeries.Process.SecondOrder
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stochastic volatility models (FY §4.2.9, eqs. (4.60)–(4.62))

The SV model `X_t = ε_t g(h_t)` with latent AR(1) log-volatility
`h_t = a₀ + a₁ h_{t−1} + e_t` is `Models/Defs.lean`'s `IsSV`. This file carries the
three in-text results, all elementary once the AR(1) facts and the lognormal moment
formula are available:

* **eq. (4.60)**: `|a₁| < 1` ⇒ the latent process is (strictly) stationary with
  `μ_h = a₀/(1 − a₁)` and `γ_h(k) = σ_e²a₁^{|k|}/(1 − a₁²)`, hence `X` is strictly
  stationary;
* **eq. (4.61)** (Taylor's lognormal SV, `g = exp(·/2)` and Gaussian `ε`): the even
  moments `E X_t^{2k} = (2k)!·exp(kμ_h + k²σ_h²/2)/(2^k k!)`, and in particular the
  kurtosis `κ_x = 3e^{σ_h²} > 3` — SV is always leptokurtic;
* **eq. (4.62)**: `log X_t² = h_t + log ε_t²`, an ARMA(1,1) in its first two moments
  (compare Example 2.7), together with the squared-process autocorrelation
  `Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(exp(σ_h²) − 1)`.

Estimation for SV models (GMM, Kalman filtering on (4.62), MCMC) is citation-only in
FY §4.2.9 and is not formalized.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.9,
eqs. (4.60)–(4.62) (pp. 179–181). (`FY §4.2.9`.)

**Bibliographic comments.** The lognormal SV model is S. J. Taylor, *Modelling Financial
Time Series* (Wiley, 1986); the ARMA(1,1) representation of `log X_t²` and the
quasi-likelihood/Kalman route are Harvey, Ruiz & Shephard (1994).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY eq. (4.60)**: with `|a₁| < 1` the latent log-volatility is second-order
stationary with mean `a₀/(1 − a₁)` and autocovariance `σ_e² a₁^{|k|}/(1 − a₁²)`. -/
theorem IsSV.latent_stationary [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: causal AR(1) latent process; FY eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hmeas : ∀ t, Measurable (h t)) :
    IsStationary h μ ∧ (∀ t, ∫ ω, h t ω ∂μ = a0 / (1 - a1)) ∧
      ∀ k : ℤ, acvf h μ k = σe2 * a1 ^ k.natAbs / (1 - a1 ^ 2) := by
  sorry

/-- **FY eq. (4.60), conclusion**: a stationary latent process makes the observed SV
process strictly stationary. -/
theorem IsSV.isStrictlyStationary [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    -- USER-INPUT: strict stationarity of the latent chain (from the AR(1) causal
    -- representation over iid noise); FY eq. (4.60)
    (hstath : IsStrictlyStationary h μ) :
    IsStrictlyStationary X μ := by
  sorry

/-- **FY eq. (4.61)** (Taylor's lognormal SV): with `g(x) = e^{x/2}`, standard normal
`ε`, and a stationary Gaussian latent process with mean `μ_h` and variance `σ_h²`,
`E X_t^{2k} = (2k)! · exp(k μ_h + k²σ_h²/2) / (2^k k!)`. -/
theorem IsSV.moment_even_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: standard normal observation noise; FY eq. (4.61)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    -- USER-INPUT: stationary Gaussian latent law; FY eq. (4.61)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (k : ℕ) :
    (∫ ω, X 0 ω ^ (2 * k) ∂μ)
      = (Nat.factorial (2 * k) : ℝ) * Real.exp (k * μh + (k : ℝ) ^ 2 * σh2 / 2)
        / (2 ^ k * Nat.factorial k) := by
  sorry

/-- **FY eq. (4.61), kurtosis**: the lognormal SV kurtosis is `3e^{σ_h²} > 3` — SV is
strictly leptokurtic (stated multiplicatively to avoid division). -/
theorem IsSV.kurtosis_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2) :
    (∫ ω, X 0 ω ^ 4 ∂μ) = 3 * Real.exp σh2 * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 ∧
      3 < 3 * Real.exp σh2 := by
  sorry

/-- **FY eq. (4.62)**: the log-squared observation decomposes as `log X_t² = h_t +
log ε_t²` (for `g = exp(·/2)`), the identity behind the ARMA(1,1)-in-two-moments
representation and the Kalman-filter estimation route. -/
theorem IsSV.log_sq_decomposition [IsProbabilityMeasure μ] {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ) (t : ℤ) :
    (fun ω => Real.log (X t ω ^ 2)) =ᵐ[μ] fun ω => h t ω + Real.log (ε t ω ^ 2) := by
  sorry

/-- **FY eq. (4.62), squared-process ACF** (lognormal algebra):
`Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(exp(σ_h²) − 1)`. -/
theorem IsSV.acf_sq_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (ha1 : |a1| < 1)
    -- USER-INPUT: the stationary latent autocovariance structure; FY eq. (4.60)
    (hacvf : ∀ k : ℤ, acvf h μ k = σh2 * a1 ^ k.natAbs)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ) (k : ℤ) :
    acf (fun t ω => X t ω ^ 2) μ k
      = (Real.exp (σh2 * a1 ^ k.natAbs) - 1) / (Real.exp σh2 - 1) := by
  sorry

end StatLean.TimeSeries
