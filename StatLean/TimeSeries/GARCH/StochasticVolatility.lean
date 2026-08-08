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

/-- A linear process over mean-zero (white) noise has mean zero: the mean is the limit
of the (vanishing) means of the `L²`-approximating partial sums, the `L¹` defect being
dominated by the `L²` defect on a probability space. -/
private lemma integral_eq_zero_of_isLinearProcessOf [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {σ2 : ℝ} {Y ε : ℤ → Ω → ℝ} (hY : IsLinearProcessOf ψ Y ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (Y t)) (t : ℤ) : ∫ ω, Y t ω ∂μ = 0 := by
  have hmem : MemLp (Y t) 2 μ := hY.memLp hψ hε hmeas t
  have hint : Integrable (Y t) μ := hmem.integrable one_le_two
  have hεint : ∀ s : ℤ, Integrable (ε s) μ := fun s => (hε.memLp s).integrable one_le_two
  have hSmem : ∀ N : ℕ,
      MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    have := memLp_finset_sum (μ := μ) (p := 2) (Finset.range N)
      (f := fun (j : ℕ) ω => ψ j * ε (t - (j : ℕ)) ω)
      (fun j _ => (hε.memLp (t - (j : ℕ))).const_mul (ψ j))
    simpa using this
  have hSint : ∀ (N : ℕ),
      Integrable (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
    fun N => (hSmem N).integrable one_le_two
  have hS0 : ∀ N : ℕ, ∫ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    rw [integral_finset_sum _ fun j _ => (hεint _).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hε.integral_eq_zero, mul_zero]
  have hbound : ∀ N : ℕ, |∫ ω, Y t ω ∂μ|
      ≤ (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal := by
    intro N
    have hfmem : MemLp (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      hmem.sub (hSmem N)
    have hfint : Integrable (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
      hint.sub (hSint N)
    have hval : ∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ
        = ∫ ω, Y t ω ∂μ := by
      rw [integral_sub hint (hSint N), hS0 N, sub_zero]
    have h1 : |∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ|
        ≤ ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ :=
      abs_integral_le_integral_abs
    have h2 : ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ
        = (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      rw [← integral_norm_eq_lintegral_enorm hfint.aestronglyMeasurable]
      simp [Real.norm_eq_abs]
    have h3 : eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 1 μ
        ≤ eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two hfmem.aestronglyMeasurable
    rw [hval] at h1
    refine h1.trans ?_
    rw [h2]
    exact ENNReal.toReal_mono hfmem.eLpNorm_ne_top h3
  have htend : Tendsto
      (fun N => (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hY t)
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto' htend hbound) (abs_nonneg _))

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
  have hWN : IsWhiteNoise e σe2 μ := hSV.iidLatent.isWhiteNoise
  have hψ : Summable fun j : ℕ => |a1 ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg a1) ha1
  have hYm : ∀ t : ℤ, Measurable (fun ω => h t ω - a0 / (1 - a1)) :=
    fun t => (hmeas t).sub_const _
  obtain ⟨hstatY, hacvfY⟩ := hcausal.isStationary hψ hWN hYm
  -- the centred process has vanishing mean, so `E h_t = a₀/(1 − a₁)`
  have hYint : ∀ t : ℤ, Integrable (fun ω => h t ω - a0 / (1 - a1)) μ :=
    fun t => (hstatY.memLp t).integrable one_le_two
  have heq : ∀ t : ℤ,
      ((fun ω => h t ω - a0 / (1 - a1)) + fun _ : Ω => a0 / (1 - a1)) = h t := by
    intro t; funext ω; simp
  have hhint : ∀ t : ℤ, Integrable (h t) μ := by
    intro t
    have h1 := (hYint t).add (integrable_const (a0 / (1 - a1)))
    rwa [heq t] at h1
  have hmean : ∀ t : ℤ, ∫ ω, h t ω ∂μ = a0 / (1 - a1) := by
    intro t
    have h0 := integral_eq_zero_of_isLinearProcessOf hcausal hψ hWN hYm t
    rw [integral_sub (hhint t) (integrable_const _)] at h0
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
    linarith
  -- covariances are unchanged by centring
  have hcov : ∀ s t : ℤ, cov[fun ω => h s ω - a0 / (1 - a1),
      fun ω => h t ω - a0 / (1 - a1); μ] = cov[h s, h t; μ] := by
    intro s t
    rw [covariance_sub_const_left (hhint s), covariance_sub_const_right (hhint t)]
  -- the geometric autocovariance
  have hgeo : ∀ n : ℕ, (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = a1 ^ n / (1 - a1 ^ 2) := by
    intro n
    have hterm : ∀ j : ℕ, a1 ^ j * a1 ^ (j + n) = a1 ^ n * (a1 ^ 2) ^ j := by
      intro j; ring
    have hsq : a1 ^ 2 < 1 := by nlinarith [abs_nonneg a1, sq_abs a1, abs_lt.mp ha1]
    calc (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = ∑' j : ℕ, a1 ^ n * (a1 ^ 2) ^ j :=
          tsum_congr hterm
      _ = a1 ^ n * ∑' j : ℕ, (a1 ^ 2) ^ j := tsum_mul_left
      _ = a1 ^ n / (1 - a1 ^ 2) := by
          rw [tsum_geometric_of_lt_one (sq_nonneg a1) hsq, div_eq_mul_inv]
  refine ⟨⟨fun t => ?_, fun s t => by rw [hmean s, hmean t], fun t k => ?_⟩, hmean, fun k => ?_⟩
  · have h1 := (hstatY.memLp t).add (memLp_const (μ := μ) (p := 2) (a0 / (1 - a1)))
    rwa [heq t] at h1
  · have h1 := hstatY.cov_shift t k
    rw [hcov (t + k) t, hcov k 0] at h1
    exact h1
  · have h1 := hacvfY k
    rw [acvf, hcov k 0] at h1
    rw [acvf, h1, hgeo k.natAbs, mul_div_assoc]

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
