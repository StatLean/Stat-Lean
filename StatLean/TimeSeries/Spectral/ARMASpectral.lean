import StatLean.TimeSeries.Spectral.LinearFilter
import StatLean.TimeSeries.Stationarity.ARMAExistence

/-!
# ARMA spectral densities (FY §2.3.3, Proposition 2.4, eqs. (2.46)–(2.48))

**FY Proposition 2.4**: a stationary causal ARMA(p, q) process with `b(z) ≠ 0` on the
closed unit disc has spectral density
`g(ω) = σ²/(2π) · |a(e^{−iω})|² / |b(e^{−iω})|²` (eq. (2.46); the rational-in-cosines
expansions (2.47)–(2.48) are this identity with `|trig poly|²` written out and are not
restated separately). The in-text proof applies Theorem 2.12 twice — once to
`b(B)X = a(B)ε` viewed as filtering `X`, once viewing it as filtering `ε` — and uses the
white-noise density `g_ε ≡ σ²/(2π)`.

Also here: **Example 2.5** (AR(1) density, eq. (2.40), in unnormalized `g`-scale) and
**Example 2.7** (AR(1) signal plus uncorrelated observation white noise: the spectrum is
`g_Z + σ_η²/(2π)`, an ARMA(1,1)-shaped rational function — FY's non-identifiability
remark: distinct (signal, noise) pairs can produce the same spectrum).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.3,
Proposition 2.4, eqs. (2.46)–(2.48) (pp. 58–59); Example 2.5 (p. 54, eq. (2.40));
Example 2.7 (p. 59). (`FY §2.3.3`.)

**Proof formalization notes.**
* The bridge between polynomial filters and `transferFun` is `polyFilterCoeffs`:
  the transfer function of the one-sided finite filter with coefficients of `P` is
  `P(e^{−iω})` (`transferFun_polyFilterCoeffs`), where `e^{−iω} = fourier (−1) l`.
* Summability of the output ACVF is **derived**, not assumed: causality + no-root ⇒
  exponential ACVF decay (`IsARMA.acvf_exponential_decay`) ⇒ `HasSummableACVF`
  (`IsARMA.hasSummableACVF`), per the hypothesis-discipline rule.

**Bibliographic comments.** The rational ARMA spectrum computation is classical
(Wold 1938; Doob 1953 ch. X); FY Prop 2.4 follows Brockwell & Davis (1991), Thm 4.4.2.
The signal-plus-noise non-identifiability of Example 2.7 traces to the errors-in-
variables literature (Grether & Maddala 1973).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The two-sided coefficient sequence of the **one-sided polynomial filter** `P(B)`:
`k ↦ coeff_k P` for `k ≥ 0` and `0` for `k < 0` (FY §2.3.3's `b(B)X`, `a(B)ε`). Finite
support, hence always `ℓ¹`. -/
noncomputable def polyFilterCoeffs (P : Polynomial ℝ) : ℤ → ℝ := fun k =>
  if 0 ≤ k then P.coeff k.toNat else 0

/-- A polynomial filter has finitely many nonzero coefficients, hence is `ℓ¹`. -/
theorem summable_abs_polyFilterCoeffs (P : Polynomial ℝ) :
    Summable fun k : ℤ => |polyFilterCoeffs P k| := by
  sorry

/-- The transfer function of a polynomial filter is the polynomial evaluated at
`e^{−iω}`: `Γ(ω) = Σ_{k≥0} coeff_k P · e^{−ikω} = P(e^{−iω})` (FY §2.3.3, the
computation behind eq. (2.46)). -/
theorem transferFun_polyFilterCoeffs (P : Polynomial ℝ) (l : AddCircle (2 * π)) :
    transferFun (polyFilterCoeffs P) l = Polynomial.aeval ((fourier (-1) l : ℂ)) P := by
  sorry

/-- An exact a.e. finite-sum representation realizes the polynomial filter in the `L²`
sense of `IsFilteredBy` (the partial sums are eventually exact). -/
theorem isFilteredBy_of_ae_eq_polySum {X Y : ℤ → Ω → ℝ} {P : Polynomial ℝ}
    (h : ∀ t : ℤ, X t =ᵐ[μ] fun ω =>
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * Y (t - (k : ℕ)) ω) :
    IsFilteredBy X Y (polyFilterCoeffs P) μ := by
  sorry

/-- White noise has (trivially) absolutely summable ACVF. -/
theorem IsWhiteNoise.hasSummableACVF [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) :
    HasSummableACVF ε μ := by
  sorry

/-- **White-noise spectral density** (FY §2.3.2, p. 53): `g_ε(ω) ≡ σ²/(2π)` — the flat
spectrum ("white light"). -/
theorem IsWhiteNoise.spectralDensityOf_eq [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ) (l : AddCircle (2 * π)) :
    spectralDensityOf ε μ l = σ2 / (2 * π) := by
  sorry

/-- **FY Proposition 2.4 (eq. (2.46))**: the spectral density of a stationary causal
ARMA(p, q) process with `b(z) ≠ 0` on the closed unit disc is
`g(ω) = σ²/(2π) · |a(e^{−iω})|²/|b(e^{−iω})|²`.

Summability of the ACVF is derived internally (causality + no-root ⇒ exponential decay),
not assumed. -/
theorem IsARMA.spectralDensityOf_eq [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    -- USER-INPUT: the ARMA process is stationary; FY Prop 2.4
    (hstat : IsStationary X μ)
    -- USER-INPUT: causal MA(∞) representation with the ARMA ψ-weights; FY §2.1.3
    -- standing causality convention (the iff with `NoRootClosedDisc` is the named debt
    -- `arma_causal_of_stationary_debt`)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    -- USER-INPUT: b(z) ≠ 0 for |z| ≤ 1; FY Prop 2.4
    (hroot : NoRootClosedDisc b)
    (hmeas : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l =
      σ2 / (2 * π) * ‖Polynomial.aeval ((fourier (-1) l : ℂ)) (maPoly a)‖ ^ 2
        / ‖Polynomial.aeval ((fourier (-1) l : ℂ)) (arPoly b)‖ ^ 2 := by
  sorry

/-- **FY Example 2.5 (eq. (2.40))**, in unnormalized `g`-scale: a stationary causal
AR(1) process with `|b| < 1` has
`g(ω) = σ²/(2π) / (1 + b² − 2b cos ω)`. (FY prints the normalized `f = g/γ(0)`; the
`γ(0) = σ²/(1−b²)` factor converts.) -/
theorem spectralDensityOf_ar_one [IsProbabilityMeasure μ] {b1 σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsAR (fun _ : Fin 1 => b1) σ2 X ε μ)
    -- USER-INPUT: stationarity; FY Example 2.5
    (hstat : IsStationary X μ)
    -- USER-INPUT: causal representation; FY §2.1.3 convention
    (hcausal :
      IsLinearProcessOf (armaPsi (fun _ : Fin 1 => b1) (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    -- USER-INPUT: |b| < 1 (equivalent to the AR polynomial's no-root condition,
    -- derived internally); FY Example 2.5
    (hb : |b1| < 1)
    (hmeas : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l
      = σ2 / (2 * π) / (1 + b1 ^ 2 - 2 * b1 * (fourier 1 l).re) := by
  sorry

/-- Sum of two uncorrelated weakly stationary processes: stationary again, with
additive ACVF (the covariance computation behind FY Example 2.7). -/
theorem isStationary_add_of_uncorrelated [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    (hX : IsStationary X μ) (hY : IsStationary Y μ)
    -- USER-INPUT: cross-uncorrelation at all lags; FY Example 2.7 ("independent of")
    (huncorr : ∀ s t : ℤ, cov[X s, Y t; μ] = 0) :
    IsStationary (fun t ω => X t ω + Y t ω) μ ∧
      ∀ k : ℤ, acvf (fun t ω => X t ω + Y t ω) μ k = acvf X μ k + acvf Y μ k := by
  sorry

/-- **FY Example 2.7**: AR(1) signal plus uncorrelated white observation noise has
spectral density `g_Z(ω) + σ_η²/(2π)` — an ARMA(1,1)-shaped rational spectrum. FY's
point: the sum is *not* AR(1), and distinct (signal, noise) parameter pairs can give
the same spectrum (non-identifiability). -/
theorem spectralDensityOf_ar_one_add_noise [IsProbabilityMeasure μ]
    {b1 σ2 ση2 : ℝ} {Z ε η : ℤ → Ω → ℝ}
    (hZ : IsAR (fun _ : Fin 1 => b1) σ2 Z ε μ)
    -- USER-INPUT: stationarity of the signal; FY Example 2.7
    (hstatZ : IsStationary Z μ)
    -- USER-INPUT: causal representation of the signal; FY §2.1.3 convention
    (hcausal :
      IsLinearProcessOf (armaPsi (fun _ : Fin 1 => b1) (Fin.elim0 : Fin 0 → ℝ)) Z ε μ)
    -- USER-INPUT: |b| < 1; FY Example 2.7
    (hb : |b1| < 1)
    (hmeas : ∀ t, Measurable (Z t))
    -- USER-INPUT: white observation noise; FY Example 2.7
    (hη : IsWhiteNoise η ση2 μ)
    -- USER-INPUT: noise uncorrelated with the signal at all lags; FY Example 2.7
    (huncorr : ∀ s t : ℤ, cov[Z s, η t; μ] = 0)
    (l : AddCircle (2 * π)) :
    spectralDensityOf (fun t ω => Z t ω + η t ω) μ l
      = σ2 / (2 * π) / (1 + b1 ^ 2 - 2 * b1 * (fourier 1 l).re) + ση2 / (2 * π) := by
  sorry

end StatLean.TimeSeries
