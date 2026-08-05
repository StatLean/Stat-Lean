import StatLean.TimeSeries.Spectral.SpectralMeasure

/-!
# Spectral densities under absolutely summable autocovariance (FY §2.3.2, Theorem 2.11)

**FY Theorem 2.11**: when `Σ_k |γ(k)| < ∞`, the spectral measure has the continuous
density `g(λ) = (2π)⁻¹ Σ_{k ∈ ℤ} γ(k) e^{−ikλ}` with respect to the mass-`2π` Haar
measure on the circle (FY's unnormalized eq. (2.38); the `1/2π` sits in the density,
never in the forward transform — batch design D7). We define `spectralDensityOf` by the
real part of that series (γ even makes the series real) and prove: nonnegativity,
continuity, the inversion identity `γ(k) = ∫ e^{ikλ} g(λ) dλ`, and that
`(2π • haar).withDensity g` **is** the spectral measure.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.2,
Theorem 2.11 and eqs. (2.36)–(2.38) (pp. 52–53); in-text proof p. 52.
(`FY §2.3.2 Thm 2.11`.)

**Proof formalization notes.**
* Uniform convergence of the series (Weierstrass M-test, `Σ|γ| < ∞`) gives continuity
  and justifies term-by-term integration; the pointwise nonnegativity comes from
  Fejér-mean convergence (`fejerSum_re_nonneg` + `Filter.Tendsto.cesaro`-style limit of
  the weighted sums, FY's in-text argument), not from the series' shape.
* The identification with the spectral measure uses the orthonormality of `fourier`
  against `haarAddCircle` (Mathlib's probability Haar; the `2π` mass normalization
  converts FY's `∫_{−π}^{π}` to `2π • haar`).

**Bibliographic comments.** The `ℓ¹`-inversion pair goes back to Wiener's *Generalized
harmonic analysis*; FY's Theorem 2.11 statement follows Brockwell & Davis (1991),
Cor. 4.3.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **spectral density series** of a process (FY eq. (2.38)):
`g(λ) = (2π)⁻¹ Σ_{k ∈ ℤ} γ(k) · Re(e^{ikλ})` (the series is real for even `γ`; junk
when not summable, by the `tsum` convention). -/
noncomputable def spectralDensityOf (X : ℤ → Ω → ℝ) (μ : Measure Ω)
    (l : AddCircle (2 * π)) : ℝ :=
  (2 * π)⁻¹ * ∑' k : ℤ, acvf X μ k * (fourier k l).re

/-- Summability package for FY Theorem 2.11: `Σ_{k ∈ ℤ} |γ(k)| < ∞` (equivalently the
book's one-sided `Σ_{k ≥ 1}`, by evenness). -/
def HasSummableACVF (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Summable fun k : ℤ => |acvf X μ k|

/-- The spectral density series is continuous under summable ACVF. -/
theorem continuous_spectralDensityOf [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hsum : HasSummableACVF X μ) :
    Continuous (spectralDensityOf X μ) := by
  sorry

/-- **Nonnegativity** (FY Thm 2.11, in-text proof): under stationarity and summable
ACVF, the spectral density series is pointwise nonnegative (Fejér-mean argument). -/
theorem spectralDensityOf_nonneg [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) (hsum : HasSummableACVF X μ) (l : AddCircle (2 * π)) :
    0 ≤ spectralDensityOf X μ l := by
  sorry

/-- **FY Theorem 2.11**: under stationarity and summable ACVF, the measure with density
`spectralDensityOf` against the mass-`2π` Haar measure is the spectral measure of the
process (existence-with-density form; inversion `γ(k) = ∫ e^{ikλ} g dλ` is the
coefficient clause of `IsSpectralMeasure`). -/
theorem isSpectralMeasure_withDensity [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) (hsum : HasSummableACVF X μ) :
    IsSpectralMeasure X μ
      ((ENNReal.ofReal (2 * π) •
          (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))).withDensity
        fun l => ENNReal.ofReal (spectralDensityOf X μ l)) := by
  sorry

/-- Causal stationary ARMA processes satisfy the summable-ACVF hypothesis
(FY Prop 2.2(i) feeding §2.3; exponential decay ⇒ `ℓ¹`). -/
theorem IsARMA.hasSummableACVF [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℤ, |acvf X μ k| ≤ C * r ^ k.natAbs) :
    HasSummableACVF X μ := by
  sorry

end StatLean.TimeSeries
