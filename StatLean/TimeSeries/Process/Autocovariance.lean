import StatLean.TimeSeries.Process.SecondOrder
import StatLean.TimeSeries.ForMathlib.PosSemidefSequence

/-!
# The autocovariance function — symmetry, bounds, positive semidefiniteness
(FY §2.2.1, Theorem 2.7)

For a weakly stationary process: evenness `γ(−k) = γ(k)`, the bound `|γ(k)| ≤ γ(0)`
(Cauchy–Schwarz), and **FY Theorem 2.7 (necessity)**: the autocovariance function is an
even, positive semidefinite sequence — `Σᵢⱼ aᵢaⱼ γ(tᵢ − tⱼ) = Var(Σᵢ aᵢ X_{tᵢ}) ≥ 0`.
The **sufficiency** half (every even positive semidefinite sequence is the ACVF of some
stationary process — via a Gaussian process and Kolmogorov extension, cited by FY to
Brockwell & Davis 1991 p. 27) is a named DEBT here, scheduled for the Gaussian batch.
Basic ACF facts (`ρ(0) = 1`, `|ρ(k)| ≤ 1`) close the section.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.1:
Definition 2.5, Theorem 2.7 with eq. (2.17) (pp. 39–40). (`FY §2.2.1 Thm 2.7`.)

**Proof formalization notes.** Positive semidefiniteness expands
`Var(Σ aᵢ X_{tᵢ})` bilinearly into `Σᵢⱼ aᵢaⱼ Cov(X_{tᵢ}, X_{tⱼ})` and applies
`IsStationary.cov_eq_acvf`; square-integrability comes from the `memLp` field. The
sufficiency statement quantifies existentially over the probability space (`Ω : Type`),
matching FY's "of some stationary time series".

**Bibliographic comments.** The characterization of covariance functions by nonnegative
definiteness is A. Ya. Khinchin (1934); the Gaussian-process construction of the
sufficiency half is standard Kolmogorov-extension reasoning (Kolmogorov,
*Grundbegriffe*, 1933).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Evenness of the autocovariance (FY §2.2.1): `γ(−k) = γ(k)`. -/
theorem IsStationary.acvf_even (h : IsStationary X μ) (k : ℤ) :
    acvf X μ (-k) = acvf X μ k := by
  sorry

/-- `|γ(k)| ≤ γ(0)` (Cauchy–Schwarz; FY §2.2.1). -/
theorem IsStationary.abs_acvf_le [IsProbabilityMeasure μ] (h : IsStationary X μ)
    (k : ℤ) : |acvf X μ k| ≤ acvf X μ 0 := by
  sorry

/-- **FY Theorem 2.7, necessity**: the autocovariance function of a weakly stationary
process is positive semidefinite (`Σᵢⱼ aᵢaⱼ γ(tᵢ − tⱼ) = Var(Σᵢ aᵢ X_{tᵢ}) ≥ 0`,
eq. (2.17)). -/
theorem IsStationary.acvf_posSemidef [IsProbabilityMeasure μ] (h : IsStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t)) :
    IsPosSemidefSeq (acvf X μ) := by
  sorry

/-- **FY Theorem 2.7, sufficiency — DEBT** (proof scheduled for the Gaussian batch:
construct a stationary Gaussian process with the prescribed covariance via Kolmogorov
extension; FY cites Brockwell & Davis 1991, p. 27). Every even positive semidefinite
sequence is the autocovariance function of some weakly stationary process. -/
theorem exists_stationary_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness; FY §2.2.1 Thm 2.7
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, eq. (2.17); FY §2.2.1 Thm 2.7
    (hpsd : IsPosSemidefSeq γ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
        acvf X' μ' = γ := by
  sorry

/-- `ρ(0) = 1` when `γ(0) ≠ 0`. -/
theorem IsStationary.acf_zero (h : IsStationary X μ) (h0 : acvf X μ 0 ≠ 0) :
    acf X μ 0 = 1 := by
  sorry

/-- `|ρ(k)| ≤ 1` (FY §2.2.1). -/
theorem IsStationary.abs_acf_le_one [IsProbabilityMeasure μ] (h : IsStationary X μ)
    (k : ℤ) : |acf X μ k| ≤ 1 := by
  sorry

end StatLean.TimeSeries
