import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
import StatLean.TimeSeries.Process.Autocovariance
import StatLean.TimeSeries.Models.WhiteNoise

/-!
# The spectral distribution of a stationary process (FY §2.3.1–§2.3.2, Theorem 2.10)

**FY Theorem 2.10 (Wiener–Khintchine), process form**: every weakly stationary process
has a unique spectral measure — a negation-invariant finite measure `F` on
`AddCircle (2π)` whose Fourier coefficients are the autocovariances,
`γ(k) = ∫ e^{ikλ} dF(λ)` (FY eq. (2.35), unnormalized form eq. (2.37)). Existence
combines the batch-A Herglotz theorem with the ACVF's evenness and positive
semidefiniteness (FY Theorem 2.7, necessity); uniqueness is
`ext_of_measureFourierCoeff`. The book's `[−π, π]`-with-endpoint conventions are the
circle picture (batch-A design decision D7); `F(π) = γ(0)` is the mass identity.

(FY §2.3.1's periodic-process examples are instances of the correspondence — the
random-phase process of `Stationarity/Gaussian.lean` realizes an arbitrary spectral
measure — and are not separately formalized.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.1
(pp. 49–51, eqs. (2.30)–(2.34)) and §2.3.2 Theorem 2.10 (p. 51) with §2.7.4.
(`FY §2.3.2 Thm 2.10`.)

**Proof formalization notes.** Uniqueness is not claimed in FY (inventory flag); it is
supplied here so "the spectral measure" is meaningful. The mass identity is the `k = 0`
coefficient (`measureFourierCoeff_zero`).

**Bibliographic comments.** N. Wiener, *Generalized harmonic analysis* (1930);
A. Ya. Khinchin (1934); H. Wold (1938); G. Herglotz (1911) for the underlying moment
theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `F` is **a spectral measure** of the process `X` (FY eqs. (2.35)/(2.37)): a
negation-invariant finite measure on the circle whose Fourier coefficients are the
autocovariances. -/
def IsSpectralMeasure (X : ℤ → Ω → ℝ) (μ : Measure Ω)
    (F : Measure (AddCircle (2 * π))) : Prop :=
  IsFiniteMeasure F ∧ NegInvariant F ∧
    ∀ k : ℤ, measureFourierCoeff F k = (acvf X μ k : ℂ)

/-- **FY Theorem 2.10, existence (process form)**: every weakly stationary process has a
spectral measure. -/
theorem exists_isSpectralMeasure [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) :
    ∃ F : Measure (AddCircle (2 * π)), IsSpectralMeasure X μ F := by
  sorry

/-- **Uniqueness of the spectral measure** (supplied on top of FY): two spectral
measures of the same process coincide. -/
theorem IsSpectralMeasure.unique {X : ℤ → Ω → ℝ}
    {F G : Measure (AddCircle (2 * π))}
    (hF : IsSpectralMeasure X μ F) (hG : IsSpectralMeasure X μ G) : F = G := by
  sorry

/-- The **mass identity** `F(circle) = γ(0)` (FY: `G(π) = γ(0) = Var X_t`). -/
theorem IsSpectralMeasure.mass {X : ℤ → Ω → ℝ} {F : Measure (AddCircle (2 * π))}
    (hF : IsSpectralMeasure X μ F) :
    F Set.univ = ENNReal.ofReal (acvf X μ 0) := by
  sorry

/-- The spectral measure of white noise is the uniform measure of total mass `σ²`
(FY §2.3.2: constant spectral density `σ²/2π`): `F = σ² • (normalized Haar)`. -/
theorem isSpectralMeasure_whiteNoise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hσ : 0 ≤ σ2) (hε : IsWhiteNoise ε σ2 μ) :
    IsSpectralMeasure ε μ (ENNReal.ofReal σ2 •
      (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) := by
  sorry

end StatLean.TimeSeries
