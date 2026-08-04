import StatLean.TimeSeries.ForMathlib.Fourier.FejerKernel
import StatLean.TimeSeries.ForMathlib.Fourier.MeasureFourierCoeff

/-!
# The Herglotz theorem on ℤ (FY Theorem 2.10, existence core)

**Herglotz/Bochner for ℤ**: a real sequence is even and positive semidefinite **iff** it
is the Fourier-coefficient sequence of a (negation-invariant) finite measure on the
circle `AddCircle (2π)`. This is the measure-theoretic core of FY Theorem 2.10
(Wiener–Khintchine): combined with FY Theorem 2.7 (`Process/Autocovariance.lean`) it
characterizes autocovariance functions of stationary time series; uniqueness of the
measure is `ext_of_measureFourierCoeff` (`MeasureFourierCoeff.lean`).

Proof route for existence (FY §2.7.4, self-contained): the Fejér densities
`fejerSum γ n ≥ 0` define measures `F_n` on the circle with trigonometric moments
`(1 − |j|/n) γ(j)` (FY eq. (2.71)) and total mass `γ(0)`; normalize, extract a weakly
convergent subsequence by compactness of `ProbabilityMeasure` on the compact circle
(pinned Prokhorov instance), and pass the moments to the limit
(`tendsto_measureFourierCoeff_of_tendsto`). The degenerate case `γ(0) = 0` forces
`γ ≡ 0` (`IsPosSemidefSeq.abs_le_of_even`) with `F = 0`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, Theorem 2.10
(p. 51) and §2.7.4 (pp. 80–81). (`FY §2.3.2 Thm 2.10; §2.7.4`.)

**Proof formalization notes.** FY states the result for the normalized ACF (`ρ`, a
probability distribution `F`); we state the unnormalized form (mass `γ(0)`), from which
the normalized version is scalar rescaling. The book's "symmetric distribution on
`[−π, π]`" is `NegInvariant` on the circle — symmetry of the constructed limit is
part of the statement here (glossed in the book; the Fejér densities are even).

**Bibliographic comments.** G. Herglotz, "Über Potenzreihen mit positivem, reellem Teil
im Einheitskreis", *Ber. Verh. Sächs. Akad. Wiss. Leipzig* **63** (1911), 501–511;
the ℝ-analogue is S. Bochner (1932). In time series the result enters through
A. Ya. Khinchin (1934) and H. Wold (1938); FY follow Brockwell & Davis (1991),
pp. 118–119.
-/

open MeasureTheory
open scoped Real

namespace StatLean.TimeSeries

/-- **Herglotz existence** (FY Theorem 2.10, "only if" core; proof route §2.7.4): an
even positive semidefinite sequence is the Fourier-coefficient sequence of a
negation-invariant finite measure on `AddCircle (2π)`. -/
theorem exists_measure_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness of the sequence; FY §2.3.2 Thm 2.10
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, FY eq. (2.17); FY §2.3.2 Thm 2.10
    (hpsd : IsPosSemidefSeq γ) :
    ∃ F : Measure (AddCircle (2 * π)), IsFiniteMeasure F ∧ NegInvariant F ∧
      ∀ k : ℤ, measureFourierCoeff F k = (γ k : ℂ) := by
  sorry

/-- **Herglotz converse** (FY Theorem 2.10, "if" core): the real parts of the Fourier
coefficients of a finite measure form a positive semidefinite sequence
(`Σᵢⱼ aᵢaⱼ ∫ e^{i(tᵢ−tⱼ)z} dF = ∫ |Σᵢ aᵢ e^{itᵢz}|² dF ≥ 0`). -/
theorem isPosSemidefSeq_measureFourierCoeff (F : Measure (AddCircle (2 * π)))
    [IsFiniteMeasure F] :
    IsPosSemidefSeq fun k => (measureFourierCoeff F k).re := by
  sorry

/-- Evenness of the coefficient sequence of a negation-invariant finite measure
(companion to the converse: together they say the coefficient sequence of a
`NegInvariant` finite measure is even and positive semidefinite). -/
theorem measureFourierCoeff_re_even (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (k : ℤ) :
    (measureFourierCoeff F (-k)).re = (measureFourierCoeff F k).re := by
  sorry

end StatLean.TimeSeries
