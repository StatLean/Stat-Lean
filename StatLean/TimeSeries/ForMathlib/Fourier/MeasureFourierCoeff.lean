import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Fourier coefficients of finite measures on the circle `AddCircle (2π)`

For a finite measure `F` on `AddCircle (2π)` we define
`measureFourierCoeff F n = ∫ e^{inz} dF(z)` — with Mathlib's `fourier n` at `T = 2π`
being exactly `z ↦ e^{inz}`, so the book's transform convention
`γ(τ) = ∫_{−π}^{π} e^{iτω} dF(ω)` (FY eqs. (2.33)–(2.35), no `2π` factor in the forward
transform) is `measureFourierCoeff F τ` verbatim.

Bricks stated here:

* mass and norm bounds (`measureFourierCoeff_zero`, `norm_measureFourierCoeff_le`);
* **uniqueness**: a finite measure on the circle is determined by its Fourier
  coefficients (`ext_of_measureFourierCoeff`) — the uniqueness half that FY Theorem 2.10
  leaves unstated; via Stone–Weierstrass density of trigonometric polynomials
  (`span_fourier_closure_eq_top`);
* **weak-convergence of coefficients**: coefficients pass to weak limits of probability
  measures (`tendsto_measureFourierCoeff_of_tendsto`) — the Helly–Bray step of FY §2.7.4;
* negation invariance (`NegInvariant`) and its coefficient symmetry — the "symmetric
  distribution" bookkeeping of FY Theorem 2.10.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.1–§2.3.2
(eqs. (2.33)–(2.35)) and §2.7.4 (pp. 80–81). (`FY §2.3.2 Thm 2.10; §2.7.4`.)

**Proof formalization notes.** The interval `[−π, π]` with endpoints identified *is*
`AddCircle (2π)`; atoms at `±π` (a real possibility for spectral distributions, e.g.
white-noise-with-period-2 components) are handled by the circle picture with no endpoint
conventions. Uniqueness reduces to equality of the integrals of all continuous functions
(Riesz-type argument via density of `span (fourier '' univ)` in `C(AddCircle (2π), ℂ)`).

**Bibliographic comments.** That trigonometric moments determine a measure on the circle
is classical (Herglotz 1911, F. Riesz); the weak-convergence step is the Helly–Bray
theorem (E. Helly 1912; H. E. Bray 1919).
-/

open MeasureTheory Filter
open scoped Real Topology

namespace StatLean.TimeSeries

/-- **Fourier coefficient of a measure** on `AddCircle (2π)`:
`measureFourierCoeff F n = ∫ e^{inz} dF(z)` (FY forward-transform convention,
eqs. (2.33)–(2.35): no `2π` factor). -/
noncomputable def measureFourierCoeff (F : Measure (AddCircle (2 * π))) (n : ℤ) : ℂ :=
  ∫ z, fourier n z ∂F

/-- The zeroth coefficient is the total mass. -/
theorem measureFourierCoeff_zero (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F] :
    measureFourierCoeff F 0 = ((F Set.univ).toReal : ℂ) := by
  sorry

/-- Coefficients are bounded by the total mass (`‖fourier n z‖ = 1`). -/
theorem norm_measureFourierCoeff_le (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (n : ℤ) : ‖measureFourierCoeff F n‖ ≤ (F Set.univ).toReal := by
  sorry

/-- **Uniqueness**: a finite measure on the circle is determined by its Fourier
coefficients. (The uniqueness half of the Herglotz correspondence, which FY Theorem 2.10
does not state; needed to speak of *the* spectral distribution.) -/
theorem ext_of_measureFourierCoeff (F G : Measure (AddCircle (2 * π)))
    [IsFiniteMeasure F] [IsFiniteMeasure G]
    (h : ∀ n, measureFourierCoeff F n = measureFourierCoeff G n) : F = G := by
  sorry

/-- **Helly–Bray step**: Fourier coefficients pass to weak limits of probability
measures on the circle. -/
theorem tendsto_measureFourierCoeff_of_tendsto
    {Fs : ℕ → ProbabilityMeasure (AddCircle (2 * π))}
    {F : ProbabilityMeasure (AddCircle (2 * π))}
    (h : Tendsto Fs atTop (𝓝 F)) (n : ℤ) :
    Tendsto (fun k => measureFourierCoeff (Fs k : Measure (AddCircle (2 * π))) n) atTop
      (𝓝 (measureFourierCoeff (F : Measure (AddCircle (2 * π))) n)) := by
  sorry

/-- A measure on the circle is **negation-invariant** ("symmetric" in FY Theorem 2.10's
sense) when it is preserved by `z ↦ −z`. -/
def NegInvariant (F : Measure (AddCircle (2 * π))) : Prop :=
  F.map (fun z => -z) = F

/-- For a negation-invariant finite measure the Fourier coefficients are even in `n`. -/
theorem measureFourierCoeff_neg (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (n : ℤ) :
    measureFourierCoeff F (-n) = measureFourierCoeff F n := by
  sorry

/-- For a negation-invariant finite measure the Fourier coefficients are real. -/
theorem measureFourierCoeff_im (F : Measure (AddCircle (2 * π))) [IsFiniteMeasure F]
    (hF : NegInvariant F) (n : ℤ) :
    (measureFourierCoeff F n).im = 0 := by
  sorry

end StatLean.TimeSeries
