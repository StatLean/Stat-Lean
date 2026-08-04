import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Fejér–Cesàro sums of a sequence

For `γ : ℤ → ℝ` and `n : ℕ`, the **Fejér–Cesàro sum**
`fejerSum γ n ω = (2πn)⁻¹ Σ_{j,k<n} γ(j−k) e^{−iω(j−k)}
              = (2π)⁻¹ Σ_{|m|<n} (1 − |m|/n) γ(m) e^{−iωm}`
is the density (in `ω ∈ [−π, π]`) of the approximating spectral measures in the proof of
the Herglotz theorem (FY §2.7.4). Key facts stated here:

* the diagonal-collection identity (double sum = Fejér-weighted single sum);
* for even `γ` the sum is real; for positive semidefinite `γ` it is nonnegative — the
  probabilistic positivity `f_n(ω) = Var(Σⱼ e^{−iωj} X_j)/(2πn γ(0)) ≥ 0` of the book,
  obtained here directly from `IsPosSemidefSeq.complex_sum_re_nonneg` with the
  coefficient vector `cⱼ = e^{−iωj}`;
* the trigonometric-moment identity (FY eq. (2.71)):
  `∫_{−π}^{π} e^{ijω} fejerSum γ n ω dω = (1 − |j|/n) γ(j)` for `|j| < n`, `0` otherwise,
  via the basic orthogonality `∫_{−π}^{π} e^{imω} dω = 0` for `m ≠ 0`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.7.4
(pp. 80–81), supporting Theorem 2.10; the same Fejér weights appear in the in-text proof
of Theorem 2.11 (p. 52). (`FY §2.7.4, eq. (2.71)`.)

**Proof formalization notes.** `fejerSum γ 0 ω = 0` by the `(0 : ℝ)⁻¹ = 0` junk
convention (the `n = 0` case never occurs in use). The nonnegativity route deliberately
avoids constructing the random variable `ξ` of the book's proof: positive
semidefiniteness of `γ` is exactly what the variance computation extracts, so we take it
as the hypothesis.

**Bibliographic comments.** Fejér's kernel and the Cesàro summation of Fourier series are
L. Fejér, "Untersuchungen über Fouriersche Reihen", *Math. Ann.* **58** (1904), 51–69.
Their use to prove Herglotz's theorem is classical; the book follows Brockwell & Davis
(1991), pp. 118–119.
-/

open scoped Real
open Finset

namespace StatLean.TimeSeries

/-- The **Fejér–Cesàro sum** `(2πn)⁻¹ Σ_{j,k<n} γ(j−k) e^{−iω(j−k)}` (FY §2.7.4).
Junk value `0` at `n = 0`. -/
noncomputable def fejerSum (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) : ℂ :=
  (((2 * π * n)⁻¹ : ℝ) : ℂ) * ∑ j ∈ range n, ∑ k ∈ range n,
    (γ ((j : ℤ) - (k : ℤ)) : ℂ) *
      Complex.exp (-(Complex.I * (ω : ℂ) * (((j : ℤ) - (k : ℤ) : ℤ) : ℂ)))

/-- Diagonal collection: the Fejér double sum equals the weighted single sum
`(2πn)⁻¹ Σ_{|m|<n} (n − |m|) γ(m) e^{−iωm}` (the display below FY eq. (2.71)). -/
theorem fejerSum_eq_weighted (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) :
    fejerSum γ n ω = (((2 * π * n)⁻¹ : ℝ) : ℂ) *
      ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        ((((n : ℤ) - |m|) : ℤ) : ℂ) * (γ m : ℂ) *
          Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ))) := by
  sorry

/-- For even `γ` the Fejér sum is real. -/
theorem fejerSum_im (γ : ℤ → ℝ) (heven : ∀ k, γ (-k) = γ k) (n : ℕ) (ω : ℝ) :
    (fejerSum γ n ω).im = 0 := by
  sorry

/-- **Fejér positivity**: for an even positive semidefinite `γ`, the Fejér sum is
nonnegative (FY §2.7.4: `f_n(ω) = Var(ξ) ≥ 0`). -/
theorem fejerSum_re_nonneg (γ : ℤ → ℝ) (h : IsPosSemidefSeq γ)
    (heven : ∀ k, γ (-k) = γ k) (n : ℕ) (ω : ℝ) :
    0 ≤ (fejerSum γ n ω).re := by
  sorry

/-- Basic orthogonality on `[−π, π]`: `∫_{−π}^{π} e^{imω} dω = 0` for a nonzero integer
`m` (the engine of FY eq. (2.71) and of the inversion computations of §2.3.2). -/
theorem integral_exp_int_mul_I_eq_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ ω in (-π : ℝ)..π, Complex.exp (Complex.I * (ω : ℂ) * (m : ℂ)) = 0 := by
  sorry

/-- Trigonometric moments of the Fejér sum, in-range case (FY eq. (2.71)):
`∫_{−π}^{π} e^{ijω} fejerSum γ n ω dω = ((n − |j|)/n) γ(j)` for `|j| < n`. -/
theorem integral_fejerSum_mul_exp_of_lt (γ : ℤ → ℝ) {n : ℕ} {j : ℤ} (hj : |j| < (n : ℤ)) :
    ∫ ω in (-π : ℝ)..π,
        fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ))
      = (((((n : ℤ) - |j|) : ℤ) : ℂ) / (n : ℂ)) * (γ j : ℂ) := by
  sorry

/-- Trigonometric moments of the Fejér sum, out-of-range case (FY eq. (2.71)):
the integral vanishes for `|j| ≥ n`. -/
theorem integral_fejerSum_mul_exp_of_le (γ : ℤ → ℝ) {n : ℕ} {j : ℤ}
    (hj : (n : ℤ) ≤ |j|) :
    ∫ ω in (-π : ℝ)..π,
        fejerSum γ n ω * Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ)) = 0 := by
  sorry

end StatLean.TimeSeries
