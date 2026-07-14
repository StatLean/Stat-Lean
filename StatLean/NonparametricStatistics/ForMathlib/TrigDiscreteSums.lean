import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Discrete sums of cosines and sines at rational frequencies

The exact values of `∑_{s=1}^{n} cos(2πms/n)` and `∑_{s=1}^{n} sin(2πms/n)`:
both vanish when `n ∤ m`; the cosine sum equals `n` (and the sine sum `0`) when `n ∣ m`.

These are the arithmetic engine behind the discrete orthonormality of the trigonometric system
at the regular design — the fact that makes coefficient estimates at design points behave like
genuine Fourier coefficients.

**Proof formalization notes.** Pass to the complex exponential: the sums are the real and
imaginary parts of the geometric sum `∑_{s=1}^n ζ^s` with `ζ = exp(2πi·m/n)`. For `n ∤ m` one
has `ζ ≠ 1` and `ζ^n = 1`, so `∑_{s=0}^{n-1} ζ^s = (ζ^n − 1)/(ζ − 1) = 0`
(`Finset.geom_sum_eq`), and the `1..n` sum is `ζ` times the `0..n−1` sum. For `n ∣ m`, every
term is `1` (resp. `0`). Key Mathlib pieces: `Complex.exp_int_mul_two_pi_mul_I`,
`Complex.exp_re`/`exp_ofReal_mul_I_re`, `Finset.geom_sum_eq`.

**Bibliographic comments.** Classical roots-of-unity identities (Gauss).
-/

open scoped Real

namespace StatLean.NonparametricStatistics

/-- `∑_{s=1}^{n} cos(2π·m·s/n) = 0` when `n ∤ m`. -/
theorem sum_cos_two_pi_mul_div_eq_zero {n m : ℕ} (hm : ¬ (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * m * (s + 1) / n) = 0 := by
  sorry

/-- `∑_{s=1}^{n} sin(2π·m·s/n) = 0` when `n ∤ m`. -/
theorem sum_sin_two_pi_mul_div_eq_zero {n m : ℕ} (hm : ¬ (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * m * (s + 1) / n) = 0 := by
  sorry

/-- `∑_{s=1}^{n} cos(2π·m·s/n) = n` when `n ∣ m` (every angle is a multiple of `2π`). -/
theorem sum_cos_two_pi_mul_div_of_dvd {n m : ℕ} (hm : (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.cos (2 * Real.pi * m * (s + 1) / n) = n := by
  sorry

/-- `∑_{s=1}^{n} sin(2π·m·s/n) = 0` when `n ∣ m` (every angle is a multiple of `2π`). -/
theorem sum_sin_two_pi_mul_div_of_dvd {n m : ℕ} (hm : (n : ℤ) ∣ (m : ℤ)) :
    ∑ s ∈ Finset.range n, Real.sin (2 * Real.pi * m * (s + 1) / n) = 0 := by
  sorry

end StatLean.NonparametricStatistics
