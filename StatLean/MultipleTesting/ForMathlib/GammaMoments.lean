import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.Basic

/-!
# Moment generating function, mean, variance of the Gamma distribution — ForMathlib brick

Closed forms for `Gamma(a, r)` (Mathlib's `gammaMeasure a r`: shape `a`, rate `r`, density
`r^a/Γ(a) · x^{a-1} e^{-rx}` on `x ≥ 0`), the inputs to identifying the chi-squared law
`χ²ₖ := Gamma(k/2, 1/2)`:

* `mgf_gammaMeasure` — `E[e^{tX}] = (r/(r−t))^a` for `t < r` (the brick the χ²-law identification
  uses: at rate `r = 1/2` this is `(1−2t)^{−a}`, matching the squared-Gaussian MGF);
* `integral_id_gammaMeasure` — `E[X] = a/r`;
* `variance_gammaMeasure` — `Var[X] = E[(X − a/r)²] = a/r²`.

Theorem-agnostic. Consumed by `ForMathlib/ChiSquared.lean` (the χ²ₖ definition and the
sum-of-squares law) in the chi-squared test development (Candès, Lecture 2, §2.3).

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory Real

namespace StatLean.MultipleTesting

/-- **MGF of `Gamma(a, r)`**: `E[e^{tX}] = (r/(r−t))^a` for `t < r` (`0 < a`, `0 < r`). At rate
`r = 1/2` this is `(1−2t)^{−a}`, the form the χ²-law identification matches against. -/
theorem mgf_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂(gammaMeasure a r) = (r / (r - t)) ^ a := by
  sorry

/-- **Mean of `Gamma(a, r)`**: `E[X] = a/r` (`0 < a`, `0 < r`). -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂(gammaMeasure a r) = a / r := by
  sorry

/-- **Variance of `Gamma(a, r)`**: `E[(X − a/r)²] = a/r²` (`0 < a`, `0 < r`). -/
theorem variance_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, (x - a / r) ^ 2 ∂(gammaMeasure a r) = a / r ^ 2 := by
  sorry

end StatLean.MultipleTesting
