import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exponential Taylor bounds — elementary numeric bricks

Elementary inequalities between polynomials, factorials, and the real
exponential, used throughout the Orlicz cluster:
$$ y \le e^{y/2} \ (y \ge 0), \qquad y^2 \le e^{y} \ (y \ge 0), \qquad
   e^{x} \le 1 + x + \tfrac{x^2}{2}\,e^{|x|}, $$
$$ \frac{x^n}{n!} \le e^{x} \ (x \ge 0), \qquad
   \Bigl(\frac{n}{e}\Bigr)^{n} \le n!. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability: An Introduction
with Applications in Data Science*, 2nd ed., Cambridge University Press. These
are the unnamed numeric steps inside Proposition 2.6.1 ((iii)⇒(iv), (iii)⇒(ii),
(ii)⇒(iii)), Proposition 2.8.1 ((iii)⇒(iv)), and Lemma 1.7.8 ($(n/e)^n \le n!$).

**Proof formalization notes.** Pure real analysis, probability-free
(Mathlib-candidate; this file creates the area's `ForMathlib/` layer, precedent
`HighDimensionalStatistics/ForMathlib/`). All constants are exact — no frozen
numerals. The Taylor–Lagrange bound `exp_le_one_add_add_sq_half_mul_exp_abs`
splits into a series-comparison branch for `x ≥ 0` (via
`Real.sum_le_exp_of_nonneg`) and the alternating-series/convexity branch
`exp_le_one_add_add_sq_half_of_nonpos` for `x ≤ 0`; the latter is this work
item's designated named-sorry fallback. `(n/e)^n ≤ n!` follows from
`x^n/n! ≤ e^x` at `x = n` (backup brick: `Stirling.le_factorial_stirling`).

**Bibliographic comments.** Taylor–Lagrange bounds on the exponential are
classical (Euler). Their systematic use to convert Orlicz-moment conditions
into MGF bounds follows Vershynin (HDP §2.6, §2.8 and the end-of-chapter
Notes) and Buldygin–Kozachenko, *Metric Characterization of Random Variables
and Random Processes*, AMS 2000.
-/

namespace StatLean.ConcentrationInequalities

/-- `y ≤ e^{y/2}` for `y ≥ 0` (HDP §2.6.1 proof step "x² ≤ e^{x²}",
square-root form). -/
theorem le_exp_half {y : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hy : 0 ≤ y) :
    y ≤ Real.exp (y / 2) := by sorry

/-- `y² ≤ e^{y}` for `y ≥ 0` (HDP §2.8.1 proof step "x² ≤ 4e^{|x|/2}",
normalized form; square of `le_exp_half`). -/
theorem sq_le_exp {y : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hy : 0 ≤ y) :
    y ^ 2 ≤ Real.exp y := by sorry

/-- Two-sided Taylor–Lagrange bound `e^x ≤ 1 + x + (x²/2)·e^{|x|}` (HDP
§2.6.1 (iii)⇒(iv) and §2.8.1 (iii)⇒(iv): the split `E e^{λX} ≤ 1 + λEX +
(λ²/2)E X²e^{|λX|}`). For `x ≥ 0` by series comparison
(`Real.sum_le_exp_of_nonneg`); for `x < 0` via
`exp_le_one_add_add_sq_half_of_nonpos`. -/
theorem exp_le_one_add_add_sq_half_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x| := by sorry

/-- Nonpositive branch `e^x ≤ 1 + x + x²/2` for `x ≤ 0` (alternating-series /
convexity argument; helper for `exp_le_one_add_add_sq_half_mul_exp_abs`). -/
theorem exp_le_one_add_add_sq_half_of_nonpos {x : ℝ}
    -- LEAN-ONLY: branch condition of the two-sided Taylor bound; no book scope
    (hx : x ≤ 0) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 := by sorry

/-- Single-term series bound `x^n / n! ≤ e^x` for `x ≥ 0` (HDP §2.6.1
(iii)⇒(ii) even-moment bound; from `Real.sum_le_exp_of_nonneg`). -/
theorem pow_div_factorial_le_exp {x : ℝ}
    -- LEAN-ONLY: nonnegativity of the argument; numeric brick, no book scope
    (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by sorry

/-- `(n/e)^n ≤ n!` (HDP Lemma 1.7.8; used in Prop 2.6.1 (ii)⇒(iii)).
Follows from `pow_div_factorial_le_exp` at `x = n`; backup:
`Stirling.le_factorial_stirling`. -/
theorem pow_div_exp_pow_le_factorial (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by sorry

end StatLean.ConcentrationInequalities
