import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tail bounds for p-series

Summability and an explicit tail estimate for `∑_{m ≥ n} m^{−s}`, `s > 1`:
$$ \sum_{m \ge n} m^{-s} \;\le\; \frac{s}{s-1}\,(n-1)^{1-s} \qquad (n \ge 2). $$

Used to bound the aliasing residual of trigonometric coefficient estimates over Sobolev
ellipsoids (Cauchy–Schwarz turns an ellipsoid membership into a weighted tail `∑ a_m^{-2}`).

**Proof formalization notes.** Standard integral test: `m^{-s} ≤ ∫_{m-1}^m x^{-s} dx` and
summation (`AntitoneOn.sum_le_integral_Ico`-style comparison, or directly via Mathlib's
`sum_rpow`-comparison lemmas if present on the pin); the stated constant `s/(s−1)` is
deliberately generous (the sharp integral-test constant is `1/(s−1)`).

**Bibliographic comments.** Classical (Euler; Maclaurin–Cauchy integral test).
-/

namespace StatLean.NonparametricStatistics

/-- Summability of the shifted p-series `m ↦ (n + m)^{−s}` for `s > 1`. -/
theorem summable_nat_add_rpow_neg {s : ℝ} (hs : 1 < s) (n : ℕ) :
    Summable fun m : ℕ => ((n + m : ℕ) : ℝ) ^ (-s) := by
  sorry

/-- **Tail estimate for p-series**: for `s > 1` and `n ≥ 2`,
`∑_{m≥n} m^{−s} = ∑_{k:ℕ} (n+k)^{−s} ≤ (s/(s−1))·(n−1)^{1−s}`. -/
theorem tsum_nat_add_rpow_neg_le {s : ℝ} (hs : 1 < s) {n : ℕ}
    -- LEAN-ONLY: `n ≥ 2` keeps `(n−1)^{1−s}` a genuine positive power; consumers apply this
    -- with large `n`
    (hn : 2 ≤ n) :
    (∑' m : ℕ, ((n + m : ℕ) : ℝ) ^ (-s)) ≤ s / (s - 1) * ((n : ℝ) - 1) ^ (1 - s) := by
  sorry

end StatLean.NonparametricStatistics
