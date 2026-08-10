import StatLean.RobustStatistics.LocationScale.Median
import StatLean.RobustStatistics.Core.BreakdownPoint

/-!
# Breakdown of the sample median — the maximal-resistance theorem

The flagship finite-sample robustness contrast (`MMY §3.2.5`): for `n = 2k+1`
observations, the sample median resists `k` arbitrary replacements but breaks under
`k+1`, so its breakdown count is exactly `m* = k = ⌊(n-1)/2⌋` — the maximum possible for
any location-equivariant estimator (`MMY` eq. (3.26), `Core/BreakdownPoint.lean`) — while
the sample mean has `m* = 0` (`LocationScale/Mean.lean`).

* `sampleMedian_resists` — with at most `k` replacements, the median stays within the
  range of the original data (via the replacement-perturbation bound
  `orderStat_le_of_hammingDist`).
* `sampleMedian_breaksUnder` — `k+1` replacements placed at a common large value drag
  the median beyond any bound.
* `sampleMedian_breakdownCount` — `m*(Med, x) = k`, hence `ε*_n = k/(2k+1) → 1/2`.
* `sampleMedian_breakdownCount_eq_max` — the median attains the location-equivariant
  maximum `⌊(n-1)/2⌋`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.5 (eq.
(3.24)–(3.26)), §3.8.2.
-/

namespace StatLean.RobustStatistics

variable {n k : ℕ}

/-- **The median resists `k` replacements** (`n = 2k+1`; `MMY §3.2.5`): however at most
`k` observations are replaced, the median of the corrupted sample stays within the range
of the original data, hence bounded. -/
theorem sampleMedian_resists (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    Resists sampleMedian x k := by
  sorry

/-- Quantitative form of the resistance: the corrupted median lies between the smallest
and largest original observations. -/
theorem sampleMedian_mem_Icc_of_hammingDist (hn : n = 2 * k + 1) {x y : Fin n → ℝ}
    (h : hammingDist x y ≤ k) :
    sampleMedian y ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) := by
  sorry

/-- **`k+1` replacements break the median** (`n = 2k+1`; `MMY §3.2.5`): placing `k+1`
observations at a common arbitrarily large value drags the median beyond any bound. -/
theorem sampleMedian_breaksUnder (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    BreaksUnder sampleMedian x (k + 1) := by
  sorry

/-- **The breakdown count of the median is exactly `k`** (`n = 2k+1`; `MMY §3.2.5`):
`m*(Med, x) = k`, so the finite-sample breakdown point is `ε*_n = k/(2k+1) → 1/2`. -/
theorem sampleMedian_breakdownCount (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownCount sampleMedian x = k := by
  sorry

/-- **The median attains the maximal breakdown of location-equivariant estimators**
(`MMY` eq. (3.26)): `m*(Med, x) = ⌊(n-1)/2⌋`, the upper bound of
`locEquivariant_breakdownCount_le`. -/
theorem sampleMedian_breakdownCount_eq_max (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownCount sampleMedian x = (n - 1) / 2 := by
  sorry

/-- The finite-sample breakdown point of the median, `ε*_n = k/(2k+1)`. -/
theorem sampleMedian_breakdownPoint (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    breakdownPoint sampleMedian x = k / (2 * k + 1 : ℝ) := by
  sorry

end StatLean.RobustStatistics
