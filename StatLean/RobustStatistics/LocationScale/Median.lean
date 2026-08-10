import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
import StatLean.PointEstimation.Equivariance.Defs

/-!
# The sample median

The sample median as an order statistic: for `n = 2k+1` observations the median is the
`(k+1)`-th smallest value (`MMY §1.2, §2.3.1`). For even `n` this file adopts the *low
median* (the `⌊(n-1)/2⌋`-th order statistic, `0`-indexed), one of the two conventions the
book allows (`MMY §4.5.1`: "the median must be understood as the 'high' or 'low' median");
all headline robustness theorems are stated for odd `n`, where the conventions coincide.

* `sampleMedian` — the `⌊(n-1)/2⌋`-th order statistic (`0`-indexed); junk value `0` for
  `n = 0`.
* counting characterizations: at least half the data on each side.
* equivariance: location equivariance, and full scale equivariance `Med(cx) = c·Med(x)`
  for odd `n` (index reversal fixes the middle index).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §1.2, §2.3.1
(eq. (2.18), (2.21): the median as the L¹ location estimate), §4.5.1 (high/low median).
-/

open StatLean.MultipleTesting Finset

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **sample median** (`MMY §1.2`): the `⌊(n-1)/2⌋`-th order statistic (`0`-indexed).
For odd `n = 2k+1` this is the `(k+1)`-th smallest observation; for even `n` it is the
*low* median (`MMY §4.5.1`). Junk value `0` when `n = 0`. -/
noncomputable def sampleMedian (x : Fin n → ℝ) : ℝ :=
  if h : n = 0 then 0 else orderStat x ⟨(n - 1) / 2, by omega⟩

/-- Unfolding lemma for nonempty samples. -/
theorem sampleMedian_eq_orderStat (hn : n ≠ 0) (x : Fin n → ℝ) :
    sampleMedian x = orderStat x ⟨(n - 1) / 2, by omega⟩ := by
  sorry

/-- For odd `n = 2k+1` the median is the `(k+1)`-th smallest observation (index `k`,
`0`-indexed). -/
theorem sampleMedian_odd {k : ℕ} (hn : n = 2 * k + 1) (x : Fin n → ℝ) :
    sampleMedian x = orderStat x ⟨k, by omega⟩ := by
  sorry

/-- The median is one of the data values. -/
theorem sampleMedian_mem_range (hn : n ≠ 0) (x : Fin n → ℝ) :
    sampleMedian x ∈ Set.range x := by
  sorry

/-! ### Counting characterizations (`MMY §2.3.1`, eq. (2.21) context) -/

/-- At least half the observations (strictly more than `(n-1)/2`, i.e. `⌊(n-1)/2⌋ + 1`)
are `≤` the median. -/
theorem card_le_sampleMedian (hn : n ≠ 0) (x : Fin n → ℝ) :
    (n - 1) / 2 + 1 ≤ (univ.filter fun j => x j ≤ sampleMedian x).card := by
  sorry

/-- At least half the observations are `≥` the median. -/
theorem card_sampleMedian_le (hn : n ≠ 0) (x : Fin n → ℝ) :
    n - (n - 1) / 2 ≤ (univ.filter fun j => sampleMedian x ≤ x j).card := by
  sorry

/-! ### Equivariance -/

/-- **The sample median is location equivariant** (`MMY §2.3.1`). -/
theorem sampleMedian_locEquivariant :
    PointEstimation.IsLocEquivariant (sampleMedian (n := n)) := by
  sorry

/-- For nonnegative scalars the median is scale equivariant (any `n`). -/
theorem sampleMedian_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) :
    sampleMedian (fun i => c * x i) = c * sampleMedian x := by
  sorry

/-- **For odd `n` the median is fully scale equivariant**, `Med(cx) = c·Med(x)` for every
`c : ℝ` (`MMY §2.3.1`): negation reverses the order statistics, and for odd `n` the middle
index is a fixed point of the reversal. -/
theorem sampleMedian_const_mul_of_odd {k : ℕ} (hn : n = 2 * k + 1) (c : ℝ)
    (x : Fin n → ℝ) :
    sampleMedian (fun i => c * x i) = c * sampleMedian x := by
  sorry

/-- Median of a constant sample. -/
theorem sampleMedian_const (hn : n ≠ 0) (a : ℝ) :
    sampleMedian (fun _ : Fin n => a) = a := by
  sorry

end StatLean.RobustStatistics
