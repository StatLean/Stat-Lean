import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.PointEstimation.Equivariance.Defs

/-!
# The trimmed mean

The `m`-trimmed mean discards the `m` smallest and `m` largest observations and averages
the rest (`MMY §2.4`, the α-trimmed mean with `m = [nα]`):

$$\bar x_{(m)} = \frac{1}{n-2m} \sum_{i=m}^{n-m-1} x_{(i)},$$

interpolating between the sample mean (`m = 0`) and the median (`m → ⌊(n-1)/2⌋`). Its
finite-sample robustness — resistance to `m` replacements — follows from the
replacement-perturbation bound on order statistics
(`ForMathlib/OrderStatPerturb.lean`), matching `m* = [nα]` in `MMY §3.2.5`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.4 (trimmed
and Winsorized means), §3.2.5 (their breakdown).
-/

open StatLean.MultipleTesting Finset

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **`m`-trimmed mean** (`MMY §2.4`): the average of the order statistics with the
`m` smallest and `m` largest observations removed. Junk value `0` when `n ≤ 2m` (empty
trimmed sum or division by `0`). -/
noncomputable def trimmedMean (m : ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m), orderStat x i) /
    (n - 2 * m : ℝ)

/-- With no trimming the trimmed mean is the sample mean (`MMY §2.4`, limit case
`α = 0`). -/
theorem trimmedMean_zero (x : Fin n → ℝ) : trimmedMean 0 x = sampleMean x := by
  sorry

/-- **The trimmed mean is location equivariant** (`MMY §2.4`, eq. (2.43)–(2.46): it is an
L-estimator with weights summing to one). -/
theorem trimmedMean_locEquivariant {m : ℕ} (hm : 2 * m < n) :
    PointEstimation.IsLocEquivariant (trimmedMean (n := n) m) := by
  sorry

/-- The trimmed mean lies between the extreme retained order statistics; in particular it
lies within the range of the data. -/
theorem trimmedMean_mem_Icc {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    trimmedMean m x ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) := by
  sorry

/-- **The trimmed mean resists `m` replacements** (`MMY §3.2.5`: `m* = [nα]` for the
α-trimmed mean): every retained order statistic of the corrupted sample stays within the
range of the original data, by the replacement-perturbation bound. -/
theorem trimmedMean_resists {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    Resists (trimmedMean m) x m := by
  sorry

/-- **`m+1` replacements break the `m`-trimmed mean** (`MMY §3.2.5`): one extreme value
survives the trimming. -/
theorem trimmedMean_breaksUnder {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    BreaksUnder (trimmedMean m) x (m + 1) := by
  sorry

/-- **The breakdown count of the `m`-trimmed mean is exactly `m`**
(`MMY §3.2.5`: `m* = [nα]`). -/
theorem trimmedMean_breakdownCount {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    breakdownCount (trimmedMean m) x = m := by
  sorry

end StatLean.RobustStatistics
