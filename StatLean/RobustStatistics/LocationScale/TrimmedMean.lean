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

/-! ### The retained index set

The trimmed sum runs over the `n - 2m` retained ranks `m ≤ i < n - m`; the two private
lemmas below compute that cardinality (in `ℕ` and, under `2m < n`, in `ℝ`) once and for
all. -/

/-- The retained ranks are in bijection with `Ico m (n - m)`, so there are `n - 2m` of
them. -/
private theorem card_trim_filter (n m : ℕ) :
    (univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card = n - 2 * m := by
  classical
  have h : (univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card
      = (Finset.Ico m (n - m)).card := by
    refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      exact Finset.mem_Ico.mpr ha
    · intro a _ b _ hab
      exact Fin.val_injective hab
    · intro b hb
      rw [Finset.mem_Ico] at hb
      exact ⟨⟨b, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; omega, rfl⟩
  rw [h, Nat.card_Ico]
  omega

/-- The real-valued cardinality of the retained index set, matching the denominator of
`trimmedMean`. -/
private theorem cast_card_trim {m : ℕ} (hm : 2 * m < n) :
    ((univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m)).card : ℝ)
      = (n : ℝ) - 2 * (m : ℝ) := by
  rw [card_trim_filter, Nat.cast_sub hm.le]
  push_cast
  ring

/-- The denominator of `trimmedMean` is positive when some observations are retained. -/
private theorem trim_denom_pos {m : ℕ} (hm : 2 * m < n) : (0 : ℝ) < (n : ℝ) - 2 * (m : ℝ) := by
  have h1 : ((2 * m : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hm
  push_cast at h1
  linarith

/-- A uniform lower bound on the retained order statistics is a lower bound for the
trimmed mean. -/
private theorem le_trimmedMean_of_forall {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) {a : ℝ}
    (ha : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      a ≤ orderStat x i) :
    a ≤ trimmedMean m x := by
  have hd := trim_denom_pos (n := n) hm
  have hsum := Finset.card_nsmul_le_sum _ (orderStat x) a ha
  rw [nsmul_eq_mul, cast_card_trim hm] at hsum
  simp only [trimmedMean]
  rw [le_div_iff₀ hd]
  linarith [hsum, mul_comm ((n : ℝ) - 2 * (m : ℝ)) a]

/-- A uniform upper bound on the retained order statistics is an upper bound for the
trimmed mean. -/
private theorem trimmedMean_le_of_forall {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) {b : ℝ}
    (hb : ∀ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
      orderStat x i ≤ b) :
    trimmedMean m x ≤ b := by
  have hd := trim_denom_pos (n := n) hm
  have hsum := Finset.sum_le_card_nsmul _ (orderStat x) b hb
  rw [nsmul_eq_mul, cast_card_trim hm] at hsum
  simp only [trimmedMean]
  rw [div_le_iff₀ hd]
  linarith [hsum, mul_comm ((n : ℝ) - 2 * (m : ℝ)) b]

/-! ### Basic properties -/

/-- With no trimming the trimmed mean is the sample mean (`MMY §2.4`, limit case
`α = 0`). -/
theorem trimmedMean_zero (x : Fin n → ℝ) : trimmedMean 0 x = sampleMean x := by
  classical
  have hfilter : (univ.filter (fun i : Fin n => 0 ≤ (i : ℕ) ∧ (i : ℕ) < n - 0)) = univ := by
    refine Finset.filter_true_of_mem fun i _ => ⟨Nat.zero_le _, ?_⟩
    simpa using i.isLt
  simp only [trimmedMean, sampleMean, hfilter, sum_orderStat]
  norm_num

/-- **The trimmed mean is location equivariant** (`MMY §2.4`, eq. (2.43)–(2.46): it is an
L-estimator with weights summing to one). -/
theorem trimmedMean_locEquivariant {m : ℕ} (hm : 2 * m < n) :
    PointEstimation.IsLocEquivariant (trimmedMean (n := n) m) := by
  classical
  intro a x
  have hd := trim_denom_pos (n := n) hm
  have hx : (x + a • (1 : Fin n → ℝ)) = fun j => x j + a := by funext j; simp
  -- Each retained order statistic shifts by `a`, and there are `n - 2m` of them.
  have hsum : ∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m),
        orderStat (fun j => x j + a) i
      = (∑ i ∈ univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < n - m), orderStat x i)
        + ((n : ℝ) - 2 * (m : ℝ)) * a := by
    rw [Finset.sum_congr rfl fun i _ => orderStat_add_const x a i, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, cast_card_trim hm]
  rw [hx]
  simp only [trimmedMean]
  rw [hsum, add_div, mul_div_cancel_left₀ a hd.ne']

/-- The trimmed mean lies between the extreme retained order statistics; in particular it
lies within the range of the data. -/
theorem trimmedMean_mem_Icc {m : ℕ} (hm : 2 * m < n) (x : Fin n → ℝ) :
    trimmedMean m x ∈ Set.Icc (⨅ i, x i) (⨆ i, x i) := by
  classical
  have hbb : BddBelow (Set.range x) := (Set.finite_range x).bddBelow
  have hba : BddAbove (Set.range x) := (Set.finite_range x).bddAbove
  refine ⟨le_trimmedMean_of_forall hm x fun i _ => ?_, trimmedMean_le_of_forall hm x fun i _ => ?_⟩
  · obtain ⟨j, hj⟩ := orderStat_mem_range x i
    rw [← hj]
    exact ciInf_le hbb j
  · obtain ⟨j, hj⟩ := orderStat_mem_range x i
    rw [← hj]
    exact le_ciSup hba j

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
