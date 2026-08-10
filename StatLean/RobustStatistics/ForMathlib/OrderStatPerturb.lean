import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Perm

/-!
# Order statistics under affine maps and coordinate replacement — `ForMathlib` layer

Theorem-agnostic bricks about the order statistics `orderStat v i = v (Tuple.sort v i)`
(reused from `StatLean.MultipleTesting.ForMathlib.OrderStatistics`): counting
characterizations, behaviour under affine transformations of the data, and the
*replacement-perturbation* bound — changing at most `m` coordinates of a tuple moves each
order statistic by at most `m` index positions. The perturbation bound is the combinatorial
engine behind the finite-sample breakdown analysis of the median and the trimmed mean
(`MMY §3.2.5`), but the statements here are pure finite combinatorics on real tuples, with
no statistical content.

* `sum_orderStat` — order statistics are a permutation of the data, so sums agree.
* `orderStat_nonneg`, `orderStat_mem_range` — pointwise range facts.
* `card_le_orderStat_le`, `card_orderStat_le` — counting characterizations: at least `i + 1`
  entries are `≤ v₍ᵢ₎` and at least `n - i` entries are `≥ v₍ᵢ₎`.
* `le_orderStat_of_card_le`, `orderStat_le_of_card_le` — converse counting bounds.
* `orderStat_add_const`, `orderStat_const_mul_of_nonneg`, `orderStat_neg` — equivariance of
  order statistics under monotone affine maps (with index reversal `Fin.rev` for negation).
* `orderStat_le_of_hammingDist` — the replacement-perturbation bound.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) The perturbation
bound is implicit in the finite-sample breakdown computations of `MMY §3.2.5`.
-/

open Finset

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting

variable {n : ℕ} (v : Fin n → ℝ)

/-! ### Order statistics as a rearrangement -/

/-- The order statistics are a permutation of the data: sums agree. -/
theorem sum_orderStat : ∑ i, orderStat v i = ∑ i, v i := by
  sorry

/-- Order statistics of a nonnegative tuple are nonnegative. -/
theorem orderStat_nonneg (hv : ∀ i, 0 ≤ v i) (i : Fin n) : 0 ≤ orderStat v i := by
  sorry

/-- Every order statistic is one of the data values. -/
theorem orderStat_mem_range (i : Fin n) : orderStat v i ∈ Set.range v := by
  sorry

/-! ### Counting characterizations -/

/-- At least `i + 1` data values are `≤` the `i`-th order statistic. -/
theorem card_le_orderStat_le (i : Fin n) :
    (i : ℕ) + 1 ≤ (univ.filter fun j => v j ≤ orderStat v i).card := by
  sorry

/-- At least `n - i` data values are `≥` the `i`-th order statistic. -/
theorem card_orderStat_le (i : Fin n) :
    n - (i : ℕ) ≤ (univ.filter fun j => orderStat v i ≤ v j).card := by
  sorry

/-- Converse counting bound: if at least `i + 1` data values are `≤ t`, then the `i`-th
order statistic is `≤ t`. -/
theorem orderStat_le_of_card_le (i : Fin n) (t : ℝ)
    (h : (i : ℕ) + 1 ≤ (univ.filter fun j => v j ≤ t).card) :
    orderStat v i ≤ t := by
  sorry

/-- Converse counting bound: if at least `n - i` data values are `≥ t`, then the `i`-th
order statistic is `≥ t`. -/
theorem le_orderStat_of_card_le (i : Fin n) (t : ℝ)
    (h : n - (i : ℕ) ≤ (univ.filter fun j => t ≤ v j).card) :
    t ≤ orderStat v i := by
  sorry

/-! ### Equivariance under monotone affine maps -/

/-- Order statistics commute with adding a constant. -/
theorem orderStat_add_const (a : ℝ) (i : Fin n) :
    orderStat (fun j => v j + a) i = orderStat v i + a := by
  sorry

/-- Order statistics commute with multiplication by a nonnegative constant. -/
theorem orderStat_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (i : Fin n) :
    orderStat (fun j => c * v j) i = c * orderStat v i := by
  sorry

/-- Negation reverses order statistics: the `i`-th smallest of `-v` is minus the `i`-th
largest of `v`. -/
theorem orderStat_neg (i : Fin n) :
    orderStat (fun j => -v j) i = -orderStat v i.rev := by
  sorry

/-! ### The replacement-perturbation bound

Changing at most `m` coordinates moves each order statistic by at most `m` index
positions. This single inequality (applied twice, via `hammingDist_comm`) yields both the
resistance of the median to `⌊(n-1)/2⌋` replacements and the resistance of the `m`-trimmed
mean to `m` replacements. -/

/-- **Replacement-perturbation bound.** If `x` and `y` differ in at most `m` coordinates
and `j + m ≤ i`, then the `j`-th order statistic of `x` is `≤` the `i`-th order statistic
of `y`. -/
theorem orderStat_le_of_hammingDist {x y : Fin n → ℝ} {m : ℕ}
    (h : hammingDist x y ≤ m) {i j : Fin n} (hij : (j : ℕ) + m ≤ i) :
    orderStat x j ≤ orderStat y i := by
  sorry

end StatLean.RobustStatistics
