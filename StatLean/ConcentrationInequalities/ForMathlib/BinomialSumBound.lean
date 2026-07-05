import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Truncated binomial sum bound `∑_{k ≤ d} C(n,k) ≤ (en/d)^d`

For natural numbers $1 \le d \le n$,
$$ \sum_{k=0}^{d} \binom{n}{k} \;\le\; \Bigl(\frac{e\,n}{d}\Bigr)^{d}. $$
This is the classical closed-form bound on the truncated binomial sum that
turns the Sauer–Shelah counting lemma into the polynomial growth bound used
throughout VC theory.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Exercise 0.6 (used in §8.3.3, Lemma 8.3.9,
second inequality).

**Proof formalization notes.** Absent from Mathlib (brick check). Proof plan:
multiply by $(d/n)^d \le (d/n)^k$ (for $k \le d$, since $d/n \le 1$), bound
the resulting sum by the full binomial expansion of $(1 + d/n)^n$ via
`add_pow` + `Finset.sum_le_sum_of_subset_of_nonneg`, then
$(1 + d/n)^n \le e^d$ from `Real.add_one_le_exp`. The constant is exactly
the book's $e = $ `Real.exp 1`; no numeric slack is taken here. Edge
behavior: the hypothesis `1 ≤ d` rules out the degenerate `0^0` division;
`d ≤ n` is the book's stated regime (the bound is false for `d > n` as
stated, e.g. `n = 1, d = 2`). Pure real algebra, zero probability content;
candidate upstream. Named-sorry fallback of this work item:
`sum_choose_le_exp_mul_pow` (already in final consumable form).

**Bibliographic comments.** The bound is folklore in combinatorics and
statistical learning theory; it appears as the standard companion to the
Sauer–Shelah lemma (N. Sauer, *J. Combin. Theory Ser. A* 13 (1972), 145–147;
S. Shelah, *Pacific J. Math.* 41 (1972), 247–261) — see HDP §8.3 Notes and
Exercise 0.6.
-/

open Finset

namespace StatLean.ConcentrationInequalities

/-- Truncated binomial theorem: for `0 ≤ x`, the sum of the first `d + 1`
terms of the binomial expansion of `(1 + x)^n` is at most the whole
expansion. -/
lemma sum_choose_mul_pow_le_one_add_pow {n d : ℕ}
    -- LEAN-ONLY: truncation range fits inside the expansion range; pure
    -- algebra, no book content.
    (hdn : d ≤ n) {x : ℝ}
    -- LEAN-ONLY: nonnegativity so dropped binomial terms are nonnegative.
    (hx0 : 0 ≤ x) :
    ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) * x ^ k ≤ (1 + x) ^ n := by
  sorry

/-- `(1 + d/n)^n ≤ e^d`, from `Real.add_one_le_exp` applied at `d/n`. -/
lemma one_add_div_pow_le_exp {n d : ℕ}
    -- LEAN-ONLY: positivity of the denominator; pure algebra.
    (hn : 0 < n) :
    ((1 : ℝ) + (d : ℝ) / (n : ℝ)) ^ n ≤ Real.exp d := by
  sorry

/-- **Truncated binomial sum bound** (HDP Exercise 0.6; used in §8.3.3,
Lemma 8.3.9): for `1 ≤ d ≤ n`,
`∑_{k ≤ d} C(n,k) ≤ (e·n/d)^d` with `e = Real.exp 1`. -/
theorem sum_choose_le_exp_mul_pow {n d : ℕ}
    -- USER-INPUT: 1 ≤ d (nondegenerate dimension); HDP Exercise 0.6.
    (hd1 : 1 ≤ d)
    -- USER-INPUT: d ≤ n (the book's stated regime; the bound fails above the
    -- diagonal); HDP Exercise 0.6.
    (hdn : d ≤ n) :
    (∑ k ∈ Finset.Iic d, (n.choose k : ℝ)) ≤ (Real.exp 1 * n / d) ^ d := by
  sorry

end StatLean.ConcentrationInequalities
