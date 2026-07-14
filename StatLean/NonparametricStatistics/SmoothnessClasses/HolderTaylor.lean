import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
import StatLean.NonparametricStatistics.ForMathlib.TaylorLagrangeTwoSided
import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor remainder bounds over Hölder classes

The one inequality that drives every pointwise bias bound in this area: for `f` in the Hölder
class `Σ(β, L)` and `ℓ = holderIndex β`,
$$ \Bigl|f(x_0+t) - \sum_{j=0}^{\ell} \frac{f^{(j)}(x_0)}{j!}t^j\Bigr|
   \;\le\; \frac{L}{\ell!}\,|t|^{\beta}. $$
(The sum includes the `ℓ`-th term; Taylor–Lagrange leaves the remainder
`(f^{(ℓ)}(x₀+τt) − f^{(ℓ)}(x₀))·t^ℓ/ℓ!`, which the Hölder condition bounds by
`(L/ℓ!)·|τt|^{β−ℓ}·|t|^ℓ ≤ (L/ℓ!)·|t|^β`.)

Provided in a global form (class on `ℝ`, for kernel density bias) and an interval form (class
on `Icc a b`, for local polynomial bias), plus a polynomial-growth envelope used to derive
integrability of kernel-weighted compositions.

**Proof formalization notes.** The `ℓ = 0` case is the Hölder condition itself (no Taylor
step). For `ℓ ≥ 1`, the global form uses `taylor_lagrange_global`; the interval form uses
Mathlib's `taylor_mean_remainder_lagrange` on `uIcc x₀ x` together with
`iteratedDerivWithin`-monotonicity lemmas to move between `uIcc x₀ x ⊆ Icc a b`. The exponent
algebra `|t|^ℓ·|t|^{β−ℓ} = |t|^β` is `Real.rpow_natCast`/`rpow_add` (with `t = 0` handled
separately).

**Bibliographic comments.** This bias-controlling inequality is the classical smoothness
computation of kernel estimation, in the form used since E. Parzen, *Ann. Math. Statist.*
**33** (1962), 1065–1076.
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

/-- For `0 < β`, the ceiling `⌈β⌉₊` is at least one, so `holderIndex β = ⌈β⌉₊ - 1` is honest. -/
private lemma one_le_ceil {β : ℝ} (hβ : 0 < β) : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ

/-- The smoothness index is strictly below `β`: `(holderIndex β : ℝ) < β`. -/
private lemma holderIndex_lt_self {β : ℝ} (hβ : 0 < β) : (holderIndex β : ℝ) < β := by
  have h1 : 1 ≤ ⌈β⌉₊ := one_le_ceil hβ
  unfold holderIndex
  rw [Nat.cast_sub h1, Nat.cast_one]
  have h2 : (⌈β⌉₊ : ℝ) < β + 1 := Nat.ceil_lt_add_one hβ.le
  linarith

/-- The fractional exponent `β − holderIndex β` is positive. -/
private lemma sub_holderIndex_pos {β : ℝ} (hβ : 0 < β) : 0 < β - (holderIndex β : ℝ) :=
  sub_pos.mpr (holderIndex_lt_self hβ)

/-- Exponent splitter: `|t|^ℓ · |t|^(β−ℓ) = |t|^β` for `t ≠ 0` (natural power times rpow). -/
private lemma abs_rpow_split {β : ℝ} {t : ℝ} (ht : t ≠ 0) (ℓ : ℕ) :
    |t| ^ ℓ * |t| ^ (β - (ℓ : ℝ)) = |t| ^ β := by
  rw [← Real.rpow_natCast |t| ℓ, ← Real.rpow_add (abs_pos.mpr ht)]
  congr 1; ring

/-- Global Hölder classes see through `iteratedDerivWithin univ = iteratedDeriv`: the top
derivative satisfies the Hölder bound globally. -/
theorem MemHolder.iteratedDeriv_holder {β L : ℝ} {f : ℝ → ℝ} (hf : MemHolder β L f)
    (x y : ℝ) :
    |iteratedDeriv (holderIndex β) f x - iteratedDeriv (holderIndex β) f y|
      ≤ L * |x - y| ^ (β - (holderIndex β : ℝ)) := by
  have h := MemHolderOn.deriv_holder hf x (Set.mem_univ x) y (Set.mem_univ y)
  simpa only [iteratedDerivWithin_univ] using h

/-- **Taylor remainder bound over a global Hölder class**: for `f ∈ Σ(β, L)` on `ℝ`,
`|f(x₀+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x₀)tʲ/j!| ≤ (L/ℓ!)·|t|^β` with `ℓ = holderIndex β`. -/
theorem MemHolder.taylor_remainder_abs_le {β L : ℝ}
    -- USER-INPUT: positive smoothness and Hölder constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolder β L f) (x₀ t : ℝ) :
    |f (x₀ + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)|
      ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
  rcases Nat.eq_zero_or_pos (holderIndex β) with hℓ0 | hℓpos
  · -- `ℓ = 0`: the bound is the Hölder condition itself.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)) = f x₀ := by
      rw [hℓ0, zero_add, Finset.sum_range_one]; simp
    rw [hsum, hℓ0]
    have hh := hf.iteratedDeriv_holder (x₀ + t) x₀
    rw [hℓ0] at hh
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, add_sub_cancel_left,
      Nat.factorial_zero, Nat.cast_one, div_one] at hh ⊢
    exact hh
  rcases eq_or_ne t 0 with rfl | ht
  · -- `ℓ ≥ 1`, `t = 0`: both sides vanish.
    have hsum : (∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * (0 : ℝ) ^ j / (Nat.factorial j : ℝ)) = f x₀ := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj; simp [zero_pow hj]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
    rw [add_zero, hsum, sub_self]
    simp [Real.zero_rpow hβ.ne']
  · -- `ℓ ≥ 1`, `t ≠ 0`: Taylor–Lagrange leaves a top-derivative difference; bound by Hölder.
    obtain ⟨τ, hτ, heq⟩ :=
      taylor_lagrange_global hℓpos (contDiffOn_univ.mp (MemHolderOn.contDiffOn hf)) x₀ t ht
    have hdiff : f (x₀ + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
          iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)
        = (iteratedDeriv (holderIndex β) f (x₀ + τ * t)
              - iteratedDeriv (holderIndex β) f x₀)
            * t ^ (holderIndex β) / (Nat.factorial (holderIndex β) : ℝ) := by
      rw [Finset.sum_range_succ, heq]; ring
    have hfac : (0 : ℝ) < (Nat.factorial (holderIndex β) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hA : |iteratedDeriv (holderIndex β) f (x₀ + τ * t)
          - iteratedDeriv (holderIndex β) f x₀|
        ≤ L * |t| ^ (β - (holderIndex β : ℝ)) := by
      have h1 := hf.iteratedDeriv_holder (x₀ + τ * t) x₀
      rw [add_sub_cancel_left] at h1
      refine h1.trans ?_
      apply mul_le_mul_of_nonneg_left _ hL
      apply Real.rpow_le_rpow (abs_nonneg _) _ (le_of_lt (sub_holderIndex_pos hβ))
      rw [abs_mul]
      have hτle : |τ| ≤ 1 := by rw [abs_of_pos hτ.1]; exact le_of_lt hτ.2
      calc |τ| * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hτle (abs_nonneg _)
        _ = |t| := one_mul _
    rw [hdiff, abs_div, abs_mul, abs_pow, abs_of_pos hfac]
    calc |iteratedDeriv (holderIndex β) f (x₀ + τ * t) - iteratedDeriv (holderIndex β) f x₀|
            * |t| ^ (holderIndex β) / (Nat.factorial (holderIndex β) : ℝ)
        ≤ (L * |t| ^ (β - (holderIndex β : ℝ))) * |t| ^ (holderIndex β)
            / (Nat.factorial (holderIndex β) : ℝ) := by gcongr
      _ = L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
          have hsplit : |t| ^ (holderIndex β) * |t| ^ (β - (holderIndex β : ℝ)) = |t| ^ β :=
            abs_rpow_split ht (holderIndex β)
          rw [← hsplit]; ring

/-- **Taylor remainder bound over a Hölder class on an interval**: for `f ∈ Σ(β, L)` on
`[a, b]` and `x, y ∈ [a, b]`,
`|f(y) − ∑_{j≤ℓ} f⁽ʲ⁾(x)(y−x)ʲ/j!| ≤ (L/ℓ!)·|y−x|^β` (derivatives within `[a, b]`). -/
theorem MemHolderOn.taylor_remainder_abs_le_Icc {β L a b : ℝ}
    -- LEAN-ONLY: nondegenerate interval, so `Icc a b` has unique differentiability
    (hab : a < b)
    -- USER-INPUT: positive smoothness and Hölder constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolderOn β L f (Set.Icc a b))
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |f y - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDerivWithin j f (Set.Icc a b) x * (y - x) ^ j / (Nat.factorial j : ℝ)|
      ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |y - x| ^ β := by
  sorry

/-- **Polynomial-growth envelope of a global Hölder function**: with `ℓ = holderIndex β`,
`|f(x₀+t)| ≤ ∑_{j≤ℓ} |f⁽ʲ⁾(x₀)|·|t|ʲ/j! + (L/ℓ!)·|t|^β`. Used to derive integrability of
kernel-weighted compositions `u ↦ K(u)·f(x₀+uh)` from the kernel's moment integrability. -/
theorem MemHolder.abs_le_growth {β L : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolder β L f) (x₀ t : ℝ) :
    |f (x₀ + t)| ≤ (∑ j ∈ Finset.range (holderIndex β + 1),
        |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ))
      + L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
  set S := ∑ j ∈ Finset.range (holderIndex β + 1),
      iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ) with hS
  have h1 : |f (x₀ + t) - S| ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β :=
    hf.taylor_remainder_abs_le hβ hL x₀ t
  have h2 : |S| ≤ ∑ j ∈ Finset.range (holderIndex β + 1),
      |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ) := by
    rw [hS]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl (fun j _ => ?_))
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
  calc |f (x₀ + t)| = |(f (x₀ + t) - S) + S| := by congr 1; ring
    _ ≤ |f (x₀ + t) - S| + |S| := abs_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (holderIndex β + 1),
          |iteratedDeriv j f x₀| * |t| ^ j / (Nat.factorial j : ℝ))
        + L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
        rw [add_comm (|f (x₀ + t) - S|)]; exact add_le_add h2 h1

end StatLean.NonparametricStatistics
