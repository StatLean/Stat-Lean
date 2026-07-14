import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
import StatLean.NonparametricStatistics.ForMathlib.TaylorLagrangeTwoSided

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

/-- Global Hölder classes see through `iteratedDerivWithin univ = iteratedDeriv`: the top
derivative satisfies the Hölder bound globally. -/
theorem MemHolder.iteratedDeriv_holder {β L : ℝ} {f : ℝ → ℝ} (hf : MemHolder β L f)
    (x y : ℝ) :
    |iteratedDeriv (holderIndex β) f x - iteratedDeriv (holderIndex β) f y|
      ≤ L * |x - y| ^ (β - (holderIndex β : ℝ)) := by
  sorry

/-- **Taylor remainder bound over a global Hölder class**: for `f ∈ Σ(β, L)` on `ℝ`,
`|f(x₀+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x₀)tʲ/j!| ≤ (L/ℓ!)·|t|^β` with `ℓ = holderIndex β`. -/
theorem MemHolder.taylor_remainder_abs_le {β L : ℝ}
    -- USER-INPUT: positive smoothness and Hölder constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemHolder β L f) (x₀ t : ℝ) :
    |f (x₀ + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ)|
      ≤ L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β := by
  sorry

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
  sorry

end StatLean.NonparametricStatistics
