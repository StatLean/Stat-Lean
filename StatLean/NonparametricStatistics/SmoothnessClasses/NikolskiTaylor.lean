import StatLean.NonparametricStatistics.SmoothnessClasses.Defs
import StatLean.NonparametricStatistics.ForMathlib.TaylorIntegralRemainder
import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral

/-!
# Taylor remainder bounds over Nikol'skii classes (L² form)

The `L²` analogue of the Hölder–Taylor bound, driving the *integrated* bias analysis: for `f`
in the Nikol'skii class `H(β, L)` and `ℓ = holderIndex β`,
$$ \Bigl\|\,f(\cdot+t) - \sum_{j=0}^{\ell} \frac{f^{(j)}(\cdot)}{j!}t^j\,\Bigr\|_{L^2(dx)}
   \;\le\; \frac{L}{\ell!}\,|t|^{\beta}. $$

* `taylor_integral_remainder_sub` — the centered integral-remainder identity: subtracting the
  full order-`ℓ` polynomial leaves
  `t^ℓ/(ℓ−1)!·∫₀¹(1−τ)^{ℓ−1}(f^{(ℓ)}(x+τt) − f^{(ℓ)}(x))dτ`
  (the `ℓ`-th Taylor term is absorbed because `∫₀¹(1−τ)^{ℓ−1}dτ = 1/ℓ`).
* `MemNikolski.lintegral_sq_remainder_le` — the squared-`L²` bound, via the generalized
  Minkowski inequality and the Nikol'skii translate condition.

**Proof formalization notes.** For `ℓ = 0` the identity degenerates and the bound is the
Nikol'skii condition itself. For `ℓ ≥ 1`: `taylor_integral_remainder` plus linearity of the
`τ`-integral gives the identity; then `lintegral_lintegral_sq_rpow_le` (with `μ` the restricted
Lebesgue measure on `[0,1]` in the `τ` variable) pulls the `L²(dx)`-norm inside, and
`(1−τ)^{ℓ−1}·(τ|t|)^{β−ℓ} ≤ (1−τ)^{ℓ−1}` integrates to `1/ℓ`, upgrading `1/(ℓ−1)!` to `1/ℓ!`.

**Bibliographic comments.** The `L²`-modulus route to integrated bias is the classical
mean-integrated-squared-error computation of kernel density estimation; cf. M. Rosenblatt,
*Ann. Math. Statist.* **27** (1956), 832–837, and S. M. Nikol'skii, *Approximation of
Functions of Several Variables and Imbedding Theorems*, Springer, 1975.
-/

open MeasureTheory
open scoped ENNReal Nat

namespace StatLean.NonparametricStatistics

/-- **Centered integral-remainder identity**: for `C^ℓ` `f` (`ℓ ≥ 1`), subtracting the full
order-`ℓ` Taylor polynomial leaves the centered kernel-form remainder:
`f(x+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x)tʲ/j!
  = t^ℓ/(ℓ−1)!·∫₀¹ (1−τ)^{ℓ−1}·(f⁽ℓ⁾(x+τt) − f⁽ℓ⁾(x)) dτ`. -/
theorem taylor_integral_remainder_sub {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one; the `ℓ = 0` case is treated separately by consumers
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable; classical Taylor input
    (hf : ContDiff ℝ ℓ f)
    (x t : ℝ) :
    f (x + t) - ∑ j ∈ Finset.range (ℓ + 1),
        iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)
      = t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ)
        * ∫ τ in (0 : ℝ)..1,
            (1 - τ) ^ (ℓ - 1) * (iteratedDeriv ℓ f (x + τ * t) - iteratedDeriv ℓ f x) := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ).symm⟩
  have hm0 : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hcontD : Continuous (fun τ : ℝ => iteratedDeriv (m + 1) f (x + τ * t)) :=
    (hf.continuous_iteratedDeriv' (m + 1)).comp (by fun_prop)
  have hpow : Continuous (fun τ : ℝ => (1 - τ) ^ m) :=
    (continuous_const.sub continuous_id).pow m
  have hintA : IntervalIntegrable
      (fun τ : ℝ => (1 - τ) ^ m * iteratedDeriv (m + 1) f (x + τ * t)) volume 0 1 :=
    (hpow.mul hcontD).intervalIntegrable 0 1
  have hintB : IntervalIntegrable
      (fun τ : ℝ => iteratedDeriv (m + 1) f x * (1 - τ) ^ m) volume 0 1 :=
    (continuous_const.mul hpow).intervalIntegrable 0 1
  -- Split the centered integral and evaluate `∫₀¹ (1−τ)^m = 1/(m+1)`.
  have hIsub : (∫ τ in (0 : ℝ)..1,
        (1 - τ) ^ m * (iteratedDeriv (m + 1) f (x + τ * t) - iteratedDeriv (m + 1) f x))
      = (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m * iteratedDeriv (m + 1) f (x + τ * t))
        - iteratedDeriv (m + 1) f x * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ m := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hintA hintB]
    exact intervalIntegral.integral_congr (fun τ _ => by ring)
  have hI1 : (∫ τ in (0 : ℝ)..1, (1 - τ) ^ m) = 1 / ((m : ℝ) + 1) := by
    have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => -(1 - s) ^ (m + 1) / ((m : ℝ) + 1)) ((1 - τ) ^ m) τ := by
      intro τ _
      have hw := ((hasDerivAt_id τ).const_sub (1 : ℝ)).pow (m + 1)
      simp only [id_eq] at hw
      have h3 := hw.neg.div_const ((m : ℝ) + 1)
      convert h3 using 1
      rw [Nat.add_sub_cancel]; push_cast; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hpow.intervalIntegrable 0 1)]
    simp only [sub_self, sub_zero, one_pow, zero_pow (Nat.succ_ne_zero m), neg_zero, zero_div]
    ring
  have hfs : (Nat.factorial (m + 1) : ℝ) = ((m : ℝ) + 1) * Nat.factorial m := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [Finset.sum_range_succ, taylor_integral_remainder hℓ hf x t]
  simp only [Nat.add_sub_cancel]
  rw [hIsub, hI1, hfs]
  set S := ∑ j ∈ Finset.range (m + 1), iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)
  field_simp
  ring

/-- **Squared-`L²` Taylor remainder bound over a Nikol'skii class**: for `f ∈ H(β, L)` and
`ℓ = holderIndex β`,
`∫ (f(x+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x)tʲ/j!)² dx ≤ ((L/ℓ!)·|t|^β)²`. -/
theorem MemNikolski.lintegral_sq_remainder_le {β L : ℝ}
    -- USER-INPUT: positive smoothness and Nikol'skii constant; classical class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : MemNikolski β L f) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((f (x + t) - ∑ j ∈ Finset.range (holderIndex β + 1),
        iteratedDeriv j f x * t ^ j / (Nat.factorial j : ℝ)) ^ 2)
      ≤ ENNReal.ofReal ((L / (Nat.factorial (holderIndex β) : ℝ) * |t| ^ β) ^ 2) := by
  sorry

end StatLean.NonparametricStatistics
