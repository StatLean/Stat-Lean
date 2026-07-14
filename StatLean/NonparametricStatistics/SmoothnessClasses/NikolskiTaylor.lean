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
  sorry

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
