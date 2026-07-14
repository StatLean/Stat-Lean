import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Taylor's theorem with integral remainder

For a globally `C^ℓ` function `f : ℝ → ℝ` (`ℓ ≥ 1`), the order-`ℓ` expansion with the exact
integral form of the remainder, for increments of either sign:
$$ f(x_0 + t) = \sum_{j=0}^{\ell-1} \frac{f^{(j)}(x_0)}{j!} t^j
   + \frac{t^\ell}{(\ell-1)!} \int_0^1 (1-\tau)^{\ell-1} f^{(\ell)}(x_0 + \tau t)\,d\tau. $$

This is the remainder form consumed by the *integrated* bias analysis of kernel smoothers over
Nikol'skii classes: unlike the Lagrange form it is linear in `f^{(ℓ)}` along the segment, so
`L²`-moduli of continuity can be pulled through by the generalized Minkowski inequality.

**Proof formalization notes.** Not available in Mathlib in this form (Mathlib's
`Mathlib.Analysis.Calculus.Taylor` provides mean-value-type remainders). Proof: induction on
`ℓ` with integration by parts in `τ`
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul` or `integral_deriv_smul_eq_sub`), with the
fundamental theorem of calculus (`intervalIntegral.integral_deriv_eq_sub`) as the base case
`ℓ = 1`; continuity of `iteratedDeriv ℓ f` supplies all integrability side conditions.

**Bibliographic comments.** The integral remainder is classical (A.-L. Cauchy, *Résumé des
leçons sur le calcul infinitésimal*, Paris, 1823).
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

/-- **Taylor's theorem with integral remainder** (global, two-sided). If `f` is `C^ℓ` on `ℝ`
with `ℓ ≥ 1`, then for every `x₀ t`:
`f (x₀ + t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)·tʲ/j! + (tℓ/(ℓ−1)!)·∫₀¹ (1−τ)^{ℓ−1} f⁽ℓ⁾(x₀ + τ·t) dτ`. -/
theorem taylor_integral_remainder {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one so the remainder integrand is a genuine derivative
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable on `ℝ`; classical smoothness
    -- input of Taylor's theorem
    (hf : ContDiff ℝ ℓ f)
    (x₀ t : ℝ) :
    f (x₀ + t)
      = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
        + t ^ ℓ / (Nat.factorial (ℓ - 1) : ℝ)
          * ∫ τ in (0 : ℝ)..1, (1 - τ) ^ (ℓ - 1) * iteratedDeriv ℓ f (x₀ + τ * t) := by
  sorry

end StatLean.NonparametricStatistics
