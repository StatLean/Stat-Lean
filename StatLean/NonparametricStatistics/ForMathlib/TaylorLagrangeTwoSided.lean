import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Taylor's theorem with Lagrange remainder, two-sided global form

For a globally `C^ℓ` function `f : ℝ → ℝ` (`ℓ ≥ 1`), expansion of order `ℓ − 1` around `x₀`
with the mean-value (Lagrange) form of the remainder, valid for increments of *either* sign:
$$ f(x_0 + t) = \sum_{j=0}^{\ell-1} \frac{f^{(j)}(x_0)}{j!} t^j
   + \frac{f^{(\ell)}(x_0 + \tau t)}{\ell!}\,t^\ell, \qquad \tau \in (0,1). $$

This is the exact shape consumed by the pointwise bias analysis of kernel smoothers over
Hölder classes: the remainder features the `ℓ`-th derivative at an intermediate point, to be
compared with its value at `x₀` via the Hölder condition.

**Proof formalization notes.** Mathlib's `taylor_mean_remainder_lagrange` is one-sided
(`x₀ < x`, sets phrased with `Icc x₀ x` and `iteratedDerivWithin`); this file upgrades it to
the two-sided global form by working on `uIcc` (or by reflecting `f`), and converts
`iteratedDerivWithin` on the interval to global `iteratedDeriv` using `ContDiff` and unique
differentiability of intervals. The intermediate point is reported as `x₀ + τ·t`, `τ ∈ (0,1)`,
which covers both signs of `t` uniformly.

**Bibliographic comments.** B. Taylor, *Methodus incrementorum directa et inversa* (London,
1715); the mean-value remainder form is due to J.-L. Lagrange, *Théorie des fonctions
analytiques* (Paris, 1797).
-/

open scoped Nat

namespace StatLean.NonparametricStatistics

/-- **Taylor–Lagrange, two-sided global form.** If `f` is `C^ℓ` on `ℝ` with `ℓ ≥ 1` and
`t ≠ 0`, then for some `τ ∈ (0,1)`:
`f (x₀ + t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)·tʲ/j! + f⁽ℓ⁾(x₀ + τ·t)·tℓ/ℓ!`. -/
theorem taylor_lagrange_global {f : ℝ → ℝ} {ℓ : ℕ}
    -- LEAN-ONLY: order at least one so the remainder term is a genuine derivative; the
    -- degenerate `ℓ = 0` case is handled separately by consumers
    (hℓ : 1 ≤ ℓ)
    -- USER-INPUT: `f` is `ℓ` times continuously differentiable on `ℝ`; classical smoothness
    -- input of Taylor's theorem
    (hf : ContDiff ℝ ℓ f)
    (x₀ t : ℝ)
    -- LEAN-ONLY: nonzero increment; at `t = 0` both sides are `f x₀` and no intermediate
    -- point is needed
    (ht : t ≠ 0) :
    ∃ τ ∈ Set.Ioo (0 : ℝ) 1,
      f (x₀ + t)
        = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t ^ j / (Nat.factorial j : ℝ))
          + iteratedDeriv ℓ f (x₀ + τ * t) * t ^ ℓ / (Nat.factorial ℓ : ℝ) := by
  sorry

end StatLean.NonparametricStatistics
