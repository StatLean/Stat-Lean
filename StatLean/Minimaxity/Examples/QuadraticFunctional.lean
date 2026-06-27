import StatLean.Minimaxity.LeCam.ConvexHull
import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking

/-!
# Example: optimal bounds for quadratic functionals (Wainwright Example 15.11)

The convex-hull (full) form of Le Cam's method, applied to a `2ᵐ`-element family of densities
`f_α(x) = 1 + Σⱼ αⱼ φⱼ(x)` indexed by sign vectors `α ∈ {−1,+1}ᵐ`, yields the **optimal** lower bound
for the quadratic functional `θ(f) = ∫ (f'(x))² dx`:
```
sup_{f ∈ ℱ₂} 𝔼[θ̂ − θ(f)] ≳ n^{-4/9}                       (Example 15.11),
```
improving on the suboptimal `n^{-1/2}` two-point bound (Example 15.8) by using mixtures over the
sign-vector family (whose total variation to the uniform mixture is much smaller).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Example 15.11.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Optimal lower bound for a quadratic functional** (Wainwright Example 15.11): via the convex-hull
Le Cam method over the sign-vector density family, the minimax risk for estimating `θ(f) = ∫(f')²`
from `n` i.i.d. samples is at least `c · n^{-4/9}` — the sharp nonparametric rate.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Example 15.11. -/
theorem quadratic_functional_optimal_rate {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    -- USER-INPUT: `θ(f) = ∫(f')²`, over the sign-vector density family; Wainwright §15.2.2, Ex 15.11.
    (hclass : ∀ i, ∀ x, (1 / 2 : ℝ) ≤ f i x)
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => volume.withDensity fun x => ENNReal.ofReal (f i x)) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (n : ℝ) ^ (-(4 : ℝ) / 9)) ≤ minimaxRiskDist (· ^ 2) θfunc Pn := by
  sorry

end StatLean.Minimaxity
