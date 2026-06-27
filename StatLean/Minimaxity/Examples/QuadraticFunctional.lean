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

/-- **Crux: convex-hull configuration for the quadratic-functional lower bound.** The `2ᵐ`-element
sign-vector density family splits into two `2δ`-separated subfamilies (high/low functional value)
with `δ ≍ n^{-2/9}`; the total variation between their uniform mixtures is `≪ 1` (this is the gain
of the convex-hull method over two points), yielding the `n^{-4/9}` rate after squaring. -/
private lemma quadratic_convex_hull_config {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    (hclass : ∀ i, ∀ x, (1 / 2 : ℝ) ≤ f i x)
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => volume.withDensity fun x => ENNReal.ofReal (f i x)) :
    ∃ (δ : ℝ≥0∞) (a₀ a₁ : ι → ι) (ha₀ : Measurable a₀) (ha₁ : Measurable a₁)
      (π₀ π₁ : Measure ι) (_ : IsProbabilityMeasure π₀) (_ : IsProbabilityMeasure π₁),
      (∀ i₀ i₁, 2 * δ ≤ edist (θfunc (a₀ i₀)) (θfunc (a₁ i₁))) ∧
      ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n : ℝ) ^ (-(4 : ℝ) / 9))
        ≤ (fun x : ℝ≥0∞ => x ^ 2) δ / 2
            * (1 - tvDist (Pn.comap a₀ ha₀ ∘ₘ π₀) (Pn.comap a₁ ha₁ ∘ₘ π₁)) := by
  sorry -- TODO(mmx): sign-vector family, two separated subfamilies + mixture TV ≪ 1 (HammingPacking)

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
  obtain ⟨δ, a₀, a₁, ha₀, ha₁, π₀, π₁, hπ₀, hπ₁, hsep, c, hc, hbound⟩ :=
    quadratic_convex_hull_config n hn f θfunc Pn hclass hPn
  haveI := hπ₀; haveI := hπ₁
  refine ⟨c, hc, ?_⟩
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_le_cam_convex_hull (fun x : ℝ≥0∞ => x ^ 2) θfunc Pn δ
    a₀ a₁ ha₀ ha₁ π₀ π₁ hΦ hsep
  exact le_trans hbound key

end StatLean.Minimaxity
