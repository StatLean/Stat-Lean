import StatLean.Minimaxity.LeCam.Functional

/-!
# Examples: pointwise density estimation and quadratic functionals (Wainwright Examples 15.7, 15.8)

Two nonparametric applications of Le Cam's functional method (Corollary 15.6):

* **Example 15.7** — estimating the value `f(0)` of a Lipschitz density yields the rate `n^{-2/3}`
  (the Hellinger modulus scales as `ω(ε) ≍ ε^{2/3}`).
* **Example 15.8** — estimating the quadratic functional `θ(f) = ∫(f'(x))² dx` over twice-smooth
  densities yields the (suboptimal, two-point) rate `n^{-1/2}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Examples 15.7–15.8.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Pointwise estimation of a Lipschitz density** (Wainwright Example 15.7): estimating `f(0)` over
the class of `1`-Lipschitz densities on `[-1/2, 1/2]` bounded away from zero, from `n` i.i.d. samples,
has minimax squared-error risk at least `c · n^{-2/3}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.7. -/
theorem lipschitz_density_pointwise_rate {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    -- USER-INPUT: the functional is the density value at 0; Wainwright §15.2, Example 15.7.
    (hθ : ∀ i, θfunc i = f i 0)
    -- USER-INPUT: each `f i` is a `1`-Lipschitz density bounded below; Wainwright §15.2, Example 15.7.
    (hclass : ∀ i, LipschitzWith 1 (f i) ∧ (∀ x, (1 / 2 : ℝ) ≤ f i x))
    -- USER-INPUT: `Pn i` is the `n`-fold i.i.d. product of the density `f i`; Wainwright §15.2.
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => volume.withDensity fun x => ENNReal.ofReal (f i x)) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (n : ℝ) ^ (-(2 : ℝ) / 3)) ≤ minimaxRiskDist (· ^ 2) θfunc Pn := by
  sorry

/-- **Lower bound for a quadratic functional** (Wainwright Example 15.8): estimating
`θ(f) = ∫ (f'(x))² dx` over twice-smooth densities, from `n` i.i.d. samples, has minimax risk at
least `c · n^{-1/2}` by the two-point method (this bound is not sharp; cf. Example 15.11).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.8. -/
theorem quadratic_functional_two_point_rate {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    -- USER-INPUT: `θ(f) = ∫(f')²`, over twice-smooth densities; Wainwright §15.2, Example 15.8.
    (hclass : ∀ i, ∀ x, (1 / 2 : ℝ) ≤ f i x)
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => volume.withDensity fun x => ENNReal.ofReal (f i x)) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ minimaxRiskDist (· ^ 2) θfunc Pn := by
  sorry

end StatLean.Minimaxity
