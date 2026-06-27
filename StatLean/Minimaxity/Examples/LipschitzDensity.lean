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

/-- **Crux: Hellinger-modulus lower bound for pointwise Lipschitz-density estimation.** A bump
perturbation of width `ε^{2/3}` keeps the squared Hellinger distance `≤ ε²` while moving the value
`f(0)` by `≍ ε^{2/3}`, so `ω(1/(2√n)) ≳ n^{-1/3}`; squaring and the `4⁻¹` factor of Corollary 15.6
turn this into the `n^{-2/3}` lower bound on the method's modulus term. -/
private lemma lipschitz_pointwise_modulus_bound {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (hθ : ∀ i, θfunc i = f i 0)
    (hclass : ∀ i, LipschitzWith 1 (f i) ∧ (∀ x, (1 / 2 : ℝ) ≤ f i x)) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n : ℝ) ^ (-(2 : ℝ) / 3))
      ≤ 4⁻¹ * (fun x : ℝ≥0∞ => x ^ 2) (2⁻¹ * hellingerModulus θfunc
          (fun i => volume.withDensity fun x => ENNReal.ofReal (f i x))
          (ENNReal.ofReal (1 / (2 * Real.sqrt n)))) := by
  sorry -- TODO(mmx): bump-perturbation lower bound on hellingerModulus (ω(ε) ≍ ε^{2/3})

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
  obtain ⟨c, hc, hbound⟩ := lipschitz_pointwise_modulus_bound n hn f θfunc hθ hclass
  refine ⟨c, hc, ?_⟩
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_functional_modulus θfunc
    (fun i => volume.withDensity fun x => ENNReal.ofReal (f i x)) n Pn
    (fun x : ℝ≥0∞ => x ^ 2) hΦ hPn
  exact le_trans hbound key

/-- **Lower bound for a quadratic functional** (Wainwright Example 15.8): estimating
`θ(f) = ∫ (f'(x))² dx` over twice-smooth densities, from `n` i.i.d. samples, has minimax risk at
least `c · n^{-1/2}` by the two-point method (this bound is not sharp; cf. Example 15.11).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.8. -/
private lemma quadratic_two_point_modulus_bound {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (hclass : ∀ i, ∀ x, (1 / 2 : ℝ) ≤ f i x) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2))
      ≤ 4⁻¹ * (fun x : ℝ≥0∞ => x ^ 2) (2⁻¹ * hellingerModulus θfunc
          (fun i => volume.withDensity fun x => ENNReal.ofReal (f i x))
          (ENNReal.ofReal (1 / (2 * Real.sqrt n)))) := by
  sorry -- TODO(mmx): two-point Hellinger-modulus bound for the quadratic functional (ω(ε) ≍ ε^{1/2})

theorem quadratic_functional_two_point_rate {ι : Type*} [MeasurableSpace ι] (n : ℕ) (hn : 1 ≤ n)
    (f : ι → ℝ → ℝ) (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) [IsMarkovKernel Pn]
    -- USER-INPUT: `θ(f) = ∫(f')²`, over twice-smooth densities; Wainwright §15.2, Example 15.8.
    (hclass : ∀ i, ∀ x, (1 / 2 : ℝ) ≤ f i x)
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => volume.withDensity fun x => ENNReal.ofReal (f i x)) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ minimaxRiskDist (· ^ 2) θfunc Pn := by
  obtain ⟨c, hc, hbound⟩ := quadratic_two_point_modulus_bound n hn f θfunc hclass
  refine ⟨c, hc, ?_⟩
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_functional_modulus θfunc
    (fun i => volume.withDensity fun x => ENNReal.ofReal (f i x)) n Pn
    (fun x : ℝ≥0∞ => x ^ 2) hΦ hPn
  exact le_trans hbound key

end StatLean.Minimaxity
