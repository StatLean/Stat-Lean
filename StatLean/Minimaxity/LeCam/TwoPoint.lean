import StatLean.Minimaxity.EstimationToTesting
import StatLean.Minimaxity.ForMathlib.TotalVariation

/-!
# Le Cam's two-point method (Wainwright §15.2.1)

In a binary hypothesis test the Bayes error is expressed exactly by the total variation distance,
```
inf_ψ ℚ[ψ(Z) ≠ J] = ½ (1 − ‖ℙ₁ − ℙ₀‖_TV)            (Eq. (15.13)),
```
and combining this with the estimation-to-testing reduction (Proposition 15.1) gives Le Cam's
two-point lower bound: for any `2δ`-separated pair `θ₀, θ₁`,
```
M(θ(𝒫); Φ∘ρ) ≥ (Φ(δ)/2) (1 − ‖P_{θ₀} − P_{θ₁}‖_TV)   (Eq. (15.14)).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Bayes error equals total variation** (Wainwright Eq. (15.13)): in a binary test with equally
weighted hypotheses `Q 0, Q 1`, the optimal (Bayes) error probability is `½(1 − ‖Q 0 − Q 1‖_TV)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.13). -/
theorem binary_testingError_eq_tvDist (Q : Kernel (Fin 2) 𝓧) [IsMarkovKernel Q] :
    multiwayTestingError Q = 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := by
  sorry

/-- **Le Cam's two-point lower bound** (Wainwright Eq. (15.14)): for an increasing distortion `Φ`
and a pair `θ₀, θ₁` whose functional values are `2δ`-separated,
`M(θ(𝒫); Φ∘ρ) ≥ (Φ(δ)/2)(1 − ‖P_{θ₀} − P_{θ₁}‖_TV)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.14). -/
theorem minimax_two_point [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (θ₀ θ₁ : Θ) (δ : ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.1, Eq. (15.14).
    (hΦ : Monotone Φ)
    -- USER-INPUT: the two functional values are `2δ`-separated; Wainwright §15.2.1.
    (hsep : 2 * δ ≤ edist (g θ₀) (g θ₁)) :
    Φ δ / 2 * (1 - tvDist (P θ₀) (P θ₁)) ≤ minimaxRiskDist Φ g P := by
  sorry

end StatLean.Minimaxity
