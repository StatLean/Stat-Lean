import StatLean.Minimaxity.EstimationToTesting
import StatLean.Minimaxity.ForMathlib.TotalVariation

/-!
# Le Cam's convex-hull method — Lemma 15.9 (Wainwright §15.2.2)

Le Cam's two-point method generalizes from single pairs to pairs of *classes*: if two subfamilies
`𝒫₀, 𝒫₁ ⊆ 𝒫` are `2δ`-separated, then the minimax risk is controlled by the total variation distance
measured over their **convex hulls** (mixtures), which can be far smaller than the pointwise
separation:
```
sup_{P∈𝒫} 𝔼_P[ρ(θ̂, θ(P))] ≥ (δ/2) sup_{Q₀∈conv(𝒫₀), Q₁∈conv(𝒫₁)} (1 − ‖Q₁ − Q₀‖_TV)   (Eq. (15.26)).
```

We state it for given mixtures (the supremum over `conv` is recovered by quantifying over the mixing
measures `π₀, π₁`): for any `2δ`-separated pair of subfamilies indexed by `a₀, a₁` and any priors
`π₀, π₁`, the bound holds with the mixtures `Q̄₀ = ∫ P_{a₀} dπ₀`, `Q̄₁ = ∫ P_{a₁} dπ₁`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Lemma 15.9.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

-- Crux of Lemma 15.9: the convex-hull / mixture two-point reduction. One forms the mixed prior
-- (½·π₀ on `𝒫₀`, ½·π₁ on `𝒫₁`), lower bounds its Bayes risk by `Φ δ` times the binary testing
-- error between the mixtures `Q̄₀, Q̄₁` (the convexity/data-processing step), and rewrites that
-- error via Eq. (15.13). The mixture-prior reduction is not assembled from the available
-- `minimax_ge_testing_error` (a finite-family statement); left as a named debt.
private lemma minimax_le_cam_convex_hull_aux [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (δ : ℝ≥0∞) {ι₀ ι₁ : Type*} [MeasurableSpace ι₀] [MeasurableSpace ι₁]
    (a₀ : ι₀ → Θ) (a₁ : ι₁ → Θ) (ha₀ : Measurable a₀) (ha₁ : Measurable a₁)
    (π₀ : Measure ι₀) (π₁ : Measure ι₁) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (hΦ : Monotone Φ)
    (hsep : ∀ i₀ i₁, 2 * δ ≤ edist (g (a₀ i₀)) (g (a₁ i₁))) :
    Φ δ / 2 * (1 - tvDist (P.comap a₀ ha₀ ∘ₘ π₀) (P.comap a₁ ha₁ ∘ₘ π₁))
      ≤ minimaxRiskDist Φ g P := by
  sorry -- TODO(mmx): Lemma 15.9 — mixture-prior two-point reduction over the convex hulls

/-- **Le Cam's convex-hull lower bound** (Wainwright Lemma 15.9, Eq. (15.26)): for two `2δ`-separated
subfamilies `{P_{a₀ i}}`, `{P_{a₁ i}}` and any mixing priors `π₀, π₁`, the minimax risk dominates
`(δ/2)(1 − ‖Q̄₁ − Q̄₀‖_TV)`, where `Q̄₀, Q̄₁` are the corresponding mixtures over the convex hulls.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.2, Lemma 15.9. -/
theorem minimax_le_cam_convex_hull [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (δ : ℝ≥0∞) {ι₀ ι₁ : Type*} [MeasurableSpace ι₀] [MeasurableSpace ι₁]
    (a₀ : ι₀ → Θ) (a₁ : ι₁ → Θ) (ha₀ : Measurable a₀) (ha₁ : Measurable a₁)
    (π₀ : Measure ι₀) (π₁ : Measure ι₁) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.2, Lemma 15.9.
    (hΦ : Monotone Φ)
    -- USER-INPUT: the two subfamilies are `2δ`-separated in the semimetric `ρ`; Wainwright §15.2.2.
    (hsep : ∀ i₀ i₁, 2 * δ ≤ edist (g (a₀ i₀)) (g (a₁ i₁))) :
    Φ δ / 2 * (1 - tvDist (P.comap a₀ ha₀ ∘ₘ π₀) (P.comap a₁ ha₁ ∘ₘ π₁))
      ≤ minimaxRiskDist Φ g P :=
  minimax_le_cam_convex_hull_aux Φ g P δ a₀ a₁ ha₀ ha₁ π₀ π₁ hΦ hsep

end StatLean.Minimaxity
