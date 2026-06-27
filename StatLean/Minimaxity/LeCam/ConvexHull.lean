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
      ≤ minimaxRiskDist Φ g P := by
  -- Wainwright's convex-hull method (§15.2.2): the binary experiment whose two hypotheses are the
  -- mixtures `Q̄₀ = ∫ P_{a₀} dπ₀`, `Q̄₁ = ∫ P_{a₁} dπ₁` is dominated by the original family `P`, so
  -- the two-point bound applies to the mixtures.  Concretely, against the two-class prior with
  -- mixing measures `π₀, π₁`, the Bayes risk reduces to the binary testing error between `Q̄₀, Q̄₁`,
  -- and `one_sub_tvDist_eq_iInf` rewrites `1 − ‖Q̄₁ − Q̄₀‖_TV` as the optimal-test value.
  --
  -- TODO(mmx): this requires the *mixture* analogue of `mul_multiwayTestingError_le`
  -- (`EstimationToTesting.lean`): a measurable nearest-point selector deciding class 0 vs class 1
  -- from any estimator.  Building that test inherits the same `Ω`-measurability gap as the
  -- point-family case (Borel / second-countable structure on `Ω`, absent from this signature),
  -- and additionally the prior-pushforward / mixture-domination step.  The trailing TV factor is
  -- already in the target form, so the residual is exactly this mixture two-point bound.
  sorry

end StatLean.Minimaxity
