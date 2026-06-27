import StatLean.Minimaxity.Fano.FanoLowerBound

/-!
# Lower bounds based on local packings (Wainwright §15.3.3)

The "generalized Fano" / local-packing method packages the Fano lower bound with the convexity
bound on the mutual information (Eq. (15.34)). If a `2δ`-separated family can be found whose pairwise
KL divergences are uniformly controlled and which is large enough, the minimax risk is bounded below
by `½ Φ(δ)`:

> In summary, if we can find a `2δ`-separated family of distributions such that conditions
> (15.35a) `√(D(P_{θʲ} ‖ P_{θᵏ})) ≤ c √n δ` and (15.35b) `log M(2δ) ≥ 2{c²nδ² + log 2}` both hold,
> then the minimax risk is lower bounded as `M(θ(𝒫); Φ∘ρ) ≥ ½ Φ(δ)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Local-packing minimax lower bound** (Wainwright §15.3.3, conditions (15.35a)/(15.35b)): given a
`2δ`-separated family `θfam : Fin M → Θ` whose pairwise KL divergences satisfy
`D(P_{θʲ} ‖ P_{θᵏ}) ≤ c²nδ²` (15.35a) and whose cardinality satisfies
`log M ≥ 2(c²nδ² + log 2)` (15.35b), the minimax risk is at least `½ Φ(δ)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3. -/
theorem minimax_local_packing [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞) (c n : ℝ)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.3.3.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set; Wainwright §15.3.3.
    (hsep : IsSeparatedFamily g θfam δ)
    -- USER-INPUT: pairwise KL control (15.35a), `√D ≤ c√n δ`; Wainwright §15.3.3.
    (h35a : ∀ j k, j ≠ k →
      klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * n * δ.toReal ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.3.
    (h35b : 2 * (c ^ 2 * n * δ.toReal ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    2⁻¹ * Φ δ ≤ minimaxRiskDist Φ g P := by
  sorry

end StatLean.Minimaxity
