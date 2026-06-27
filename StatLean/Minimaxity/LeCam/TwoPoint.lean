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
  -- Unfolding `bayesRisk (zeroOneLoss 2) Q (uniformPrior 2)`, a Markov test `κ : Kernel 𝓧 (Fin 2)`
  -- is encoded by the acceptance function `a x = κ x {1} ∈ [0,1]`, and its average 0–1 risk is
  --   ½ (Q0[{1}] + Q1[{0}]) = ½ (∫ a dQ0 + 1 − ∫ a dQ1) = ½ (1 − (∫ a dQ1 − ∫ a dQ0)).
  -- Taking the infimum over `0 ≤ a ≤ 1` turns the bracket into a supremum:
  --   inf_a ½(1 − ∫ a d(Q1 − Q0)) = ½(1 − sup_a ∫ a d(Q1 − Q0)) = ½(1 − ‖Q1 − Q0‖_TV),
  -- the supremum being attained by `a = 𝟙[dQ1/dQ0 > 1]` (the likelihood-ratio test), which realizes
  -- `tvDist (Q 0) (Q 1)` by the supremum form `tvDist = ⨆ s, μ s − ν s`.
  --
  -- TODO(mmx): formalize the kernel-↔-acceptance-function correspondence and the identity
  -- `⨆_{0 ≤ a ≤ 1, measurable} ∫⁻ a d(Q1 − Q0) = tvDist (Q 0) (Q 1)`; the latter is the variational
  -- characterization of total variation (companion to `one_sub_tvDist_eq_iInf`).
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
  classical
  -- The two-point sub-family `θfam = ![θ₀, θ₁]`.
  set θfam : Fin 2 → Θ := ![θ₀, θ₁] with hfam
  have hθ : Measurable θfam := measurable_of_countable _
  haveI : IsMarkovKernel (P.comap θfam hθ) := Kernel.IsMarkovKernel.comap P hθ
  have h01 : 2 * δ ≤ edist (g (θfam 0)) (g (θfam 1)) := by simpa [θfam] using hsep
  have hsepf : IsSeparatedFamily g θfam δ := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
        | exact absurd rfl hjk
        | exact h01
        | (rw [edist_comm]; exact h01)
  have key := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsepf
  rw [binary_testingError_eq_tvDist (P.comap θfam hθ)] at key
  simp only [Kernel.comap_apply, θfam, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  calc Φ δ / 2 * (1 - tvDist (P θ₀) (P θ₁))
      = Φ δ * (2⁻¹ * (1 - tvDist (P θ₀) (P θ₁))) := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ minimaxRiskDist Φ g P := key

end StatLean.Minimaxity
