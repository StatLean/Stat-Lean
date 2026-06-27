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
-- Crux of Eq. (15.13): the Bayes error of the binary test is attained at the likelihood-ratio
-- test, where it equals `½(1 − ‖Q 0 − Q 1‖_TV)`. This is the binary optimal-test identity
-- (Neyman–Pearson), which Mathlib does not yet package as a usable lemma; left as a named debt.
private lemma binary_testingError_eq_tvDist_aux (Q : Kernel (Fin 2) 𝓧) [IsMarkovKernel Q] :
    multiwayTestingError Q = 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := by
  sorry -- TODO(mmx): Eq. (15.13) — binary Bayes error = ½(1 − TV) via likelihood-ratio test

theorem binary_testingError_eq_tvDist (Q : Kernel (Fin 2) 𝓧) [IsMarkovKernel Q] :
    multiwayTestingError Q = 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) :=
  binary_testingError_eq_tvDist_aux Q

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
  -- The two-point family `θfam = ![θ₀, θ₁] : Fin 2 → Θ`.
  have hθ : Measurable (![θ₀, θ₁] : Fin 2 → Θ) := measurable_from_top
  -- The pair is `2δ`-separated as a (two-element) separated family.
  have hsepfam : IsSeparatedFamily g (![θ₀, θ₁] : Fin 2 → Θ) δ := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · simpa using hsep
    · simpa [edist_comm] using hsep
    · exact absurd rfl hjk
  -- Specialize Proposition 15.1 to `M = 2`, then rewrite the testing error via Eq. (15.13).
  have key := minimax_ge_testing_error Φ g P (![θ₀, θ₁] : Fin 2 → Θ) hθ δ hΦ hsepfam
  rw [binary_testingError_eq_tvDist] at key
  simp only [Kernel.comap_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  calc Φ δ / 2 * (1 - tvDist (P θ₀) (P θ₁))
      = Φ δ * (2⁻¹ * (1 - tvDist (P θ₀) (P θ₁))) := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ minimaxRiskDist Φ g P := key

end StatLean.Minimaxity
