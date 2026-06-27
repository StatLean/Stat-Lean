import StatLean.Minimaxity.Defs

/-!
# From estimation to testing — Proposition 15.1 (Wainwright §15.1.2)

The fundamental reduction underlying every minimax lower bound in the chapter: the minimax
risk is lower bounded by `Φ(δ)` times the error probability of an M-ary hypothesis test built
from a `2δ`-separated family.

For any increasing distortion `Φ` and any `2δ`-separated family `{θʲ}` (in the semimetric `ρ`),
```
M(θ(𝒫); Φ∘ρ) ≥ Φ(δ) · inf_ψ ℚ[ψ(Z) ≠ J]          (Eq. (15.3))
```
where `ℚ` is the joint law of `(Z, J)` with `J` uniform on `[M]` and `Z ∼ P_{θᴶ}`.

**Proof (Wainwright §15.1.2).** Restricting the supremum over `𝒫` to the finite subfamily can only
decrease it, and the maximum over the subfamily dominates the uniform average (the Bayes risk):
this uses `bayesRisk_le_minimaxRisk`. The geometric core (Figure 15.1) is that the nearest-point
test `ψ(Z) = argmin_ℓ ρ(θ̂, θ(P_{θˡ}))` errs only when `ρ(θ̂, θ(P_{θᴶ})) ≥ δ`, so by Markov's
inequality and monotonicity of `Φ`, `𝔼[Φ(ρ(θ̂, θ(P_{θᴶ})))] ≥ Φ(δ)·ℙ[ψ ≠ J]`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧}

/-- **From estimation to testing** (Wainwright Proposition 15.1, Eq. (15.3)): for any increasing
distortion `Φ` and any `2δ`-separated family `θfam : Fin M → Θ` in the semimetric `ρ = edist` on
the functional values, the minimax risk is lower bounded by `Φ(δ)` times the M-ary testing error
of the induced sub-model `j ↦ P_{θfam j}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3). -/
theorem minimax_ge_testing_error
    [PseudoEMetricSpace Ω] {M : ℕ} [NeZero M]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.1.2, Prop 15.1.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set in the semimetric `ρ`; Wainwright §15.1.2.
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * multiwayTestingError (P.comap θfam hθ) ≤ minimaxRiskDist Φ g P := by
  sorry

end StatLean.Minimaxity
