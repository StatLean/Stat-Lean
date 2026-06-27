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

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- Composition of an estimator kernel with a comapped data kernel is the comap of the composition:
`κ ∘ₖ (P.comap f) = (κ ∘ₖ P).comap f`. Both equal `(κ ∘ₖ P) ∘ₖ deterministic f`. -/
private lemma comp_comap {M : ℕ} (κ : Kernel 𝓧 Ω) (P : Kernel Θ 𝓧)
    (f : Fin M → Θ) (hf : Measurable f) :
    κ ∘ₖ P.comap f hf = (κ ∘ₖ P).comap f hf := by
  simp only [← Kernel.comp_deterministic_eq_comap]
  rw [← Kernel.comp_assoc]

/-- **Restriction to a finite subfamily decreases the minimax risk** (Wainwright §15.1.2, the
"restrict the supremum" step): the minimax risk of the sub-model `P.comap θfam` under the loss
`(j, y) ↦ Φ(ρ(θ(P_{θʲ}), y))` is at most the full minimax risk, since the supremum over the finite
index set `Fin M` is dominated by the supremum over all of `Θ`. -/
private lemma minimaxRisk_comap_le [PseudoEMetricSpace Ω] {M : ℕ}
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧)
    (θfam : Fin M → Θ) (hθ : Measurable θfam) :
    minimaxRisk (fun j y => distortionLoss Φ g (θfam j) y) (P.comap θfam hθ)
      ≤ minimaxRisk (distortionLoss Φ g) P := by
  simp only [minimaxRisk]
  refine iInf_mono fun κ => iInf_mono fun _ => iSup_le fun j => ?_
  rw [comp_comap κ P θfam hθ, Kernel.comap_apply]
  exact le_iSup (fun θ => ∫⁻ y, distortionLoss Φ g θ y ∂((κ ∘ₖ P) θ)) (θfam j)

/-- **Nearest-point reduction** (Wainwright §15.1.2, the geometric core, Figure 15.1): for a
`2δ`-separated family of functional values `gfam`, scaling the M-ary testing Bayes risk by `Φ δ`
lower bounds the distortion Bayes risk. The proof builds, from any estimator `κ : Kernel 𝓧 Ω`, the
nearest-point test `ψ = argmin_ℓ ρ(·, gfam ℓ) ∘ κ`, whose 0–1 error is controlled pointwise by
`Φ δ · 𝟙[ψ ≠ j] ≤ Φ(ρ(gfam j, ·))` via the triangle inequality and monotonicity of `Φ`. -/
private lemma mul_bayesRisk_zeroOne_le [PseudoEMetricSpace Ω] {M : ℕ} [NeZero M]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (gfam : Fin M → Ω) (δ : ℝ≥0∞)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ edist (gfam j) (gfam k)) :
    Φ δ * bayesRisk (zeroOneLoss M) Q (uniformPrior M)
      ≤ bayesRisk (fun j y => Φ (edist (gfam j) y)) Q (uniformPrior M) := by
  -- TODO(mmx): measurable nearest-point selector `T : Ω → Fin M` + the pointwise
  -- triangle-inequality bound; Wainwright §15.1.2, Eq. (15.3).
  sorry

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
  haveI : IsMarkovKernel (P.comap θfam hθ) := inferInstance
  calc Φ δ * multiwayTestingError (P.comap θfam hθ)
      = Φ δ * bayesRisk (zeroOneLoss M) (P.comap θfam hθ) (uniformPrior M) := rfl
    _ ≤ bayesRisk (fun j y => distortionLoss Φ g (θfam j) y) (P.comap θfam hθ) (uniformPrior M) :=
        mul_bayesRisk_zeroOne_le Φ hΦ (P.comap θfam hθ) (fun j => g (θfam j)) δ hsep
    _ ≤ minimaxRisk (fun j y => distortionLoss Φ g (θfam j) y) (P.comap θfam hθ) :=
        bayesRisk_le_minimaxRisk _ _ _
    _ ≤ minimaxRiskDist Φ g P := minimaxRisk_comap_le Φ g P θfam hθ

end StatLean.Minimaxity
