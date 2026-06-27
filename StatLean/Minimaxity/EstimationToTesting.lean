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

/-- **Restricting to a sub-family decreases the minimax risk.** For a measurable reindexing
`e : ι → Θ`, the minimax risk of the pulled-back model `P.comap e` with the precomposed loss is at
most the minimax risk of the full model: restricting the supremum over parameters to the image of
`e` can only decrease it. This is the first step of Wainwright's Proposition 15.1 (§15.1.2). -/
private lemma minimaxRisk_precomp_le {𝓨 ι : Type*} [MeasurableSpace 𝓨] [MeasurableSpace ι]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (e : ι → Θ) (he : Measurable e) :
    minimaxRisk (fun i => ℓ (e i)) (P.comap e he) ≤ minimaxRisk ℓ P := by
  refine iInf₂_mono fun κ _ => iSup_le fun i => le_iSup_of_le (e i) ?_
  have hcomp : (κ ∘ₖ (P.comap e he)) i = (κ ∘ₖ P) (e i) := by
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply]
  rw [hcomp]

/-- **Geometric core of Proposition 15.1 given a measurable nearest-point selector.** If the test
`T : Ω → Fin M` is measurable and its value at `y` realizes the nearest functional value
`g (θfam (T y))` to `y`, then `Φ(δ)` times the M-ary testing error of the sub-model is at most the
(restricted) minimax risk.
The estimation-to-testing reduction (Wainwright §15.1.2, Figure 15.1): post-compose any estimator
`κ` with `T` to obtain a test, and use the `2δ`-separation to bound the 0–1 loss by `Φ(ρ)/Φ(δ)`. -/
private lemma mul_multiwayTestingError_le
    [PseudoEMetricSpace Ω] {M : ℕ} [NeZero M]
    {Φ : ℝ≥0∞ → ℝ≥0∞} {g : Θ → Ω} (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {θfam : Fin M → Θ} (hθ : Measurable θfam) {δ : ℝ≥0∞}
    (hΦ : Monotone Φ) (hsep : IsSeparatedFamily g θfam δ)
    {T : Ω → Fin M} (hT : Measurable T)
    (hTmin : ∀ y ℓ, edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y) :
    Φ δ * multiwayTestingError (P.comap θfam hθ)
      ≤ minimaxRisk (fun j => distortionLoss Φ g (θfam j)) (P.comap θfam hθ) := by
  set Q := P.comap θfam hθ with hQ
  haveI : IsMarkovKernel Q := Kernel.IsMarkovKernel.comap P hθ
  -- Pointwise geometric bound: `Φ(δ)·𝟙[T y ≠ j] ≤ Φ(ρ(g(θfam j), y))`.
  have hpt : ∀ (j : Fin M) (y : Ω),
      Φ δ * zeroOneLoss M j (T y) ≤ distortionLoss Φ g (θfam j) y := by
    intro j y
    unfold distortionLoss zeroOneLoss
    by_cases hjy : j = T y
    · simp [hjy]
    · rw [if_neg hjy, mul_one]
      apply hΦ
      have hsep' := hsep j (T y) hjy
      have htri : edist (g (θfam j)) (g (θfam (T y)))
          ≤ edist (g (θfam j)) y + edist (g (θfam (T y))) y := by
        calc edist (g (θfam j)) (g (θfam (T y)))
            ≤ edist (g (θfam j)) y + edist y (g (θfam (T y))) := edist_triangle _ _ _
          _ = edist (g (θfam j)) y + edist (g (θfam (T y))) y := by rw [edist_comm y]
      have hmin := hTmin y j
      have h2 : 2 * δ ≤ 2 * edist (g (θfam j)) y := by
        calc 2 * δ ≤ edist (g (θfam j)) (g (θfam (T y))) := hsep'
          _ ≤ edist (g (θfam j)) y + edist (g (θfam (T y))) y := htri
          _ ≤ edist (g (θfam j)) y + edist (g (θfam j)) y := by gcongr
          _ = 2 * edist (g (θfam j)) y := (two_mul _).symm
      exact (ENNReal.mul_le_mul_left (by norm_num) (by norm_num)).mp h2
  -- Reduce the minimax risk to a per-estimator bound.
  rw [multiwayTestingError, minimaxRisk]
  refine le_iInf₂ fun κ hκ => ?_
  haveI := hκ
  -- The post-composed test `ψ = T ∘ κ`.
  haveI : IsMarkovKernel (Kernel.deterministic T hT) := Kernel.isMarkovKernel_deterministic hT
  set ψ : Kernel 𝓧 (Fin M) := (Kernel.deterministic T hT).comp κ with hψ
  have hψcomp : ψ ∘ₖ Q = (κ ∘ₖ Q).map T := by
    rw [hψ, Kernel.comp_assoc, Kernel.deterministic_comp_eq_map]
  have hB : avgRisk (zeroOneLoss M) Q ψ (uniformPrior M)
      = ∫⁻ j, ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by
    unfold avgRisk
    refine lintegral_congr fun j => ?_
    have hfm : Measurable (zeroOneLoss M j) := measurable_of_countable _
    rw [hψcomp, Kernel.map_apply (κ ∘ₖ Q) hT]
    exact lintegral_map hfm hT
  calc Φ δ * bayesRisk (zeroOneLoss M) Q (uniformPrior M)
      ≤ Φ δ * avgRisk (zeroOneLoss M) Q ψ (uniformPrior M) := by
        gcongr; exact bayesRisk_le_avgRisk _ _ _ _
    _ = Φ δ * ∫⁻ j, ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by rw [hB]
    _ ≤ ∫⁻ j, Φ δ * ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ j, ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by
        refine lintegral_mono fun j => ?_
        calc Φ δ * ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j)
            ≤ ∫⁻ y, Φ δ * zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) := lintegral_const_mul_le _ _
          _ ≤ ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) :=
              lintegral_mono fun y => hpt j y
    _ ≤ ⨆ j, ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) := lintegral_le_iSup _

/-- **From estimation to testing** (Wainwright Proposition 15.1, Eq. (15.3)): for any increasing
distortion `Φ` and any `2δ`-separated family `θfam : Fin M → Θ` in the semimetric `ρ = edist` on
the functional values, the minimax risk is lower bounded by `Φ(δ)` times the M-ary testing error
of the induced sub-model `j ↦ P_{θfam j}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3). -/
theorem minimax_ge_testing_error
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {M : ℕ} [NeZero M]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.1.2, Prop 15.1.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set in the semimetric `ρ`; Wainwright §15.1.2.
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * multiwayTestingError (P.comap θfam hθ) ≤ minimaxRiskDist Φ g P := by
  unfold minimaxRiskDist
  refine le_trans ?_ (minimaxRisk_precomp_le (distortionLoss Φ g) P θfam hθ)
  -- It remains to supply a *measurable* nearest-point selector `T : Ω → Fin M`.
  -- TODO(mmx): constructing a measurable `argmin`-test requires Borel / second-countable structure
  -- on `Ω` (so that `y ↦ edist (g (θfam ℓ)) y` is measurable), which the current public signature
  -- does not provide; given `⟨T, hT, hTmin⟩` the bound closes via `mul_multiwayTestingError_le`.
  obtain ⟨T, hT, hTmin⟩ : ∃ T : Ω → Fin M, Measurable T ∧
      ∀ y ℓ, edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y := by
    sorry
  exact mul_multiwayTestingError_le P hθ hΦ hsep hT hTmin

end StatLean.Minimaxity
