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

/-- The singleton mass of the uniform prior on `Fin 2` is `½`. -/
private lemma uniformPrior_two_apply (j : Fin 2) : uniformPrior 2 {j} = 2⁻¹ := by
  unfold uniformPrior
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), PMF.uniformOfFintype_apply]
  simp [Fintype.card_fin]

/-- Integration against the uniform prior on `Fin 2` averages the two values. -/
private lemma uniformPrior_two_lintegral (g : Fin 2 → ℝ≥0∞) :
    ∫⁻ j, g j ∂(uniformPrior 2) = 2⁻¹ * (g 0 + g 1) := by
  rw [lintegral_fintype, Fin.sum_univ_two, uniformPrior_two_apply, uniformPrior_two_apply]
  ring

/-- **Randomized binary test** with acceptance function `a`: on input `x` it answers `1` with
probability `a x` and `0` with probability `1 − a x`. This realizes the `iInf`-over-Markov-kernels
in `bayesRisk` by the explicit family of estimators `Kernel 𝓧 (Fin 2)`. -/
private noncomputable def binaryTest (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) : Kernel 𝓧 (Fin 2) :=
  Kernel.mk (fun x => a x • Measure.dirac 1 + (1 - a x) • Measure.dirac 0)
    (by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      exact (ha.mul measurable_const).add ((measurable_const.sub ha).mul measurable_const))

private lemma binaryTest_apply (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x = a x • Measure.dirac 1 + (1 - a x) • Measure.dirac 0 := by
  unfold binaryTest; rw [Kernel.coe_mk]

private lemma binaryTest_apply_one (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x {1} = a x := by
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2)),
      Measure.dirac_apply' _ (measurableSet_singleton (1 : Fin 2))]
  simp

private lemma binaryTest_apply_zero (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (x : 𝓧) :
    binaryTest a ha x {0} = 1 - a x := by
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2)),
      Measure.dirac_apply' _ (measurableSet_singleton (0 : Fin 2))]
  simp

private lemma isMarkovKernel_binaryTest (a : 𝓧 → ℝ≥0∞) (ha : Measurable a) (h1 : ∀ x, a x ≤ 1) :
    IsMarkovKernel (binaryTest a ha) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [binaryTest_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      smul_eq_mul, smul_eq_mul, measure_univ, measure_univ, mul_one, mul_one]
  exact add_tsub_cancel_of_le (h1 x)

/-- The average 0–1 risk of a Markov test `κ` against equally-weighted hypotheses `Q 0, Q 1`
equals `½ (Q 0[κ accepts `1`] + Q 1[κ accepts `0`])` (the two ways of being wrong). -/
private lemma avgRisk_zeroOneLoss_two (Q : Kernel (Fin 2) 𝓧) (κ : Kernel 𝓧 (Fin 2)) :
    avgRisk (zeroOneLoss 2) Q κ (uniformPrior 2)
      = 2⁻¹ * (∫⁻ x, κ x {1} ∂(Q 0) + ∫⁻ x, κ x {0} ∂(Q 1)) := by
  unfold avgRisk
  rw [uniformPrior_two_lintegral]
  have h0 : ∫⁻ y, zeroOneLoss 2 0 y ∂((κ ∘ₖ Q) 0) = ∫⁻ x, κ x {1} ∂(Q 0) := by
    rw [← Kernel.comp_apply' κ Q 0 (measurableSet_singleton 1), lintegral_fintype, Fin.sum_univ_two]
    simp [zeroOneLoss]
  have h1 : ∫⁻ y, zeroOneLoss 2 1 y ∂((κ ∘ₖ Q) 1) = ∫⁻ x, κ x {0} ∂(Q 1) := by
    rw [← Kernel.comp_apply' κ Q 1 (measurableSet_singleton 0), lintegral_fintype, Fin.sum_univ_two]
    simp [zeroOneLoss]
  rw [h0, h1]

/-- **Bayes error equals total variation** (Wainwright Eq. (15.13)): in a binary test with equally
weighted hypotheses `Q 0, Q 1`, the optimal (Bayes) error probability is `½(1 − ‖Q 0 − Q 1‖_TV)`.

The proof identifies the `iInf`-over-Markov-kernels defining `bayesRisk` with the variational
representation `one_sub_tvDist_eq_iInf` of total variation. Each Markov test `κ` contributes the
feasible pair `(κ·{1}, κ·{0})` (whose pointwise sum is `1`), giving the lower bound; conversely each
feasible `(f₀, f₁)` is realized — up to a value-decreasing truncation `a = min f₀ 1` — by the
explicit randomized test `binaryTest a`, giving the upper bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.13). -/
theorem binary_testingError_eq_tvDist (Q : Kernel (Fin 2) 𝓧) [IsMarkovKernel Q] :
    multiwayTestingError Q = 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  refine le_antisymm ?_ ?_
  · -- Upper bound: each feasible `(f₀, f₁)` is realized by a randomized test.
    have key : 2 * multiwayTestingError Q ≤ 1 - tvDist (Q 0) (Q 1) := by
      rw [one_sub_tvDist_eq_iInf (Q 0) (Q 1)]
      refine le_iInf fun f₀ => le_iInf fun f₁ => le_iInf fun hf0 => le_iInf fun hf1 =>
        le_iInf fun hfeas => ?_
      have ha : Measurable (fun x => min (f₀ x) 1) := hf0.min measurable_const
      have h1 : ∀ x, (fun x => min (f₀ x) 1) x ≤ 1 := fun x => min_le_right _ _
      haveI : IsMarkovKernel (binaryTest (fun x => min (f₀ x) 1) ha) :=
        isMarkovKernel_binaryTest _ ha h1
      have e1 : ∫⁻ x, binaryTest (fun x => min (f₀ x) 1) ha x {1} ∂(Q 0)
          = ∫⁻ x, min (f₀ x) 1 ∂(Q 0) := lintegral_congr fun x => binaryTest_apply_one _ ha x
      have e0 : ∫⁻ x, binaryTest (fun x => min (f₀ x) 1) ha x {0} ∂(Q 1)
          = ∫⁻ x, (1 - min (f₀ x) 1) ∂(Q 1) := lintegral_congr fun x => binaryTest_apply_zero _ ha x
      calc 2 * multiwayTestingError Q
          ≤ 2 * avgRisk (zeroOneLoss 2) Q
              (binaryTest (fun x => min (f₀ x) 1) ha) (uniformPrior 2) := by
            gcongr; exact bayesRisk_le_avgRisk _ _ _ _
        _ = ∫⁻ x, min (f₀ x) 1 ∂(Q 0) + ∫⁻ x, (1 - min (f₀ x) 1) ∂(Q 1) := by
            rw [avgRisk_zeroOneLoss_two Q (binaryTest (fun x => min (f₀ x) 1) ha), e1, e0,
                ← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
        _ ≤ ∫⁻ x, f₀ x ∂(Q 0) + ∫⁻ x, f₁ x ∂(Q 1) := by
            refine add_le_add (lintegral_mono fun x => min_le_left _ _) (lintegral_mono fun x => ?_)
            rcases le_total (f₀ x) 1 with h | h
            · rw [min_eq_left h, tsub_le_iff_right, add_comm]; exact hfeas x
            · rw [min_eq_right h, tsub_self]; exact zero_le _
    calc multiwayTestingError Q
        = 2⁻¹ * (2 * multiwayTestingError Q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h2 h2', one_mul]
      _ ≤ 2⁻¹ * (1 - tvDist (Q 0) (Q 1)) := mul_le_mul_left' key _
  · -- Lower bound: every Markov test contributes a feasible pair to the variational `iInf`.
    unfold multiwayTestingError bayesRisk
    refine le_iInf fun κ => le_iInf fun hκ => ?_
    rw [avgRisk_zeroOneLoss_two Q κ]
    gcongr
    rw [one_sub_tvDist_eq_iInf (Q 0) (Q 1)]
    have hfeas : ∀ x, (1 : ℝ≥0∞) ≤ κ x {1} + κ x {0} := by
      intro x
      rw [← measure_union (Set.disjoint_singleton.mpr (by decide)) (measurableSet_singleton 0)]
      have huniv : ({1} ∪ {0} : Set (Fin 2)) = Set.univ := by ext i; fin_cases i <;> simp
      rw [huniv, measure_univ]
    exact iInf_le_of_le (fun x => κ x {1}) (iInf_le_of_le (fun x => κ x {0})
      (iInf_le_of_le (κ.measurable_coe (measurableSet_singleton 1))
        (iInf_le_of_le (κ.measurable_coe (measurableSet_singleton 0))
          (iInf_le_of_le hfeas le_rfl))))

/-- **Le Cam's two-point lower bound** (Wainwright Eq. (15.14)): for an increasing distortion `Φ`
and a pair `θ₀, θ₁` whose functional values are `2δ`-separated,
`M(θ(𝒫); Φ∘ρ) ≥ (Φ(δ)/2)(1 − ‖P_{θ₀} − P_{θ₁}‖_TV)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.14). -/
theorem minimax_two_point [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
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
