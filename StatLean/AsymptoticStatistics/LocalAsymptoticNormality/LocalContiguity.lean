import StatLean.AsymptoticStatistics.ForMathlib.ContiguityIntegralComparison
import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.MovingProductLikelihood
import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.MovingLAN

/-!
# Local contiguity from differentiability in quadratic mean

Support-free mutual contiguity of product experiments along finite-dimensional
`1 / √n`-local parameter sequences.  The first theorem keeps an arbitrary sample-size
subsequence `m n`; the second is the bounded-local-parameter wrapper used by
subsequence arguments.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

open AsymptoticRepresentation

variable {d : ℕ}
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **DQM local alternatives are mutually contiguous along a strictly increasing
sample-size subsequence.**

The proof combines the contiguity integral-comparison theorem, the
moving-product likelihood comparison, and moving-path LAN.  Strict
monotonicity packages both divergence of the sample sizes and the injective range
needed by the moving-path construction.  No common-support, absolute-continuity,
or public sigma-finiteness premise is exposed.
-/
theorem mutuallyContiguous_products_of_dqm_of_scaled_tendsto_strictMono
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M μ)
    (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : ℕ → ℕ)
    (hm : StrictMono m)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Contiguity.MutuallyContiguous atTop
      (fun n => productMeasure M μ θ₀ (m n))
      (fun n => productMeasure M μ (θ n) (m n)) := by
  let P : ∀ n, Measure (Fin (m n) → 𝒳) :=
    fun n => productMeasure M μ θ₀ (m n)
  let Q : ∀ n, Measure (Fin (m n) → 𝒳) :=
    fun n => productMeasure M μ (θ n) (m n)
  let L : ∀ n, (Fin (m n) → 𝒳) → ℝ :=
    fun n => movingLogLikelihood M θ₀ m θ n
  let v : NNReal := (fisherInformation M μ θ₀ ℓ h h).toNNReal
  haveI hP_prob : ∀ n, IsProbabilityMeasure (P n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ (m n)
  haveI hQ_prob : ∀ n, IsProbabilityMeasure (Q n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF (θ n) (m n)
  obtain ⟨h_exp_int, h_mass, h_comparison⟩ :=
    movingProductMeasure_likelihood_comparison M μ θ₀ ℓ hPDF hDQM m hm θ h hθ
  have h_weak := movingLogLikelihood_weaklyConverges
    M μ θ₀ ℓ hPDF hℓ hDQM m hm θ h hθ
  exact Contiguity.mutuallyContiguous_of_asymptotically_log_normal_of_integral_comparison
    P Q L (movingLogLikelihood_measurable M θ₀ m θ) h_exp_int h_mass
      h_comparison v h_weak

/-- **DQM local alternatives are mutually contiguous along an arbitrary sample-size
subsequence.**

If `m n → ∞` and `√(m n) • (θ n - θ₀) → h`, then the `m n`-fold product
laws at `θ₀` and `θ n` are mutually contiguous.  This is the support-free local
contiguity consequence of DQM; its proof uses a finite dominating measure for each
two-point local experiment rather than a public sigma-finiteness or common-support
assumption.

The arbitrary `m` formulation is the form required when a failure of contiguity is
pulled back to a bad subsequence.
-/
theorem mutuallyContiguous_products_of_dqm_of_scaled_tendsto
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M μ)
    (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d))
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    Contiguity.MutuallyContiguous atTop
      (fun n => productMeasure M μ θ₀ (m n))
      (fun n => productMeasure M μ (θ n) (m n)) := by
  constructor
  · intro A hA hP
    refine SubsequenceLimit.tendsto_of_subseq_tendsto
      (fun n => productMeasure M μ (θ n) (m n) (A n)) 0 ?_
    intro φ hφ
    have hmφ : Tendsto (m ∘ φ) atTop atTop := hm.comp hφ.tendsto_atTop
    obtain ⟨ψ, hψ, hmφψ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hmφ
    have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have hcont := mutuallyContiguous_products_of_dqm_of_scaled_tendsto_strictMono
      M μ θ₀ ℓ hPDF hℓ hDQM ((m ∘ φ) ∘ ψ) hmφψ
        ((θ ∘ φ) ∘ ψ) h (hθ.comp hφψ.tendsto_atTop)
    refine ⟨ψ, hψ, ?_⟩
    exact hcont.1 (fun n => A (φ (ψ n))) (fun n => hA _)
      (hP.comp hφψ.tendsto_atTop)
  · intro A hA hQ
    refine SubsequenceLimit.tendsto_of_subseq_tendsto
      (fun n => productMeasure M μ θ₀ (m n) (A n)) 0 ?_
    intro φ hφ
    have hmφ : Tendsto (m ∘ φ) atTop atTop := hm.comp hφ.tendsto_atTop
    obtain ⟨ψ, hψ, hmφψ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hmφ
    have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have hcont := mutuallyContiguous_products_of_dqm_of_scaled_tendsto_strictMono
      M μ θ₀ ℓ hPDF hℓ hDQM ((m ∘ φ) ∘ ψ) hmφψ
        ((θ ∘ φ) ∘ ψ) h (hθ.comp hφψ.tendsto_atTop)
    refine ⟨ψ, hψ, ?_⟩
    exact hcont.2 (fun n => A (φ (ψ n))) (fun n => hA _)
      (hQ.comp hφψ.tendsto_atTop)

/-- **Bounded `√n` local parameters imply mutual contiguity.**

In finite-dimensional Euclidean parameter space, eventual boundedness of
`√n · ‖θ n - θ₀‖` lets every bad subsequence be refined to one on which the
scaled parameter converges.  Applying
`mutuallyContiguous_products_of_dqm_of_scaled_tendsto` on that refinement rules
out failure of either contiguity direction.
-/
theorem mutuallyContiguous_products_of_dqm_of_rootNBounded
    (M : ParametricFamily 𝒳 (EuclideanSpace ℝ (Fin d)))
    (μ : Measure 𝒳)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (ℓ : 𝒳 → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M μ)
    (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (θ : ℕ → EuclideanSpace ℝ (Fin d))
    (hθ : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Real.sqrt n * ‖θ n - θ₀‖ ≤ C) :
    Contiguity.MutuallyContiguous atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => productMeasure M μ (θ n) n) := by
  classical
  obtain ⟨C, hC⟩ := hθ
  have hscaled_bdd : (∀ᶠ n : ℕ in atTop,
      ‖Real.sqrt n • (θ n - θ₀)‖ ≤ max C 0) := by
    filter_upwards [hC] with n hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hn.trans (le_max_left _ _)
  constructor
  · intro A hA hP
    refine SubsequenceLimit.tendsto_of_subseq_tendsto
      (fun n => productMeasure M μ (θ n) n (A n)) 0 ?_
    intro φ hφ
    have hscaled_sub : (∀ᶠ n : ℕ in atTop,
        Real.sqrt (φ n) • (θ (φ n) - θ₀) ∈
          Metric.closedBall 0 (max C 0)) := by
      filter_upwards [hφ.tendsto_atTop.eventually hscaled_bdd] with n hn
      simpa [Metric.mem_closedBall, dist_zero_right] using hn
    have hscaled_freq : (∃ᶠ n : ℕ in atTop,
        Real.sqrt (φ n) • (θ (φ n) - θ₀) ∈
          Metric.closedBall 0 (max C 0)) :=
      hscaled_sub.frequently
    obtain ⟨h, _hh, ψ, hψ, hconv⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (max C 0)).tendsto_subseq'
        hscaled_freq
    have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have hcont := mutuallyContiguous_products_of_dqm_of_scaled_tendsto
      M μ θ₀ ℓ hPDF hℓ hDQM (φ ∘ ψ) hφψ.tendsto_atTop
        ((θ ∘ φ) ∘ ψ) h (by simpa [Function.comp_def] using hconv)
    refine ⟨ψ, hψ, ?_⟩
    exact hcont.1 (fun n => A (φ (ψ n))) (fun n => hA _)
      (hP.comp hφψ.tendsto_atTop)
  · intro A hA hQ
    refine SubsequenceLimit.tendsto_of_subseq_tendsto
      (fun n => productMeasure M μ θ₀ n (A n)) 0 ?_
    intro φ hφ
    have hscaled_sub : (∀ᶠ n : ℕ in atTop,
        Real.sqrt (φ n) • (θ (φ n) - θ₀) ∈
          Metric.closedBall 0 (max C 0)) := by
      filter_upwards [hφ.tendsto_atTop.eventually hscaled_bdd] with n hn
      simpa [Metric.mem_closedBall, dist_zero_right] using hn
    have hscaled_freq : (∃ᶠ n : ℕ in atTop,
        Real.sqrt (φ n) • (θ (φ n) - θ₀) ∈
          Metric.closedBall 0 (max C 0)) :=
      hscaled_sub.frequently
    obtain ⟨h, _hh, ψ, hψ, hconv⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (max C 0)).tendsto_subseq'
        hscaled_freq
    have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
    have hcont := mutuallyContiguous_products_of_dqm_of_scaled_tendsto
      M μ θ₀ ℓ hPDF hℓ hDQM (φ ∘ ψ) hφψ.tendsto_atTop
        ((θ ∘ φ) ∘ ψ) h (by simpa [Function.comp_def] using hconv)
    refine ⟨ψ, hψ, ?_⟩
    exact hcont.2 (fun n => A (φ (ψ n))) (fun n => hA _)
      (hQ.comp hφψ.tendsto_atTop)

end AsymptoticStatistics
