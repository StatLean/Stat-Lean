import StatLean.Bayesian.BayesEstimators.Defs
import StatLean.Bayesian.BayesEstimators.PosteriorTails
import StatLean.Bayesian.BernsteinVonMises.Theorem10_1

/-!
# Uniform approximation of the recentred posterior-risk process

Part 3 of the proof of vdV Theorem 10.8, in recentred form: after the change of variables
`t = τ + Δₙ`, the posterior-risk process approximates the **deterministic** limit criterion
`g = bpeGaussCriterion` uniformly over balls, in `P^n_{θ₀}`-probability:

* `lintegral_loss_bvmGaussian` — the exact recentring identity
  `∫ ℓ(t − h) dN(Δₙ, J⁻¹)(h) = g(t − Δₙ)` (translation pushforward);
* `posteriorRisk_shifted_majorant` — the majorant form of the uniform approximation:
  measurable `Mₙ(ω) → 0` in probability dominating the two-sided deviation
  `|Zₙ(τ + Δₙ) − g(τ)|` over `‖τ‖ ≤ R`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.3, proof of
Theorem 10.8, pp. 148–149 (the processes `Z_{n,M}`, `W_{n,M}` and their comparison).

**Proof formalization notes.** The deviation splits into (i) the truncated part
`∫_{‖h‖ ≤ Mₙ'} ℓ(τ + Δₙ − h) d(Post − N(Δₙ,J⁻¹))`, bounded by
`(sup_{ball} ℓ) · tvDist` (`lintegral_le_lintegral_add_tvDist` + Theorem 10.1); (ii) the
posterior tail, bounded by display (10.9) (`posterior_tail_lintegral_tendsto`); (iii) the
Gaussian tail, bounded by `gaussian_loss_convolution_lt_top`-style domination and score-sum
tightness. The book's `ℓ^∞(K)`-weak-convergence route (Corollary 5.58) is replaced by this
majorant statement — a formalization deviation recorded in `Theorem10_8.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Recentring identity**: the loss average against the random Gaussian is the
deterministic criterion evaluated at the recentred point,
`∫ ℓ(t − h) dN(Δₙ, J⁻¹)(h) = bpeGaussCriterion (t − Δₙ)`. -/
theorem lintegral_loss_bvmGaussian {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ) (n : ℕ) (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)) :
    ∫⁻ h, ℓ (t - h) ∂(bvmGaussian J sc n ω)
      = bpeGaussCriterion J ℓ (t - bvmEffScore J sc n ω) := by
  sorry

/-- **Majorant-form uniform approximation** (vdV pp. 148–149, recentred): there are
measurable `Mₙ : (Fin n → 𝓧) → ℝ≥0∞` vanishing in `P^n_{θ₀}`-probability such that on the
ball `‖τ‖ ≤ R`, the recentred posterior risk `Zₙ(τ + Δₙ)` and the deterministic criterion
`g(τ)` differ by at most `Mₙ` in both directions. -/
theorem posteriorRisk_shifted_majorant
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the tests condition (10.2); vdV Thm 10.1
    (hTests : UniformlyConsistentTests M μ θ₀)
    -- USER-INPUT: the prior condition; vdV Thm 10.1
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ) {p : ℝ}
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial approximation radius
    (hR : 0 < R) :
    ∃ Mn : ∀ n : ℕ, (Fin n → 𝓧) → ℝ≥0∞,
      (∀ n, Measurable (Mn n)) ∧
      (∀ δ : ℝ≥0∞, 0 < δ →
        Tendsto (fun n => productMeasure M μ θ₀ n {ω | δ ≤ Mn n ω}) atTop (𝓝 0)) ∧
      ∀ n (ω : Fin n → 𝓧) (τ : EuclideanSpace ℝ (Fin k)), ‖τ‖ ≤ R →
        bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω
            ≤ bpeGaussCriterion J ℓ τ + Mn n ω ∧
          bpeGaussCriterion J ℓ τ
            ≤ bpePosteriorRisk κ π θ₀ ℓ n (τ + bvmEffScore J sc n ω) ω + Mn n ω := by
  sorry

end StatLean.Bayesian
