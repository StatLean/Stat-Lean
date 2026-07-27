import StatLean.Bayesian.BernsteinVonMises.ExponentialTests
import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
import StatLean.Bayesian.BernsteinVonMises.LocalApproximation

/-!
# Theorem 10.1: the Bernstein–von Mises theorem

Assembly of vdV Theorem 10.1. Let the model be an iid sample from a dominated parametric
family that is differentiable in quadratic mean at `θ₀` with nonsingular Fisher information
`J`, let the tests condition (10.2) hold, and let the prior be a probability measure that is
absolutely continuous near `θ₀` with a density continuous and positive at `θ₀`. Then the
total-variation distance between the posterior law of `h = √n(θ − θ₀)` and the random
Gaussian `N(Δ_{n,θ₀}, J⁻¹)`, `Δ_{n,θ₀} = J⁻¹ (n^{-1/2} ∑ sc(Xᵢ))`, tends to zero in
`P^n_{θ₀}`-probability.

* `scoreSum_uniformly_tight` — uniform tightness of the score sums under `P^n_{θ₀}` (from
  the score CLT), feeding the Gaussian-tail side of the triangle inequality;
* `bernstein_von_mises` — the headline, in unrolled in-probability form;
* `bernstein_von_mises_lintegral` — the expectation form
  `∫ tvDist dP^n_{θ₀} → 0` (equivalent since `tvDist ≤ 1`), the form consumed by
  Theorem 10.8.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.2, Theorem 10.1, p. 141 (statement); proof pp. 141–143.

**Proof formalization notes.** Triangle inequality with the conditioned measures (all in
sup-form `tvDist`, half of vdV's `L¹` norm):
`tvDist(Post, N) ≤ tvDist(Post, Post^C) + tvDist(Post^C, N^C) + tvDist(N^C, N)`,
with `C = B̄(0, M)`: the first term is controlled by Step A (`posterior_mass_compl_ball_tendsto`
via `tvDist_cond_le` and `bvmLocalPosterior_compl_ball`), the third by score-sum tightness
plus the mean-uniform Gaussian tail bound
(`multivariateGaussian_compl_closedBall_uniform_small`), the second by Step B
(`local_tv_tendsto`) at fixed `M`; conclude by a `limsup`-in-`M` argument (for every `δ`,
`limsup_n P(tvDist ≥ δ) ≤ ε(M) → 0`). The tests of Lemma 10.3 are supplied by
`exponential_tests`.

**Bibliographic comments.** The theorem's name refers to S. Bernstein, *Theory of
Probability* (Russian), 1917, and R. von Mises, *Wahrscheinlichkeitsrechnung*, Deuticke,
1931, who proved early versions for smooth one-dimensional models; P. S. Laplace's *Mémoire
sur les probabilités des causes par les événements* (1774) contains the germ of the normal
approximation to posteriors. The modern total-variation statement under
quadratic-mean differentiability is due to L. Le Cam — *On some asymptotic properties of
maximum likelihood estimates and related Bayes' estimates*, University of California
Publications in Statistics **1** (1953), 277–330, and *Asymptotic Methods in Statistical
Decision Theory*, Springer, 1986 — with the streamlined testing-condition form in L. Le Cam
and G. L. Yang, *Asymptotics in Statistics: Some Basic Concepts*, Springer, 1990.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Uniform tightness of the score sums** under `P^n_{θ₀}` (a consequence of the score
CLT `scoreSum_weakly_converges`): for every `ε > 0` there is a radius `K` such that
eventually `P^n_{θ₀}(‖scoreSum‖ > K) ≤ ε`. -/
theorem scoreSum_uniformly_tight
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
    {ε : ℝ≥0∞}
    -- LEAN-ONLY: nontrivial tolerance
    (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n {ω | K < ‖scoreSum sc n ω‖} ≤ ε := by
  classical
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n =>
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
  have hscm : ∀ n : ℕ, Measurable (scoreSum sc n) := by
    intro n
    unfold scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  set ν : ℕ → Measure (EuclideanSpace ℝ (Fin k)) :=
    fun n => (productMeasure M μ θ₀ n).map (scoreSum sc n) with hνdef
  haveI hνprob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    rw [hνdef]; exact Measure.isProbabilityMeasure_map (hscm n).aemeasurable
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := inferInstance
  have hweak : AsymptoticStatistics.WeakConverges ν
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    AsymptoticStatistics.AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ sc hsc
      (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun _ _ => hPDF.density_integral_eq_one _) (fun _ _ => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  have htight := AsymptoticStatistics.Prohorov.weakConverges_range_tight ν _ hweak
  rw [AsymptoticStatistics.Prohorov.isTightMeasureSet_range_iff_singleton_tight] at htight
  obtain ⟨C, hCcpt, hC⟩ := htight ε hε
  obtain ⟨K, hKC⟩ := hCcpt.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin k))
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    Filter.Eventually.of_forall fun n => ?_⟩
  have hsub : {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} ⊆ Cᶜ := by
    intro x hx
    intro hxC
    exact absurd (mem_closedBall_zero_iff.1 (hKC hxC))
      (not_le.2 (lt_of_le_of_lt (le_max_left K 1) hx))
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hpre : {ω : Fin n → 𝓧 | max K 1 < ‖scoreSum sc n ω‖}
      = (scoreSum sc n) ⁻¹' {x : EuclideanSpace ℝ (Fin k) | max K 1 < ‖x‖} := rfl
  rw [hpre, ← Measure.map_apply (hscm n) hmeas]
  exact le_trans (measure_mono hsub) (hC n)

/-- **Theorem 10.1 (Bernstein–von Mises).** Let the experiment be an iid sample from the
dominated family `κ θ = p_θ · μ`, differentiable in quadratic mean at `θ₀` with nonsingular
Fisher information `J`; let uniformly consistent tests exist (condition (10.2)); and let the
prior `π` be absolutely continuous near `θ₀` with density continuous and positive at `θ₀`.
Then for every `δ > 0`,
`P^n_{θ₀} { tvDist( posterior law of √n(θ−θ₀), N(Δ_{n,θ₀}, J⁻¹) ) ≥ δ } → 0`. -/
theorem bernstein_von_mises
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information matrix; vdV Thm 10.1
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
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ bvmTV κ π θ₀ J sc n ω}) atTop (𝓝 0) := by
  sorry

/-- **Theorem 10.1, expectation form**: the mean total-variation deviation vanishes,
`∫ tvDist(posterior, Gaussian) dP^n_{θ₀} → 0`. Equivalent to `bernstein_von_mises` since
`tvDist ≤ 1`; this is the form consumed by the Bayes-point-estimator theorem. -/
theorem bernstein_von_mises_lintegral
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information matrix; vdV Thm 10.1
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
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    Tendsto (fun n => ∫⁻ ω, bvmTV κ π θ₀ J sc n ω ∂(productMeasure M μ θ₀ n))
      atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
