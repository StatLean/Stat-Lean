import StatLean.Bayesian.BernsteinVonMises.MixtureContiguity
import StatLean.Bayesian.Dominated.PosteriorLintegral
import StatLean.Bayesian.Updating.IID

/-!
# Step A: posterior concentration on `√n`-balls

The first half of the proof of vdV Theorem 10.1: the posterior mass outside the balls
`‖θ − θ₀‖ ≤ Mₙ/√n` tends to zero in `P^n_{θ₀}`-probability, for every `Mₙ → ∞`, given
exponentially powerful tests (Lemma 10.3) and the prior conditions.

* `bvmLocalPosterior_compl_ball` — pushforward bookkeeping: the local posterior's mass
  outside the radius-`Mₙ` ball is the θ-posterior's mass outside the radius-`Mₙ/√n` ball;
* `mixture_posterior_test_bound` — the disintegration/Fubini bound (vdV p. 142, first
  display of Step A): the `P_{n,U}`-mean of `Post(A)(1 − φₙ)` is at most
  `π(Bₙ)⁻¹ ∫_A P^n_θ(1 − φₙ) dπ(θ)`;
* `posterior_mass_compl_ball_tendsto` — the Step-A conclusion.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, p. 142 ("In view of Lemma 10.3 … the first step of the proof").

**Proof formalization notes.** The a.e. posterior identities
(`posterior_iid_eq_withDensity_prod_likelihood`, `posterior_apply_eq_div`) hold
predictive-a.e.; their exceptional sets are killed under `P^n_{θ₀}` by
`measure_tendsto_zero_of_predictive_null`. The test kills the event `{φₙ ≥ 1/2}`-side under
`P^n_{θ₀}` directly (type-I error → 0 and Markov's inequality); the `(1 − φₙ)`-side is
bounded through the mixture by `mixture_posterior_test_bound`, then by Lemma 10.3's
exponential bound integrated against the prior (`prior_tail_split`) and the small-ball lower
bound (`prior_ball_inv_sqrt_lower`), and transferred back by the contiguity swap
(`mutuallyContiguous_mixture_base`).
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

/-- **Pushforward bookkeeping**: for `n ≥ 1`, the local posterior's mass outside the ball of
radius `R` equals the θ-posterior's mass outside the ball of radius `R/√n` around `θ₀`. -/
theorem bvmLocalPosterior_compl_ball [IsFiniteMeasure π] {n : ℕ}
    -- LEAN-ONLY: `√n ≠ 0` needs `1 ≤ n`; the `n = 0` case is junk
    (hn : 1 ≤ n) (ω : Fin n → 𝓧) (R : ℝ) :
    bvmLocalPosterior κ π θ₀ n ω (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) R)ᶜ
      = ((iidKernel κ n)†π) ω {θ | R / Real.sqrt n ≤ ‖θ - θ₀‖} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  rw [bvmLocalPosterior,
    Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _
      Metric.isOpen_ball.measurableSet.compl]
  congr 1
  ext θ
  simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt,
    Set.mem_setOf_eq, bvmLocalScale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq.le]
  rw [div_le_iff₀ hsq, mul_comm]

/-- **The disintegration bound of Step A** (vdV p. 142, first display): for a `[0,1]`-valued
test `φ` and a measurable parameter set `A`, the `bvmMixture`-mean of the posterior mass of
`A` damped by `(1 − φ)` is at most `π(B(θ₀, u/√n))⁻¹ · ∫_A P^n_θ(1 − φ) dπ(θ)`. -/
theorem mixture_posterior_test_bound
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    {u : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hu : 0 < u) (n : ℕ) {φ : (Fin n → 𝓧) → ℝ}
    -- LEAN-ONLY: measurable test (regularity)
    (hφ_meas : Measurable φ)
    -- LEAN-ONLY: `[0,1]`-valued test
    (hφ01 : ∀ ω, φ ω ∈ Set.Icc (0 : ℝ) 1)
    {A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable parameter set (regularity)
    (hA : MeasurableSet A) :
    ∫⁻ ω, ((iidKernel κ n)†π) ω A * ENNReal.ofReal (1 - φ ω)
        ∂(bvmMixture κ π θ₀ u n)
      ≤ (π (Metric.ball θ₀ (u / Real.sqrt n)))⁻¹ *
          ∫⁻ θ in A, ∫⁻ ω, ENNReal.ofReal (1 - φ ω) ∂(iidKernel κ n θ) ∂π := by
  sorry

/-- **Step A: posterior concentration** (vdV p. 142). Under the model, Fisher, test and prior
conditions of Theorem 10.1, for every `Mₙ → ∞` and every `δ > 0`,
`P^n_{θ₀} { posterior mass of {‖θ − θ₀‖ ≥ Mₙ/√n} ≥ δ } → 0`. The tests are taken in the
Lemma-10.3 conclusion shape (`IsExpConsistentTestSeq`), discharged at assembly by
`exponential_tests`. -/
theorem posterior_mass_compl_ball_tendsto
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
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop)
    {φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ} {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by Lemma 10.3)
    (hc : 0 < c)
    -- USER-INPUT: exponentially powerful tests; vdV Lemma 10.3 (discharged at assembly)
    (hφ : IsExpConsistentTestSeq M μ θ₀ Mseq c φ) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ ((iidKernel κ n)†π) ω {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖}})
        atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
