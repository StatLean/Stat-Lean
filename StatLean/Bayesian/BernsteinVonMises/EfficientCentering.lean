import StatLean.Bayesian.BernsteinVonMises.Theorem10_1
import StatLean.Bayesian.ForMathlib.GaussianTV

/-!
# Efficient centering: the posterior is approximately `N(θ̂ₙ, (n I_{θ₀})⁻¹)`

The corollary after Theorem 10.1 (vdV p. 144): the centering `Δ_{n,θ₀}` may be replaced by
any **asymptotically efficient** estimator sequence. If `√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} → 0` in
`P^n_{θ₀}`-probability, then on the *original* parameter scale
`‖ P_{Θ̄ | X₁..Xₙ} − N(θ̂ₙ, (n I_{θ₀})⁻¹) ‖ → 0` in `P^n_{θ₀}`-probability.

* `bernstein_von_mises_efficient_centering` — the headline;
* the version on the local scale is an immediate intermediate: replace the mean of the
  Gaussian in `bernstein_von_mises` by `√n(θ̂ₙ − θ₀)` via the mean-shift TV bound.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, p. 144
(the two displays following the proof of Lemma 10.3, including
`‖P_{Θ̄|X₁..Xₙ} − N(θ̂ₙ, n⁻¹ I⁻¹_θ)‖ → 0`).

**Proof formalization notes.** vdV derives the hypothesis `√n(θ̂ₙ − θ) − Δ_{n,θ} →ᵖ 0` from
best-regularity via his Theorem 8.14; here the expansion itself is taken as the definition
of asymptotic efficiency (USER-INPUT), which is exactly what the argument consumes —
best-regularity theory is out of scope for this batch. Chain: triangle with
`bernstein_von_mises`; `tvDist_multivariateGaussian_le` (Pinsker) turns the vanishing
center difference into vanishing TV between the two Gaussians; the unrescaling to the
original parameter scale is `tvDist_map_measurableEmbedding` along `bvmLocalUnscale`
(an affine measurable equivalence for `n ≥ 1`), which sends the local posterior to the
posterior of `Θ̄` and `N(√n(θ̂ₙ−θ₀), J⁻¹)` to `N(θ̂ₙ, (nJ)⁻¹)`
(`multivariateGaussian_map_const_add` + `multivariateGaussian_map_toEuclideanCLM`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)
open StatLean.Minimaxity (tvDist)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Efficient centering** (vdV p. 144). Under the hypotheses of Theorem 10.1, if the
estimator sequence `θ̂ₙ` is asymptotically efficient — i.e.
`√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} → 0` in `P^n_{θ₀}`-probability — then the posterior law of `Θ̄`
itself is approximated by `N(θ̂ₙ, (n)⁻¹ J⁻¹)` in total variation, in
`P^n_{θ₀}`-probability: for every `δ > 0`,
`P^n_{θ₀} { tvDist( (iidKernel κ n)†π ·, N(θ̂ₙ, n⁻¹ • J⁻¹) ) ≥ δ } → 0`. -/
theorem bernstein_von_mises_efficient_centering
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
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {est : ∀ n : ℕ, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)}
    -- LEAN-ONLY: measurable estimators (regularity)
    (hest_meas : ∀ n, Measurable (est n))
    -- USER-INPUT: asymptotic efficiency of `θ̂ₙ` in expansion form,
    -- `√n(θ̂ₙ − θ₀) − Δ_{n,θ₀} →ᵖ 0`; vdV p. 144 (via Thm 8.14, best-regular ⟺ expansion)
    (hest_eff : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - bvmEffScore J sc n ω‖})
        atTop (𝓝 0)) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ tvDist (((iidKernel κ n)†π) ω)
            (multivariateGaussian (est n ω) ((n : ℝ)⁻¹ • J⁻¹))})
        atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
