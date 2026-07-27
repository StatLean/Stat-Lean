import StatLean.Bayesian.BayesEstimators.Defs
import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
import StatLean.Bayesian.BernsteinVonMises.PriorSmallBall

/-!
# Display (10.9): negligibility of the posterior tails with polynomial weights

The first part of the proof of vdV Theorem 10.8: for every `Mₙ → ∞`, the local posterior
integral of the polynomial envelope `1 + ‖h‖ᵖ` outside the radius-`Mₙ` balls tends to zero
in `P^n_{θ₀}`-probability, provided the prior has a finite `p`-th moment. This strengthens
Step A of Theorem 10.1 from posterior *masses* to *weighted* masses.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.3, proof of
Theorem 10.8, p. 148, display (10.9) and the paragraph deriving it.

**Proof formalization notes.** Identical architecture to `posterior_mass_compl_ball_tendsto`
(the tests kill the `{φₙ ≈ 1}` side; the mixture/Fubini bound handles the `(1 − φₙ)` side),
with the weight `1 + ‖h‖ᵖ` inserted in the Fubini bound and the prior `p`-moment
condition absorbing the polynomial factor in the tail split (vdV: "and use the fact that
`∫ ‖θ‖ᵖ dΠ(θ) < ∞`"). The envelope form suffices for every measurable `f` with
`|f| ≤ 1 + ‖·‖ᵖ` by monotonicity of the lintegral.
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

/-- **Display (10.9)** (vdV p. 148): the polynomial-weighted posterior tails are negligible.
For every `Mₙ → ∞` and `δ > 0`,
`P^n_{θ₀} { ∫_{‖h‖ ≥ Mₙ} (1 + ‖h‖ᵖ) d(local posterior) ≥ δ } → 0`,
given the model/Fisher/prior conditions of Theorem 10.1, exponentially powerful tests
(Lemma 10.3 shape), and the prior moment `∫ ‖θ‖ᵖ dπ < ∞`. -/
theorem posterior_tail_lintegral_tendsto
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
    {p : ℝ}
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: finite prior `p`-moment, `∫ ‖θ‖ᵖ dΠ < ∞`; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.3 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop)
    {φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ} {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by Lemma 10.3)
    (hc : 0 < c)
    -- USER-INPUT: exponentially powerful tests; vdV Lemma 10.3 (discharged at assembly)
    (hφ : IsExpConsistentTestSeq M μ θ₀ Mseq c φ) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ ∫⁻ h in (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (Mseq n))ᶜ,
            ENNReal.ofReal (1 + ‖h‖ ^ p) ∂(bvmLocalPosterior κ π θ₀ n ω)})
        atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
