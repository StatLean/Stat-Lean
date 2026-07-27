import StatLean.Bayesian.BernsteinVonMises.Defs
import StatLean.Bayesian.BernsteinVonMises.PriorSmallBall
import StatLean.AsymptoticStatistics.ForMathlib.ContiguityIntegralComparison

/-!
# The contiguity swap: base law vs localized prior mixtures

vdV's proof of Theorem 10.1 constantly exchanges the base law `P^n_{θ₀}` with the Bayesian
mixture `P_{n,U} = ∫ P^n_{θ} dΠ̄ₙ(θ)` over the shrinking prior ball `U/√n` ("we may always
exchange `P_{n,0}` and `P_{n,U}`", p. 141). This file supplies that swap:

* `bvmMixture` — the localized prior mixture `P_{n,U} := iidKernel κ n ∘ₘ π[|B(θ₀, u/√n)]`;
* `bvmMixture_absolutelyContinuous` — `P_{n,U} ≪ κₙ ∘ₘ π` (the predictive), so
  predictive-null exceptional sets of the a.e. posterior identities are `P_{n,U}`-null
  **exactly**;
* `logLikelihood_weakConverges` — asymptotic log-normality of the local log-likelihood ratio
  under `P^n_{θ₀}` (score CLT + LAN residual + Slutsky);
* `mutuallyContiguous_local_alternative` — the support-free per-`h` mutual contiguity
  `P^n_{θ₀} ◁▷ P^n_{θ₀+h/√n}` (via the integral-comparison Le Cam lemma — no common-support
  hypothesis, unlike `contiguous_local_alternatives`);
* `mutuallyContiguous_mixture_base` — the mixture swap `P^n_{θ₀} ◁▷ P_{n,U}`;
* `measure_tendsto_zero_of_predictive_null` — predictive-null (measurable) event sequences
  are asymptotically `P^n_{θ₀}`-null.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, pp. 141–142 (the preliminary contiguity observations), and Chapter 6, §6.4
(Le Cam's first lemma).

**Proof formalization notes.** Per-`h` contiguity routes through
`Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison` with the comparison
supplied by `AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable`
(support-free; vdV Thm 10.1 makes no common-support assumption). The mixture direction uses
the two-sided prior-vs-Lebesgue comparison on small balls (`PriorSmallBall`), an
`L¹`-subsequence extraction (`TendstoInMeasure.exists_seq_tendsto_ae`), a single-`h`
application of the per-`h` lemma along the subsequence (`Contiguous.comp_subseq`), and
`Filter.tendsto_of_subseq_tendsto`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation WeakConverges)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum logLikelihood)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Localized prior mixture** `P_{n,U}`: the marginal law of the `n`-sample when the
parameter is drawn from the prior conditioned to the shrinking ball `B(θ₀, u/√n)`
(vdV p. 141, "`P_{n,U}` for `U` a ball of fixed radius around zero" — here expressed on the
original parameter scale). -/
noncomputable def bvmMixture (κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧) [IsMarkovKernel κ]
    (π : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure π]
    (θ₀ : EuclideanSpace ℝ (Fin k)) (u : ℝ) (n : ℕ) : Measure (Fin n → 𝓧) :=
  iidKernel κ n ∘ₘ (π[|Metric.ball θ₀ (u / Real.sqrt n)])

/-- The localized mixture is dominated by the predictive `κₙ ∘ₘ π` (with density bounded by
the inverse prior small-ball mass). In particular, predictive-null sets are
`bvmMixture`-null. -/
theorem bvmMixture_absolutelyContinuous (u : ℝ) (n : ℕ) :
    bvmMixture κ π θ₀ u n ≪ iidKernel κ n ∘ₘ π := by
  have hc : (π[|Metric.ball θ₀ (u / Real.sqrt n)]) ≪ π := by
    rw [ProbabilityTheory.cond]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
  exact Measure.AbsolutelyContinuous.comp_right hc (iidKernel κ n)

/-- **Asymptotic log-normality of the local log-likelihood ratio** under `P^n_{θ₀}`:
`log(dP^n_{θ₀+h/√n}/dP^n_{θ₀}) ⇝ N(−v/2, v)` with `v = ⟪h, J h⟫` (vdV Theorem 7.2 +
the score CLT + Slutsky). -/
theorem logLikelihood_weakConverges
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
    (h : EuclideanSpace ℝ (Fin k)) (v : NNReal)
    -- LEAN-ONLY: `v` is the quadratic form `⟪h, J h⟫` packaged as `NNReal`
    (hv : (v : ℝ) = ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫) :
    WeakConverges (fun n => (productMeasure M μ θ₀ n).map (logLikelihood M θ₀ h n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  sorry

/-- **Support-free per-`h` mutual contiguity of the local alternatives**
`P^n_{θ₀} ◁▷ P^n_{θ₀+h/√n}` (vdV Example 6.5 for a DQM family; no common-support
hypothesis). -/
theorem mutuallyContiguous_local_alternative
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
    (h : EuclideanSpace ℝ (Fin k)) :
    AsymptoticStatistics.Contiguity.MutuallyContiguous (ι := ℕ)
      (Ω := fun n => Fin n → 𝓧) atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) := by
  sorry

/-- **The contiguity swap** (vdV p. 141: "`P_{n,U} ◁▷ P_{n,0}`"): the base law and the
localized prior mixture are mutually contiguous, given the model and prior conditions of
Theorem 10.1. -/
theorem mutuallyContiguous_mixture_base
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
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hu : 0 < u) :
    AsymptoticStatistics.Contiguity.MutuallyContiguous (ι := ℕ)
      (Ω := fun n => Fin n → 𝓧) atTop
      (fun n => productMeasure M μ θ₀ n)
      (fun n => bvmMixture κ π θ₀ u n) := by
  sorry

/-- **Predictive-null events are asymptotically base-null**: if measurable events `Nₙ` are
null for the predictive `κₙ ∘ₘ π`, then `P^n_{θ₀}(Nₙ) → 0`. This discharges the exceptional
sets of the a.e. posterior identities (`posterior_iid_eq_withDensity_prod_likelihood` etc.)
under the base law. -/
theorem measure_tendsto_zero_of_predictive_null
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
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {N : ∀ n : ℕ, Set (Fin n → 𝓧)}
    -- LEAN-ONLY: measurable exceptional events (regularity)
    (hN_meas : ∀ n, MeasurableSet (N n))
    -- LEAN-ONLY: the events are predictive-null (they carry the a.e. identities)
    (hN : ∀ n, (iidKernel κ n ∘ₘ π) (N n) = 0) :
    Tendsto (fun n => productMeasure M μ θ₀ n (N n)) atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
