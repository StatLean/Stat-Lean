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
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure_isProbabilityMeasure
  logLikelihood_measurable scoreSum_weakly_converges lanResidual_tendsto_productMeasure
  productMeasure_integral_comparison_boundedMeasurable)

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
  classical
  haveI hProb : ∀ θ : EuclideanSpace ℝ (Fin k), ∀ n : ℕ,
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ n
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ w : EuclideanSpace ℝ (Fin k),
      ∫ x, M.density (θ₀ + t • w) x ∂μ = 1 := fun _ _ => hPDF.density_integral_eq_one _
  have hint_perturb : ∀ t : ℝ, ∀ w : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • w)) μ := fun _ _ => hPDF.density_integrable _
  have hScoreCLT := scoreSum_weakly_converges
    M μ θ₀ sc hsc h_one hint h_one_perturb hint_perturb hDQM J hJ_pd.posSemidef hJ
  have hΔ_meas : ∀ n, Measurable (scoreSum sc n) := by
    intro n
    unfold AsymptoticStatistics.AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- The quadratic form as a dot product; `v` is its `toNNReal`.
  have hv_dot : (v : ℝ) = h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    rw [hv]
    change inner ℝ h ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h) = _
    rw [Matrix.inner_toEuclideanCLM]
  have hv_eq : v = (h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal := by
    rw [← hv_dot]; exact Real.toNNReal_coe.symm
  -- Step A: `⟪h, Δₙ⟫ ⇝ N(0, v)`.
  have h_inner_cont : Continuous (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    continuous_const.inner continuous_id
  have h_inner_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    h_inner_cont.measurable
  have h_scalarCLT :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => ⟪h, scoreSum sc n ω⟫)) (ProbabilityTheory.gaussianReal 0 v) := by
    have h_comp : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, scoreSum sc n ω⟫))
        = fun n => ((productMeasure M μ θ₀ n).map (scoreSum sc n)).map
            (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
      funext fun n => (Measure.map_map h_inner_meas (hΔ_meas n)).symm
    rw [h_comp]
    have h_map := hScoreCLT.map h_inner_cont h_inner_meas
    rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h
      hJ_pd.posSemidef] at h_map
    rwa [hv_eq]
  -- Step B: shift by `−v/2`.
  have h_sub_cont : Continuous (fun y : ℝ => y - (v : ℝ) / 2) := by fun_prop
  have h_sub_meas : Measurable (fun y : ℝ => y - (v : ℝ) / 2) := h_sub_cont.measurable
  have h_shiftedCLT :
      WeakConverges (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => ⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_comp : (fun n => (productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2))
        = fun n => ((productMeasure M μ θ₀ n).map
            (fun ω => ⟪h, scoreSum sc n ω⟫)).map (fun y : ℝ => y - (v : ℝ) / 2) :=
      funext fun n => (Measure.map_map h_sub_meas (h_inner_meas.comp (hΔ_meas n))).symm
    rw [h_comp]
    have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
    rwa [ProbabilityTheory.gaussianReal_map_sub_const ((v : ℝ) / 2), zero_sub,
      ← neg_div] at h_map
  -- Step C: Slutsky absorbs the LAN residual.
  have h_lanRes := lanResidual_tendsto_productMeasure
    M μ θ₀ sc hsc h_one hint h_one_perturb hint_perturb hDQM J hJ h
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => ((h_inner_meas.comp (hΔ_meas n)).sub_const _).aemeasurable)
    (fun n => (logLikelihood_measurable M θ₀ h n).aemeasurable) h_shiftedCLT ?_
  intro ε hε
  have h_set_eq : ∀ n : ℕ,
      {ω : Fin n → 𝓧 | ε ≤ dist (⟪h, scoreSum sc n ω⟫ - (v : ℝ) / 2)
          (logLikelihood M θ₀ h n ω)}
        = {ω : Fin n → 𝓧 | ε ≤ |logLikelihood M θ₀ h n ω
            - (⟪h, scoreSum sc n ω⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)|} := by
    intro n
    ext ω
    have hhalf : (v : ℝ) / 2
        = (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
      rw [← hv]; ring
    simp only [Set.mem_setOf_eq, Real.dist_eq, hhalf]
    rw [abs_sub_comm]
  exact (h_lanRes ε hε).congr fun n =>
    congrArg (productMeasure M μ θ₀ n).real (h_set_eq n).symm

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
  classical
  haveI hProb : ∀ θ : EuclideanSpace ℝ (Fin k), ∀ n : ℕ,
      IsProbabilityMeasure (productMeasure M μ θ n) := fun θ n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ n
  have hv_nn : 0 ≤ h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    have := hJ_pd.posSemidef.re_dotProduct_nonneg (x := (h.ofLp : Fin k → ℝ))
    simpa using this
  have hv : ((h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal : ℝ)
      = ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
    rw [Real.coe_toNNReal _ hv_nn]
    change _ = inner ℝ h ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h)
    rw [Matrix.inner_toEuclideanCLM]
  have hcmp := productMeasure_integral_comparison_boundedMeasurable M μ θ₀ sc hsc hDQM hPDF h
  exact AsymptoticStatistics.Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison
    _ _ (fun n => logLikelihood M θ₀ h n)
    (fun n => logLikelihood_measurable M θ₀ h n)
    hcmp _ (logLikelihood_weakConverges hPDF hsc hDQM hJ_pd hJ h _ hv)

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
