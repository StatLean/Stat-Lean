import StatLean.Bayesian.BayesEstimators.UniformApproximation
import StatLean.Bayesian.BayesEstimators.ArgminConsistency
import StatLean.AsymptoticStatistics.ForMathlib.Anderson

/-!
# Theorem 10.8: asymptotics of Bayes point estimators

Assembly of vdV Theorem 10.8. Under the conditions of the Bernstein–von Mises theorem, for a
loss `ℓ` satisfying the separation and polynomial-growth conditions with a matching prior
moment, any (approximate) minimizer `Tₙ` of the posterior risk
`t ↦ ∫ ℓ(√n(t − θ)) dΠ(θ | X₁..Xₙ)` satisfies
`√n(Tₙ − θ₀) − Δ_{n,θ₀} → u₀` in `P^n_{θ₀}`-probability, where `u₀` is the unique
minimizer of the deterministic criterion `g(u) = ∫ ℓ(u − z) dN(0, J⁻¹)(z)`; consequently
`√n(Tₙ − θ₀) ⇝ N(u₀, J⁻¹)`. For bowl-shaped losses `u₀ = 0` (Anderson's lemma), recovering
vdV's "in particular, for every nonzero subconvex loss it converges to `X`".

* `bpe_tight` — Part 2 of vdV's proof: the standardized estimators are uniformly tight;
* `bayes_estimator_asymptotics` — the recentred in-probability headline;
* `bayes_estimator_weakConverges` — the weak-convergence consequence;
* `gaussCriterion_argmin_zero_of_bowlShaped` — `u₀ = 0` for bowl-shaped losses;
* `bayes_estimator_asymptotics_bowlShaped` — the subconvex/bowl-shaped conclusion.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10 (Bayes
Procedures), §10.3 (Point Estimators), Theorem 10.8, p. 147 (statement), proof pp. 147–149.

**Proof formalization notes.** Deviations from the book's proof, recorded once here:
(i) the argmax-CMT/`ℓ^∞(K)` route (Cor. 5.58) is replaced by the recentred majorant
approximation (`posteriorRisk_shifted_majorant`) plus deterministic argmin consistency
(`argmin_tendsto_of_uniform_approx`) applied pointwise on good events — after recentring by
`Δₙ`, the limit criterion is deterministic, so no weak convergence of processes is needed;
(ii) `Tₙ` is only required to be an `εₙ`-approximate minimizer (with `εₙ → 0`), a
generalization; the book's exact-minimizer hypothesis is the case `εₙ = 0`; measurable
selection of `Tₙ` is a hypothesis, as in the book ("this is an implicit assumption");
(iii) the uniqueness proviso "any two minimizers of the limit process coincide a.s." is
taken in the equivalent recentred form: `g` has the strict unique minimizer `u₀`;
(iv) the conclusion is strengthened to convergence in probability of
`√n(Tₙ − θ₀) − Δ_{n,θ₀}` (the book's weak convergence of `√n(Tₙ − θ₀)` to the law of
`X + u₀` follows by the score CLT and Slutsky).

**Bibliographic comments.** Asymptotics of Bayes point estimators for general loss functions
go back to I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic
Theory*, Springer, 1981, Chapters I–III, who treat locally asymptotically normal (and
non-normal) models by direct analysis of the normalized posterior risk; the streamlined
route through the total-variation Bernstein–von Mises theorem is L. Le Cam's (see
*Asymptotic Methods in Statistical Decision Theory*, Springer, 1986, Chapter 12). The
`u₀ = 0` step for symmetric unimodal criteria is T. W. Anderson's integral inequality,
*Proceedings of the American Mathematical Society* **6** (1955), 170–176.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation BowlShaped WeakConverges)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum
  productMeasure_isProbabilityMeasure scoreSum_weakly_converges)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
variable {ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} {p : ℝ}
variable {T : ∀ n : ℕ, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)} {εseq : ℕ → ℝ≥0∞}

/-- **Part 2 of the proof of Theorem 10.8: uniform tightness** of the standardized Bayes
point estimators `√n(Tₙ − θ₀)` (vdV p. 148: the separation condition forces the minimizer
into balls of fixed radius with probability tending to one). -/
theorem bpe_tight
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
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n
          {ω | K ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} ≤ ε := by
  -- LEFT AS DEBT: the statement is FALSE as frozen. vdV's Part-2 argument needs a *positive*
  -- sup–inf gap `inf_{‖y‖ ≥ 2M} ℓ − sup_{‖x‖ ≤ M} ℓ > 0` for some `M`, but the frozen
  -- `SeparatedLoss.strict` field only supplies a single pointwise pair `ℓ x < ℓ y`, which is
  -- strictly weaker. `separatedLoss_zeroOne_no_gap` below exhibits the `0–1` loss as a
  -- witness: it satisfies `SeparatedLoss` and `PolyGrowthLoss 0`, yet has zero gap at every
  -- scale, so its posterior risk `Zₙ(τ) = 1 − Post{τ}` is identically `1` whenever the local
  -- posterior is atomless (e.g. Gaussian location model with Gaussian prior). Every `τ` is
  -- then an exact minimizer, and a measurable selection escaping to infinity satisfies `hT`
  -- with `εseq = 0` while violating the conclusion. Repair: strengthen `SeparatedLoss.strict`
  -- in `Defs.lean` to vdV's genuine sup–inf form (that file is outside this touch-set).
  sorry

/-- **Obstruction witness for `bpe_tight`.** The `0–1` loss `ℓ(u) = 1 − 1_{u = 0}` satisfies
the frozen `SeparatedLoss` (and `PolyGrowthLoss 0`), yet at *every* scale `M > 0` the sup–inf
inequality `sup_{‖x‖ ≤ M} ℓ ≤ inf_{‖y‖ ≥ 2M} ℓ` is an equality — witnessed here by `x, y`
with `‖x‖ ≤ M`, `2M ≤ ‖y‖` and `ℓ y ≤ ℓ x`. So the frozen `strict` field (one pointwise pair
`ℓ x < ℓ y`) does not imply vdV's strict sup–inf separation, which is what Part 2 of the
proof of Theorem 10.8 consumes. -/
private theorem separatedLoss_zeroOne_no_gap (hk : 0 < k) :
    ∃ ℓ01 : EuclideanSpace ℝ (Fin k) → ℝ≥0∞,
      Measurable ℓ01 ∧ SeparatedLoss ℓ01 ∧ PolyGrowthLoss 0 ℓ01 ∧
      ∀ M : ℝ, 0 < M → ∃ x y : EuclideanSpace ℝ (Fin k),
        ‖x‖ ≤ M ∧ 2 * M ≤ ‖y‖ ∧ ℓ01 y ≤ ℓ01 x := by
  classical
  set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : ℝ) with he
  have hnorme : ‖e‖ = 1 := by simp [he]
  have he0 : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorme
    exact zero_ne_one hnorme
  have hsmul : ∀ c : ℝ, 0 < c → ‖c • e‖ = c ∧ c • e ≠ 0 := by
    intro c hc
    refine ⟨by rw [norm_smul, hnorme, mul_one, Real.norm_eq_abs, abs_of_pos hc], ?_⟩
    exact smul_ne_zero hc.ne' he0
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨fun u => if u = 0 then 0 else 1, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin k)))
      measurable_const measurable_const
  · -- monotonicity: any `y` with `2M ≤ ‖y‖` is nonzero, so `ℓ y = 1` dominates
    intro M hM x y _ hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, norm_zero] at hy
      linarith
    rw [if_neg hy0]
    split_ifs <;> simp
  · -- strictness at the single pair `(0, 2e)`
    obtain ⟨hn2, hz2⟩ := hsmul 2 two_pos
    refine ⟨1, one_pos, 0, (2 : ℝ) • e, by simp, ?_, ?_⟩
    · rw [hn2]; norm_num
    · rw [if_pos rfl, if_neg hz2]; exact zero_lt_one
  · -- polynomial growth with exponent `0`
    intro h
    have h2 : ENNReal.ofReal (1 + ‖h‖ ^ (0 : ℝ)) = ENNReal.ofReal 2 := by
      rw [Real.rpow_zero]; norm_num
    change (if h = 0 then (0 : ℝ≥0∞) else 1) ≤ ENNReal.ofReal (1 + ‖h‖ ^ (0 : ℝ))
    rw [h2]
    split_ifs
    · exact zero_le _
    · exact hone
  · -- no gap at any scale: both witnesses are nonzero, so both losses equal `1`
    intro M hM
    obtain ⟨hn1, hz1⟩ := hsmul (M / 2) (by linarith)
    obtain ⟨hn2, hz2⟩ := hsmul (2 * M) (by linarith)
    exact ⟨(M / 2) • e, (2 * M) • e, by rw [hn1]; linarith, by rw [hn2],
      by simp [hz1, hz2]⟩

/-- **Pointwise argmin consistency** (the single-`ω` form of `argmin_tendsto_of_uniform_approx`,
whose sequential shape does not fit the `ω`-wise application needed below): if `τ` is an
`e`-approximate minimizer of `z` over the ball `B̄(0,R)`, `z` approximates `g` within `δ` on
that ball, and the total slack `e + 2δ` undercuts the separation gap `η`, then `τ` is within
`ρ` of the unique minimizer `u₀`. -/
private theorem argmin_close_of_gap {g z : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    {u₀ τ : EuclideanSpace ℝ (Fin k)} {R ρ : ℝ} {η δ e : ℝ≥0∞}
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    (hgap : ∀ u, ‖u‖ ≤ R → ρ ≤ ‖u - u₀‖ → g u₀ + η ≤ g u)
    (hρ : 0 < ρ) (hu₀R : ‖u₀‖ ≤ R) (hτR : ‖τ‖ ≤ R)
    (happrox : ∀ u, ‖u‖ ≤ R → z u ≤ g u + δ ∧ g u ≤ z u + δ)
    (hmin : ∀ u, ‖u‖ ≤ R → z τ ≤ z u + e)
    (hslack : e + (δ + δ) < η) :
    ‖τ - u₀‖ < ρ := by
  by_contra hcon'
  have hcon : ρ ≤ ‖τ - u₀‖ := not_lt.1 hcon'
  have hne : τ ≠ u₀ := by
    intro h
    rw [h, sub_self, norm_zero] at hcon
    exact absurd hcon (not_le.2 hρ)
  have hfin : g u₀ ≠ ∞ := ne_top_of_lt (hunique _ hne)
  have hlow : g u₀ + η ≤ g τ := hgap _ hτR hcon
  have hup : g τ ≤ g u₀ + (e + (δ + δ)) :=
    calc g τ ≤ z τ + δ := (happrox τ hτR).2
      _ ≤ z u₀ + e + δ := by gcongr; exact hmin u₀ hu₀R
      _ ≤ g u₀ + δ + e + δ := by gcongr; exact (happrox u₀ hu₀R).1
      _ = g u₀ + (e + (δ + δ)) := by ring
  exact absurd ((ENNReal.add_le_add_iff_left hfin).1 (hlow.trans hup)) (not_le.2 hslack)

/-- **Theorem 10.8 (Bayes point estimators), recentred form.** Under the Bernstein–von Mises
conditions, the loss conditions, the prior moment, and the uniqueness of the minimizer `u₀`
of the limit criterion `g`, the approximate posterior-risk minimizers satisfy
`√n(Tₙ − θ₀) − Δ_{n,θ₀} → u₀` in `P^n_{θ₀}`-probability. -/
theorem bayes_estimator_asymptotics
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
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV Thm 10.8
    -- ("provided that any two minimizers of this process coincide almost surely")
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖})
        atTop (𝓝 0) := by
  classical
  intro ε hε
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hAdef
  have hAeq : ∀ (n : ℕ) (ω : Fin n → 𝓧), bvmEffScore J sc n ω = A (scoreSum sc n ω) :=
    fun _ _ => by rw [hAdef]; rfl
  refine Metric.tendsto_atTop.2 fun ε' hε' => ?_
  set t : ℝ≥0∞ := ENNReal.ofReal (ε' / 4) with htdef
  have ht0 : 0 < t := by rw [htdef]; exact ENNReal.ofReal_pos.2 (by linarith)
  have httop : t ≠ ∞ := ENNReal.ofReal_ne_top
  -- Part 2: uniform tightness of the estimators; and tightness of the score sums.
  obtain ⟨K₁, hK₁pos, hK₁⟩ := bpe_tight hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ hℓ
    hsep hp hpoly hmom hT_meas hεseq hT t ht0
  obtain ⟨K₂, hK₂pos, hK₂⟩ := scoreSum_uniformly_tight hPDF hsc hDQM hJ_pd hJ ht0
  -- a ball containing both the minimizer and (with high probability) the estimators
  set R : ℝ := ‖u₀‖ + 1 + K₁ + ‖A‖ * K₂ with hRdef
  have hAnn : 0 ≤ ‖A‖ * K₂ := mul_nonneg (norm_nonneg _) hK₂pos.le
  have hu₀R : ‖u₀‖ < R := by rw [hRdef]; linarith
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg u₀) hu₀R
  -- the limit criterion is continuous, hence well-separated at its unique minimizer
  have hg : Continuous (bpeGaussCriterion J ℓ) :=
    AsymptoticStatistics.gaussian_loss_convolution_continuous hJ_pd.inv hℓ hpoly hp
  obtain ⟨η, hη, hgap⟩ := exists_gap_of_unique_argmin hg hunique hu₀R hε
  -- a deterministic majorant tolerance `γ` whose triple undercuts the gap
  set η' : ℝ≥0∞ := min η 1 with hη'def
  have hη'pos : 0 < η' := lt_min hη zero_lt_one
  have hη'top : η' ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set γ : ℝ≥0∞ := η' / 2 / 2 with hγdef
  have hγpos : 0 < γ := ENNReal.half_pos (ENNReal.half_pos hη'pos.ne').ne'
  have hγsum : γ + γ < η := by
    rw [hγdef, ENNReal.add_halves]
    exact lt_of_lt_of_le (ENNReal.half_lt_self hη'pos.ne' hη'top) (min_le_left _ _)
  -- Part 3: the uniform majorant approximation of the recentred posterior risk
  obtain ⟨Mn, -, hMn_tendsto, hMn_approx⟩ :=
    posteriorRisk_shifted_majorant hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ hℓ hp hpoly
      hmom hR
  have hslack : ∀ᶠ n : ℕ in atTop, εseq n + (γ + γ) < η := by
    have hlim : Tendsto (fun n => εseq n + (γ + γ)) atTop (𝓝 (0 + (γ + γ))) :=
      hεseq.add tendsto_const_nhds
    rw [zero_add] at hlim
    exact (tendsto_order.1 hlim).2 η hγsum
  have hbad3 : ∀ᶠ n : ℕ in atTop,
      productMeasure M μ θ₀ n {ω | γ ≤ Mn n ω} < t :=
    (tendsto_order.1 (hMn_tendsto γ hγpos)).2 t ht0
  refine Filter.eventually_atTop.1 ?_
  filter_upwards [hK₁, hK₂, hbad3, hslack] with n h1 h2 h3 h4
  -- the bad event is covered by the three tight events
  have hsub : {ω : Fin n → 𝓧 |
        ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖} ⊆
      {ω | K₁ ≤ ‖Real.sqrt n • (T n ω - θ₀)‖} ∪
        ({ω | K₂ < ‖scoreSum sc n ω‖} ∪ {ω | γ ≤ Mn n ω}) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_lt] at hnot
    obtain ⟨hb1, hb2, hb3⟩ := hnot
    simp only [Set.mem_setOf_eq] at hω
    set Rn : EuclideanSpace ℝ (Fin k) :=
      Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω with hRn
    have hΔnorm : ‖bvmEffScore J sc n ω‖ ≤ ‖A‖ * K₂ := by
      rw [hAeq n ω]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb2 (norm_nonneg A))
    have hRnR : ‖Rn‖ ≤ R := by
      have hle := norm_sub_le (Real.sqrt n • (T n ω - θ₀)) (bvmEffScore J sc n ω)
      rw [← hRn] at hle
      rw [hRdef]
      linarith [norm_nonneg u₀]
    have hminz : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ R →
        bpePosteriorRisk κ π θ₀ ℓ n (Rn + bvmEffScore J sc n ω) ω
          ≤ bpePosteriorRisk κ π θ₀ ℓ n (u + bvmEffScore J sc n ω) ω + εseq n := by
      intro u _
      have hid : Rn + bvmEffScore J sc n ω = Real.sqrt n • (T n ω - θ₀) := by
        rw [hRn]; abel
      rw [hid]
      exact hT n ω (u + bvmEffScore J sc n ω)
    have hsl : εseq n + (Mn n ω + Mn n ω) < η :=
      lt_of_le_of_lt (by gcongr) h4
    have hclose : ‖Rn - u₀‖ < ε :=
      argmin_close_of_gap hunique hgap hε hu₀R.le hRnR
        (fun u hu => hMn_approx n ω u hu) hminz hsl
    exact absurd hω (not_le.2 hclose)
  -- assemble the three probability bounds
  have hle : productMeasure M μ θ₀ n
      {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖} ≤ t + (t + t) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    exact add_le_add h1 ((measure_union_le _ _).trans (add_le_add h2 h3.le))
  have hsumtop : t + (t + t) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨httop, ENNReal.add_ne_top.2 ⟨httop, httop⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hcalc : (t + (t + t)).toReal = 3 * (ε' / 4) := by
    rw [ENNReal.toReal_add httop (ENNReal.add_ne_top.2 ⟨httop, httop⟩),
      ENNReal.toReal_add httop httop, htdef, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc (productMeasure M μ θ₀ n).real
        {ω | ε ≤ ‖Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀‖}
      ≤ (t + (t + t)).toReal := ENNReal.toReal_mono hsumtop hle
    _ = 3 * (ε' / 4) := hcalc
    _ < ε' := by linarith

/-- **Theorem 10.8, weak-convergence form**: `√n(Tₙ − θ₀) ⇝ N(u₀, J⁻¹)` under `P^n_{θ₀}`
(the law of `X + u₀` for `X ∼ N(0, J⁻¹)`, i.e. of the minimizer of the limit process). -/
theorem bayes_estimator_weakConverges
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
    -- LEAN-ONLY: measurable loss (regularity)
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV Thm 10.8
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => Real.sqrt n • (T n ω - θ₀)))
      (multivariateGaussian u₀ J⁻¹) := by
  classical
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  haveI hGprob : IsProbabilityMeasure (multivariateGaussian u₀ J⁻¹) := inferInstance
  -- measurability of the score sums and of the estimators
  have hscsum : ∀ n : ℕ, Measurable (scoreSum sc n) := by
    intro n
    unfold AsymptoticStatistics.AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hsc.comp (measurable_pi_apply i))).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  -- the affine map `z ↦ u₀ + J⁻¹ z`
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ with hA
  have hfc : Continuous fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z :=
    continuous_const.add A.continuous
  have hfm : Measurable fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z :=
    measurable_const.add A.measurable
  -- the score CLT `scoreSum ⇝ N(0, J)`
  have hCLT := scoreSum_weakly_converges M μ θ₀ sc hsc (hPDF.density_integral_eq_one θ₀)
    (hPDF.density_integrable θ₀) (fun _ _ => hPDF.density_integral_eq_one _)
    (fun _ _ => hPDF.density_integrable _) hDQM J hJ_pd.posSemidef hJ
  -- push forward by the affine map: `u₀ + Δₙ ⇝ N(u₀, J⁻¹)`
  have hlim : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
      (fun z => u₀ + A z) = multivariateGaussian u₀ J⁻¹ := by
    rw [show (fun z : EuclideanSpace ℝ (Fin k) => u₀ + A z) = (fun x => u₀ + x) ∘ A from rfl,
      ← Measure.map_map (measurable_const_add u₀) A.measurable,
      show (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map A
        = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ from
        AsymptoticStatistics.multivariateGaussian_map_matrix_inv hJ_pd,
      AsymptoticStatistics.multivariateGaussian_map_const_add]
  have hX : WeakConverges (fun n => (productMeasure M μ θ₀ n).map
      (fun ω => u₀ + bvmEffScore J sc n ω)) (multivariateGaussian u₀ J⁻¹) := by
    have hmap := hCLT.map hfc hfm
    rw [hlim] at hmap
    have hcomp : ∀ n : ℕ, ((productMeasure M μ θ₀ n).map (scoreSum sc n)).map
        (fun z => u₀ + A z) = (productMeasure M μ θ₀ n).map
          (fun ω => u₀ + bvmEffScore J sc n ω) := by
      intro n
      rw [Measure.map_map hfm (hscsum n)]
      rfl
    simpa only [hcomp] using hmap
  -- Slutsky: the estimators differ from `u₀ + Δₙ` by an `oₚ(1)`
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => u₀ + bvmEffScore J sc n ω)
    (Y := fun n ω => Real.sqrt n • (T n ω - θ₀))
    (fun n => (measurable_const.add (A.measurable.comp (hscsum n))).aemeasurable)
    (fun n => (((hT_meas n).sub measurable_const).const_smul
      (Real.sqrt (n : ℝ))).aemeasurable) hX ?_
  intro ε hε
  have hkey := bayes_estimator_asymptotics hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
    hℓ hsep hp hpoly hmom hT_meas hεseq hT hunique ε hε
  refine hkey.congr fun n => ?_
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, dist_eq_norm]
  rw [show u₀ + bvmEffScore J sc n ω - Real.sqrt n • (T n ω - θ₀)
      = -(Real.sqrt n • (T n ω - θ₀) - bvmEffScore J sc n ω - u₀) by abel, norm_neg]

/-- **Anderson step**: for a bowl-shaped loss, the unique minimizer of the limit criterion
is the origin (`anderson_lemma_loss` gives `g(0) ≤ g(u)`; uniqueness upgrades it to
`u₀ = 0`). -/
theorem gaussCriterion_argmin_zero_of_bowlShaped
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- USER-INPUT: bowl-shaped loss; vdV §8.2 / Lemma 8.5
    (hL : BowlShaped ℓ) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV Thm 10.8
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    u₀ = 0 := by
  -- Anderson's lemma: the criterion is minimized at the origin.
  have hmin : ∀ u, bpeGaussCriterion J ℓ 0 ≤ bpeGaussCriterion J ℓ u := by
    intro u
    have hzero : bpeGaussCriterion J ℓ 0
        = ∫⁻ z, ℓ z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
      simp only [bpeGaussCriterion, zero_sub]
      exact lintegral_congr fun z => hL.symm z
    have hu : bpeGaussCriterion J ℓ u
        = ∫⁻ z, ℓ (z + -u) ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
      refine lintegral_congr fun z => ?_
      rw [← hL.symm (u - z)]
      congr 1
      abel
    rw [hzero, hu]
    exact AsymptoticStatistics.anderson_lemma_loss hJ_pd.inv.posSemidef hL (-u)
  by_contra hne
  exact absurd (hmin u₀) (not_le.2 (hunique 0 (Ne.symm hne)))

/-- **Theorem 10.8 for bowl-shaped losses** (vdV: "In particular, for every nonzero,
subconvex loss function it converges to `X`"): the standardized Bayes estimators are
asymptotically efficient, `√n(Tₙ − θ₀) ⇝ N(0, J⁻¹)`. -/
theorem bayes_estimator_asymptotics_bowlShaped
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
    -- USER-INPUT: bowl-shaped loss; vdV §8.2 / Lemma 8.5
    (hL : BowlShaped ℓ)
    -- USER-INPUT: the loss separation condition; vdV §10.3, p. 147
    (hsep : SeparatedLoss ℓ)
    -- LEAN-ONLY: nonnegative growth exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p)
    -- USER-INPUT: polynomial growth of the loss; vdV §10.3, p. 147
    (hpoly : PolyGrowthLoss p ℓ)
    -- USER-INPUT: finite prior `p`-moment; vdV Thm 10.8
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞)
    -- LEAN-ONLY: measurable estimators (vdV p. 147: "an implicit assumption")
    (hT_meas : ∀ n, Measurable (T n))
    -- LEAN-ONLY: vanishing minimization tolerance (`εₙ = 0` is the book's exact case)
    (hεseq : Tendsto εseq atTop (𝓝 0))
    -- USER-INPUT: `Tₙ` approximately minimizes the posterior risk; vdV §10.3, p. 147
    (hT : ∀ n (ω : Fin n → 𝓧) (t : EuclideanSpace ℝ (Fin k)),
      bpePosteriorRisk κ π θ₀ ℓ n (Real.sqrt n • (T n ω - θ₀)) ω
        ≤ bpePosteriorRisk κ π θ₀ ℓ n t ω + εseq n)
    {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the limit criterion has the unique minimizer `u₀`; vdV Thm 10.8
    (hunique : ∀ u, u ≠ u₀ → bpeGaussCriterion J ℓ u₀ < bpeGaussCriterion J ℓ u) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => Real.sqrt n • (T n ω - θ₀)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
  have hu₀ : u₀ = 0 := gaussCriterion_argmin_zero_of_bowlShaped hJ_pd hL hunique
  subst hu₀
  exact bayes_estimator_weakConverges hPDF hsc hDQM hJ_pd hJ hκ hM_joint hTests hπ
    hL.measurable hsep hp hpoly hmom hT_meas hεseq hT hunique

end StatLean.Bayesian
