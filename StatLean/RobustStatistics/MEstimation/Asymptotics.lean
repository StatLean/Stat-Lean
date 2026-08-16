import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import StatLean.AsymptoticStatistics.Consistency.OneDimMonotoneConsistency
import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Asymptotics of location M-estimators — by reuse of StatLean Z-estimation theory

Consistency and asymptotic normality of monotone location M-estimators (`MMY §10.2–10.3`,
Theorems 10.5 and 10.7): under i.i.d. sampling from `P`, a near-root sequence `θ̂ₙ` of the
empirical M-equation tends in probability to the population root `θ₀`, and

$$\sqrt n\,(\hat\theta_n - \theta_0) \Rightarrow
  N\!\left(0,\ \frac{E_P\,\psi(x-\theta_0)^2}{\big(E_P\,\psi'(x-\theta_0)\big)^2}\right)$$

(`MMY` eq. (2.24)–(2.25)). Per the charter, this file *reuses* the general machinery of
`StatLean/AsymptoticStatistics` rather than re-proving it:

* consistency instantiates `AsymptoticStatistics.Consistency.oneDim_monotone_zEstimator_consistent`
  (vdV Lemma 5.10) with the empirical score `θ ↦ -n⁻¹ ∑ ψ(Xᵢ - θ)` and the LLN
  `iid_lln_in_prob_seq`;
* Huber asymptotic normality instantiates the Lipschitz-score route
  `AsymptoticStatistics.EmpiricalProcess.zEstimator_asymptotic_normality` (vdV Theorem
  5.21), which needs no differentiability of `ψ` — exactly right for the kinked Huber
  score, whose population score is differentiable at `θ₀` once `P` has no atoms at the
  clipping knots.

**Hypothesis discipline.** The sign conditions on the population score encode the
identification of `θ₀` (`MMY` (10.7)); the near-root conditions describe how the
estimator sequence was constructed. Both are genuine external inputs. The LLN, the
CLT for the empirical score, and the differentiability of the population score at `θ₀`
are *derived internally* from the i.i.d. inputs.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.3.2 (eq.
(2.22)–(2.25)), §10.2 (Thm 10.5), §10.3 (Thm 10.7). Cross-reference: van der Vaart,
*Asymptotic Statistics*, Lemma 5.10 and Theorem 5.21 (`vdV §5.2–5.3`).
-/

open MeasureTheory Filter Topology AsymptoticStatistics

namespace StatLean.RobustStatistics

/-- **Consistency of monotone location M-estimators** (`MMY` Theorem 10.5; vdV Lemma
5.10): under i.i.d. sampling from `P`, any near-root sequence of the empirical M-equation
for a bounded monotone continuous score tends in probability to the population root `θ₀`
identified by the sign change of the population score. -/
theorem mLocation_consistent
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {ψ : ℝ → ℝ} {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} {θhat : ℕ → Ξ → ℝ}
    -- USER-INPUT: i.i.d. data with common law P; MMY §10.2
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: continuous monotone bounded score (ψ-function shape); MMY Def 2.2, §2.3.1
    (hψc : Continuous ψ) (hψm : Monotone ψ) (hψb : ∃ C, ∀ u, |ψ u| ≤ C)
    -- USER-INPUT: θ₀ is identified — the population score changes sign strictly at θ₀;
    -- MMY Thm 10.5 / eq. (10.7)
    (hsign_lt : ∀ θ < θ₀, 0 < mLocationScore ψ P θ)
    (hsign_gt : ∀ θ, θ₀ < θ → mLocationScore ψ P θ < 0)
    -- USER-INPUT: θ̂ₙ nearly solves the empirical M-equation (in probability); MMY (10.1)
    (hnear : TendstoInMeasure μ
      (fun (n : ℕ) ξ => (n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X i ξ - θhat n ξ)) atTop
      (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => μ {ξ | ε ≤ |θhat n ξ - θ₀|}) atTop (𝓝 0) := by
  classical
  have hψmeas : Measurable ψ := hψc.measurable
  obtain ⟨C, hC⟩ := hψb
  -- The *negated* empirical score. `ψ` is nondecreasing and `θ ↦ x − θ` is antitone, so
  -- `θ ↦ n⁻¹∑ψ(Xᵢ − θ)` is nonincreasing; negating it produces the nondecreasing random
  -- criterion required by vdV Lemma 5.10, and flips the sign conditions into place.
  refine Consistency.oneDim_monotone_zEstimator_consistent_univ
    (Ψn := fun n ξ θ => -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X i ξ - θ)))
    (Ψ := fun θ => -(mLocationScore ψ P θ)) ?_ ?_ ?_ ?_ ?_
  · -- Monotonicity in `θ` of the negated empirical score.
    intro n ξ a b hab
    simp only [neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hψm (by linarith))
      (by positivity)
  · -- Pointwise convergence in probability: the i.i.d. weak law at the fixed `θ`.
    intro θ
    have hgm : Measurable fun x : ℝ => ψ (x - θ) := hψmeas.comp (measurable_id.sub_const θ)
    have hgi : Integrable (fun x : ℝ => ψ (x - θ)) P :=
      Integrable.mono' (integrable_const C) hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC (x - θ))
    have hlln := iid_lln_in_prob_seq P (fun x : ℝ => ψ (x - θ)) hgm hgi μ X
      hX_meas hX_indep hX_id hX_law
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro ε hε
    refine (hlln ε hε).congr fun n => ?_
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq, EmpiricalProcess.empiricalAvg, mLocationScore]
    rw [show -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X (i : ℕ) ξ - θ)) - -(∫ x, ψ (x - θ) ∂P)
        = -((n : ℝ)⁻¹ * ∑ i : Fin n, ψ (X (i : ℕ) ξ - θ) - ∫ x, ψ (x - θ) ∂P) from by ring,
      norm_neg]
  · -- Near-root condition: negate the hypothesis.
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine ((tendstoInMeasure_iff_norm.mp hnear) ε hε).congr fun n => ?_
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq, sub_zero, norm_neg]
  · exact fun θ hθ => neg_lt_zero.mpr (hsign_lt θ hθ)
  · exact fun θ hθ => neg_pos.mpr (hsign_gt θ hθ)

/-- **Consistency of the Huber location estimator** (`MMY §2.3.2` + Thm 10.5): the Huber
score is continuous, monotone and bounded, so any near-root sequence tends to the
population Huber root identified by the sign conditions. -/
theorem huberLocation_consistent
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} {θhat : ℕ → Ξ → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: identification of θ₀; MMY Thm 10.5 / eq. (10.7)
    (hsign_lt : ∀ θ < θ₀, 0 < mLocationScore (huberPsi c) P θ)
    (hsign_gt : ∀ θ, θ₀ < θ → mLocationScore (huberPsi c) P θ < 0)
    -- USER-INPUT: near-root sequence; MMY (10.1)
    (hnear : TendstoInMeasure μ
      (fun (n : ℕ) ξ => (n : ℝ)⁻¹ * ∑ i : Fin n, huberPsi c (X i ξ - θhat n ξ)) atTop
      (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => μ {ξ | ε ≤ |θhat n ξ - θ₀|}) atTop (𝓝 0) :=
  mLocation_consistent hX_meas hX_indep hX_id hX_law (huberPsi_continuous c)
    (huberPsi_monotone c) ⟨c, abs_huberPsi_le hc.le⟩ hsign_lt hsign_gt hnear

/-- **The asymptotic variance of the Huber location estimator** (`MMY` eq. (2.25)):
`v = E_P ψ_c(x-θ₀)² / P(|x-θ₀| < c)²`. -/
noncomputable def huberAsymptoticVariance (P : Measure ℝ) (c θ₀ : ℝ) : ℝ :=
  (∫ x, huberPsi c (x - θ₀) ^ 2 ∂P) / (P.real {x | |x - θ₀| < c}) ^ 2

/-- Above the upper knot the Huber score is the constant `c`. (Branch formula for the
derivative computation below; `Huber.lean` only exports the central-region formula.) -/
private theorem huberPsi_of_clip_le {c u : ℝ} (hc : 0 ≤ c) (h : c ≤ u) : huberPsi c u = c := by
  unfold huberPsi
  rw [min_eq_left h, max_eq_right (by linarith)]

/-- Below the lower knot the Huber score is the constant `-c`. -/
private theorem huberPsi_of_le_neg_clip {c u : ℝ} (hc : 0 ≤ c) (h : u ≤ -c) :
    huberPsi c u = -c := by
  unfold huberPsi
  rw [min_eq_right (by linarith), max_eq_left h]

/-- **Off the two clipping knots `x = θ₀ ± c` the map `θ ↦ ψ_c(x − θ)` is differentiable at
`θ₀`.** The derivative is `-1` on the central region `|x − θ₀| < c` and `0` outside it —
exactly the indicator whose `P`-integral is the `B = -P(|x − θ₀| < c)` of `MMY` Thm 10.7.
No two-sided gluing is needed: each of the three regions is *open* in `θ` around `θ₀`, so
the branch formula holds on a whole neighbourhood and `congr_of_eventuallyEq` applies. -/
private theorem hasDerivAt_huberPsi_sub {c θ₀ x : ℝ} (hc : 0 < c) (hx : |x - θ₀| ≠ c) :
    HasDerivAt (fun θ => huberPsi c (x - θ))
      (Set.indicator {y : ℝ | |y - θ₀| < c} (fun _ => (-1 : ℝ)) x) θ₀ := by
  rcases lt_or_gt_of_ne hx with hin | hout
  · -- Central region: `ψ_c(x − θ) = x − θ` on the open set `{θ | |x − θ| < c}`.
    rw [Set.indicator_of_mem (show x ∈ {y : ℝ | |y - θ₀| < c} from hin)]
    have h1 : HasDerivAt (fun θ : ℝ => x - θ) (-1 : ℝ) θ₀ := by
      simpa using (hasDerivAt_id θ₀).const_sub x
    refine h1.congr_of_eventuallyEq ?_
    have hopen : IsOpen {θ : ℝ | |x - θ| < c} :=
      isOpen_lt (continuous_const.sub continuous_id).abs continuous_const
    filter_upwards [hopen.mem_nhds (show |x - θ₀| < c from hin)] with θ hθ
    exact huberPsi_of_abs_le hc.le (le_of_lt hθ)
  · -- Outside the central region the score is locally constant (`c` or `-c`).
    rw [Set.indicator_of_notMem (by simpa using hout.le)]
    rcases lt_abs.mp hout with hA | hB
    · refine (hasDerivAt_const θ₀ c).congr_of_eventuallyEq ?_
      have hopen : IsOpen {θ : ℝ | c < x - θ} :=
        isOpen_lt continuous_const (continuous_const.sub continuous_id)
      filter_upwards [hopen.mem_nhds (show c < x - θ₀ from hA)] with θ hθ
      exact huberPsi_of_clip_le hc.le (le_of_lt hθ)
    · refine (hasDerivAt_const θ₀ (-c)).congr_of_eventuallyEq ?_
      have hopen : IsOpen {θ : ℝ | x - θ < -c} :=
        isOpen_lt (continuous_const.sub continuous_id) continuous_const
      filter_upwards [hopen.mem_nhds (show x - θ₀ < -c from by linarith)] with θ hθ
      exact huberPsi_of_le_neg_clip hc.le (le_of_lt hθ)

/-- Private, earlier-placed copy of `hasDerivAt_mLocationScore_huber` (below): the
normality theorem needs the population score's derivative *before* the frozen statement's
position in the file. The frozen theorem is this lemma verbatim. -/
private theorem hasDerivAt_mLocationScore_huber_aux
    {P : Measure ℝ} [IsProbabilityMeasure P] {c θ₀ : ℝ} (hc : 0 < c)
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0) :
    HasDerivAt (mLocationScore (huberPsi c) P) (-(P.real {x | |x - θ₀| < c})) θ₀ := by
  classical
  set S : Set ℝ := {x : ℝ | |x - θ₀| < c} with hS_def
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_id.sub_const θ₀).abs measurable_const
  have hF'meas : Measurable (Set.indicator S (fun _ => (-1 : ℝ))) :=
    measurable_const.indicator hS
  -- The knot set `{x | |x − θ₀| = c} = {θ₀+c, θ₀−c}` is `P`-null: this is precisely where
  -- the atom hypotheses enter.
  have hnull : P {x : ℝ | |x - θ₀| = c} = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h_atom_add h_atom_sub)
    simp only [Set.mem_setOf_eq] at hx
    have : x = θ₀ + c ∨ x = θ₀ - c := by
      rcases (abs_eq hc.le).mp hx with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases this with h | h <;> simp [h]
  have hae : ∀ᵐ x ∂P, |x - θ₀| ≠ c := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have h_diff : ∀ᵐ x ∂P,
      HasDerivAt (fun θ => huberPsi c (x - θ)) (Set.indicator S (fun _ => (-1 : ℝ)) x) θ₀ := by
    filter_upwards [hae] with x hx using hasDerivAt_huberPsi_sub hc hx
  -- The parameter-Lipschitz domination: `θ ↦ ψ_c(x − θ)` is `1`-Lipschitz, uniformly in `x`,
  -- so the constant `1` is an (integrable) Lipschitz bound.
  have h_lip : ∀ᵐ x ∂P, LipschitzOnWith (Real.nnabs ((fun _ : ℝ => (1 : ℝ)) x))
      (fun θ => huberPsi c (x - θ)) Set.univ := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 : LipschitzWith 1 (fun θ : ℝ => huberPsi c (x - θ)) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h := (huberPsi_lipschitz c).dist_le_mul (x - a) (x - b)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h ⊢
      calc |huberPsi c (x - a) - huberPsi c (x - b)| ≤ |x - a - (x - b)| := h
        _ = |a - b| := by rw [show x - a - (x - b) = -(a - b) from by ring, abs_neg]
    simpa [show Real.nnabs (1 : ℝ) = 1 from by ext; simp] using
      (lipschitzOnWith_univ (K := 1) (f := fun θ : ℝ => huberPsi c (x - θ))).mpr h1
  have hcont : Continuous fun x : ℝ => huberPsi c (x - θ₀) :=
    (huberPsi_continuous c).comp (continuous_id.sub continuous_const)
  have hF_meas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (fun x : ℝ => huberPsi c (x - θ)) P :=
    Filter.Eventually.of_forall fun θ =>
      ((huberPsi_continuous c).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hF_int : Integrable (fun x : ℝ => huberPsi c (x - θ₀)) P :=
    Integrable.mono' (integrable_const c) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using abs_huberPsi_le hc.le (x - θ₀))
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun θ x => huberPsi c (x - θ)) (x₀ := θ₀) (s := Set.univ)
    (bound := fun _ : ℝ => (1 : ℝ)) (F' := Set.indicator S (fun _ => (-1 : ℝ)))
    Filter.univ_mem hF_meas hF_int hF'meas.aestronglyMeasurable h_lip
    (integrable_const 1) h_diff
  have hval : ∫ x, Set.indicator S (fun _ => (-1 : ℝ)) x ∂P = -(P.real S) := by
    rw [integral_indicator_const (-1 : ℝ) hS]
    simp
  rw [hval] at hderiv
  exact hderiv

/-! ### `ℝ ↔ EuclideanSpace ℝ (Fin 1)` packaging for the `k = 1` instantiation

The Z-estimation engine carries its parameter in `EuclideanSpace ℝ (Fin k)`; the location
model is `k = 1`. These private helpers are the coordinate dictionary. -/

/-- The `Fin 1` Euclidean packaging of a real parameter. -/
private noncomputable def packFin1 (t : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single (0 : Fin 1) t

@[simp] private theorem packFin1_apply (t : ℝ) : (packFin1 t) 0 = t := by
  simp [packFin1]

/-- In one dimension the Euclidean norm *is* the absolute value of the single coordinate. -/
private theorem norm_euclideanFin1 (y : EuclideanSpace ℝ (Fin 1)) : ‖y‖ = |y 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

private theorem continuous_packFin1 : Continuous packFin1 :=
  LipschitzWith.continuous (K := 1)
    (LipschitzWith.of_dist_le_mul fun a b => by
      simp [packFin1, EuclideanSpace.dist_single_same])

/-- The coordinate functional as an inner product against `packFin1 1` — the form in which
`multivariateGaussian_map_inner_eq_gaussianReal` identifies the one-dimensional marginal. -/
private theorem inner_packFin1_one (y : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (packFin1 1) y = y 0 := by
  have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) (0 : Fin 1) (1 : ℝ) y
  simpa [packFin1] using h

/-- The Huber estimating function packaged as the `k = 1` criterion family of the
Z-estimation engine: one coordinate, evaluated at the single parameter coordinate. -/
private noncomputable def huberPsiFin1 (c : ℝ) :
    EuclideanSpace ℝ (Fin 1) → Fin 1 → (ℝ → ℝ) :=
  fun θ _ x => huberPsi c (x - θ 0)

/-- **Asymptotic normality of the Huber location estimator** (`MMY` Theorem 10.7 with eq.
(2.24)–(2.25); via vdV Theorem 5.21, the Lipschitz-score route): a consistent near-root
sequence at rate `o_P(n^{-1/2})` satisfies
`√n (θ̂ₙ - θ₀) ⇒ N(0, E ψ_c²/(P(|x-θ₀|<c))²)`. The absence of atoms at the clipping
knots makes the population score differentiable at `θ₀` with derivative
`-P(|x-θ₀| < c)`; that Fréchet condition is derived internally, not assumed. -/
theorem huberLocation_asymptoticNormal
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) {θ₀ : ℝ}
    {X : ℕ → Ξ → ℝ} {θhat : ℕ → Ξ → ℝ}
    -- USER-INPUT: i.i.d. data with common law P; MMY §10.3
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    -- USER-INPUT: θ₀ solves the population Huber equation; MMY (2.22)
    (hroot : IsMLocationRoot (huberPsi c) P θ₀)
    -- USER-INPUT: no atoms at the clipping knots; MMY §10.3 (Example 10.4: F continuous)
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0)
    -- USER-INPUT: nondegenerate central mass (B ≠ 0 in Thm 10.7)
    (hmass : 0 < P.real {x | |x - θ₀| < c})
    -- LEAN-ONLY: measurable estimator sequence, for the image laws to exist
    (hθhat_meas : ∀ n, Measurable (θhat n))
    -- USER-INPUT: consistency of the estimator sequence (from `huberLocation_consistent`);
    -- MMY Thm 10.5
    (h_consist : ∀ ε > (0 : ℝ), Tendsto (fun n => μ {ξ | ε ≤ |θhat n ξ - θ₀|}) atTop (𝓝 0))
    -- USER-INPUT: the estimating equation is solved at rate o_P(n^{-1/2}); MMY (10.1),
    -- vdV Thm 5.21 estimating-equation condition
    (h_est_eq : TendstoInMeasure μ
      (fun (n : ℕ) ξ => Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i : Fin n, huberPsi c (X i ξ - θhat n ξ)))
      atTop (fun _ => (0 : ℝ))) :
    WeakConverges
      (fun n => μ.map (fun ξ => Real.sqrt n * (θhat n ξ - θ₀)))
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (huberAsymptoticVariance P c θ₀))) := by
  sorry

/-- **The population Huber score is differentiable at `θ₀` with derivative the negative
central mass** (the `B` of `MMY` Theorem 10.7 for the Huber score): derived from the
Lipschitz score and the absence of atoms at the knots, via differentiation under the
integral. Named separately because it is the analytic heart of the normality proof. -/
theorem hasDerivAt_mLocationScore_huber {P : Measure ℝ} [IsProbabilityMeasure P] {c θ₀ : ℝ}
    (hc : 0 < c)
    -- USER-INPUT: no atoms at the clipping knots; MMY §10.3
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0) :
    HasDerivAt (mLocationScore (huberPsi c) P) (-(P.real {x | |x - θ₀| < c})) θ₀ :=
  hasDerivAt_mLocationScore_huber_aux hc h_atom_add h_atom_sub

end StatLean.RobustStatistics
