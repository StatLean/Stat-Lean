import StatLean.HypothesisTesting.LikelihoodMethods.UniformLAN
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The likelihood trinity: Wald, score and likelihood ratio statistics

Three statistics test the same simple null `θ = θ₀` in an i.i.d. quadratic-mean
differentiable model with positive definite Fisher information `I(θ₀)`:

* the **Wald statistic** `Wₙ = n·(θ̂ₙ − θ₀)ᵀ I(θ₀) (θ̂ₙ − θ₀)`, built from an efficient
  estimator sequence;
* the **Rao score statistic** `Rₙ = Zₙᵀ I⁻¹(θ₀) Zₙ`, built from the normalized score and
  requiring no estimator at all;
* the **likelihood ratio statistic** `2 log Rₙ = 2[ℓₙ(θ̂ₙ) − ℓₙ(θ₀)]`.

They are asymptotically equivalent — pairwise differences vanish in probability — and each
converges in law to `χ²` with `k` degrees of freedom. For the composite null obtained by
restricting `θ` to an affine subspace of codimension `p`, the likelihood ratio statistic
formed from efficient estimators in the full and in the restricted model converges to `χ²`
with `p` degrees of freedom.

Beyond quadratic-mean differentiability, the likelihood ratio analysis needs the source's
additional second-order remainder condition
$$ \bigl|\log p_\theta(x) - \log p_{\theta_0}(x)
   - \langle\theta-\theta_0, \tilde\eta_{\theta_0}(x)\rangle\bigr| \le M(x)\|\theta-\theta_0\|^2,
   \qquad E_{\theta_0}[M(X)]<\infty, $$
for `θ` in a neighbourhood of `θ₀` — it is what makes the local expansion uniform over
bounded directions, and hence usable at the random direction `√n(θ̂ₙ − θ₀)`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.4 (Likelihood Methods in Parametric Models), Theorem 14.4.2
(§14.4.2–14.4.4, Wald Tests, Rao Score Tests and Likelihood Ratio Tests): the three statistics
are asymptotically equivalent and chi-squared. (`TSH4 §14.4 Thm 14.4.2`.)

**Proof formalization notes.**
* *Hypotheses are assigned per statistic, not globally.* The source states the whole theorem
  under one set of standing assumptions; here the envelope condition is imposed only on the
  likelihood-ratio statements, which are the ones that consume it (through
  `sup_LAN_remainder_tendsto`). The score and Wald limits follow from quadratic-mean
  differentiability, the score central limit theorem and the assumed expansion alone.
* The efficient estimator sequence is never constructed: it is data, constrained by
  `IsAsymptoticallyLinear`, exactly as in the source, where maximum likelihood estimators
  and one-step estimators are cited as examples but the expansion is what is assumed.
* The Wald statistic is normalized by `I(θ₀)` rather than by `I(θ̂ₙ)`. The source notes the
  two versions are interchangeable ("`I(θ̂ₙ)` may be replaced by `I(θ₀)` or any consistent
  estimator"); the fixed-matrix form avoids carrying a consistency hypothesis on a plug-in
  estimator of the information matrix.
* The composite null is presented as the affine subspace `a + range B` with `B` an injective
  linear map from a space of dimension `m`. This is exactly the solution set of
  `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p = k − m`, and it lets the restricted
  model be an honest `ParametricFamily` in the chart `β`, so that "efficient estimator
  assuming the null" is the *same* predicate `IsAsymptoticallyLinear` applied to the
  restricted model rather than a new, unverified formula for its influence function.
* The smooth-constraint version of the composite case (null `{θ | g(θ) = 0}` with a
  continuously differentiable `g : ℝᵏ → ℝᵖ` whose Jacobian has rank `p`) is not stated
  separately: at `θ₀` it is the affine statement in the chart supplied by the implicit
  function theorem, with the same `p` degrees of freedom, and stating it independently would
  duplicate that reduction rather than add content.

**Bibliographic comments.** The three statistics are due to A. Wald ("Tests of statistical
hypotheses concerning several parameters when the number of observations is large," *Trans.
Amer. Math. Soc.* **54** (1943), 426–482), C. R. Rao ("Large sample tests of statistical
hypotheses concerning several parameters with applications to problems of estimation,"
*Proc. Camb. Phil. Soc.* **44** (1948), 50–57) and S. S. Wilks ("The large-sample
distribution of the likelihood ratio for testing composite hypotheses," *Ann. Math.
Statist.* **9** (1938), 60–62). The modern proof, which replaces classical
third-derivative conditions by quadratic-mean differentiability and contiguity, is due to
L. Le Cam ("Locally asymptotically normal families of distributions," *Univ. California
Publ. Statist.* **3** (1960), 37–98; "On the assumptions used to prove asymptotic normality
of maximum likelihood estimates," *Ann. Math. Statist.* **41** (1970), 802–828).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal Matrix BoundedContinuousFunction

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-! ## The three statistics -/

/-- The **Wald statistic** `Wₙ = n·⟪θ̂ₙ − θ₀, I(θ₀)(θ̂ₙ − θ₀)⟫` for the simple null
`θ = θ₀`, with the information matrix evaluated at the null value.

Edge behaviour: at `n = 0` the statistic is `0`. -/
noncomputable def waldStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  (n : ℝ) * ⟪est n ω - θ₀, mulVecE J (est n ω - θ₀)⟫

/-- The **Rao score statistic** `Rₙ = ⟪Zₙ, I⁻¹(θ₀)Zₙ⟫`, a quadratic form in the normalized
score sum. It uses no estimator of the parameter.

Edge behaviour: at `n = 0` the empty score sum vanishes, so the statistic is `0`. -/
noncomputable def scoreStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  ⟪scoreSum ℓ n ω, mulVecE J⁻¹ (scoreSum ℓ n ω)⟫

/-- The **likelihood ratio statistic** `2 log(Lₙ(θ̂ₙ)/Lₙ(θ̂ₙ,₀))` for a pair of estimator
sequences: twice the difference of the log-likelihoods at the unrestricted and restricted
estimates. The simple null `θ = θ₀` is the case of the constant restricted sequence.

Edge behaviour: densities enter through their ratio, so points where both densities vanish
contribute `Real.log (0/0) = 0`; at `n = 0` the statistic is `0`. -/
noncomputable def logLRStatistic (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  2 * ∑ i, Real.log (M.density (est n ω) (ω i) / M.density (est₀ n ω) (ω i))

/-- The **affinely restricted model** `β ↦ P_{a + Bβ}`: the model reparametrized by a chart
of the affine null subspace `a + range B`. Densities, their measurability and their
nonnegativity are inherited pointwise from the full model. -/
noncomputable def restrictFamily {m : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin m)) where
  density := fun β x => M.density (a + B β) x
  density_meas := fun β => M.density_meas (a + B β)
  density_nonneg := fun β x => M.density_nonneg (a + B β) x

/-! ## Algebraic, measurability and tightness helpers -/

/-- The matrix action `mulVecE J` is the application of the continuous linear map
`Matrix.toEuclideanCLM J`; the two spellings are definitionally equal. -/
private lemma mulVecE_eq_toEuclideanCLM (J : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    mulVecE J v = Matrix.toEuclideanCLM (𝕜 := ℝ) J v := rfl

/-- Continuity of the quadratic form `z ↦ ⟪z, A·z⟫` on `EuclideanSpace ℝ (Fin k)`; the matrix
action `mulVecE A` is definitionally `AsymptoticStatistics.GaussianShift.matrixAction A`, so
its continuity is inherited. -/
private lemma continuous_gaussQuadratic (A : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE A z⟫) :=
  continuous_id.inner (GaussianShift.matrixAction_continuous A)

/-- Measurability of the normalized score sum. -/
private lemma measurable_scoreSum (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (n : ℕ) : Measurable (scoreSum ℓ n) := by
  unfold scoreSum
  exact (Finset.measurable_sum Finset.univ
    (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul (Real.sqrt n)⁻¹

/-- **Gaussian quadratic form is chi-squared.** For a positive-definite `k×k` matrix `J`
(`k > 0`), the pushforward of `N(0, J)` under the quadratic form `z ↦ ⟪z, J⁻¹ z⟫` is the
`χ²ₖ` distribution — the exact distributional identity `Zᵀ J⁻¹ Z ∼ χ²ₖ` for `Z ∼ N(0, J)`,
supplied by the whitening bridge of `ForMathlib/NoncentralChiSquared.lean`. -/
private lemma multivariateGaussian_map_quadratic_eq_chiSquared
    (hk : 0 < k) (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef) :
    (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (fun z => ⟪z, mulVecE J⁻¹ z⟫) = MultipleTesting.chiSquared k :=
  multivariateGaussian_map_inner_inv_eq_chiSquared hk hJ_pd

/-- The matrix action `mulVecE J` is `ℝ`-linear in its vector argument (scalar homogeneity). -/
private lemma mulVecE_smul (J : Matrix (Fin k) (Fin k) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin k)) : mulVecE J (c • v) = c • mulVecE J v := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) J (c • v) = c • Matrix.toEuclideanCLM (𝕜 := ℝ) J v
  rw [map_smul]

/-- `J·(J⁻¹ z) = z` for a nonsingular `J`: `Matrix.toEuclideanCLM` is a `⋆`-algebra map, so
it carries `J * J⁻¹ = 1` to the identity operator. -/
private lemma mulVecE_mulVecE_inv (J : Matrix (Fin k) (Fin k) ℝ) (hdet : IsUnit J.det)
    (z : EuclideanSpace ℝ (Fin k)) : mulVecE J (mulVecE J⁻¹ z) = z := by
  rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
    ← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv J hdet, map_one]
  rfl

omit [MeasurableSpace 𝓧] in
/-- The Wald statistic is the quadratic form `⟪·, J ·⟫` evaluated at the normalized deviation
`√n·(θ̂ₙ − θ₀)`: `Wₙ = ⟪√n(θ̂ₙ−θ₀), J √n(θ̂ₙ−θ₀)⟫`. The two `√n` factors collapse the `n` in
front of the definition. -/
private lemma waldStatistic_eq_quadratic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    waldStatistic J θ₀ est n ω
      = ⟪Real.sqrt n • (est n ω - θ₀), mulVecE J (Real.sqrt n • (est n ω - θ₀))⟫ := by
  unfold waldStatistic
  rw [mulVecE_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]

omit [MeasurableSpace 𝓧] in
/-- The Rao score statistic is the *same* quadratic form `⟪·, J ·⟫` evaluated at
`Vₙ = J⁻¹Zₙ`: `Rₙ = ⟪Zₙ, J⁻¹Zₙ⟫ = ⟪J⁻¹Zₙ, J J⁻¹Zₙ⟫`. This is what puts the Wald and the
score statistic on a common footing. -/
private lemma scoreStatistic_eq_quadratic (J : Matrix (Fin k) (Fin k) ℝ) (hdet : IsUnit J.det)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    scoreStatistic J ℓ n ω
      = ⟪mulVecE J⁻¹ (scoreSum ℓ n ω), mulVecE J (mulVecE J⁻¹ (scoreSum ℓ n ω))⟫ := by
  rw [mulVecE_mulVecE_inv J hdet, real_inner_comm]
  rfl

/-- Polarization of the difference of two values of the quadratic form `q(z) = ⟪z, J z⟫`:
`q(u) − q(v) = ⟪u−v, J u⟫ + ⟪v, J(u−v)⟫`, bilinear in the increment `u − v`. -/
private lemma inner_mulVecE_quadratic_sub (J : Matrix (Fin k) (Fin k) ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    ⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫
      = ⟪u - v, mulVecE J u⟫ + ⟪v, mulVecE J (u - v)⟫ := by
  have h : mulVecE J (u - v) = mulVecE J u - mulVecE J v := by
    rw [mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM, mulVecE_eq_toEuclideanCLM,
      map_sub]
  rw [h, inner_sub_left, inner_sub_right]
  ring

/-- The quantitative form of the previous lemma: the quadratic form is Lipschitz on bounded
sets, with the operator norm of `J` as constant. -/
private lemma abs_inner_mulVecE_quadratic_sub_le (J : Matrix (Fin k) (Fin k) ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    |⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫|
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
  set C := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hC
  have hop : ∀ w : EuclideanSpace ℝ (Fin k), ‖mulVecE J w‖ ≤ C * ‖w‖ := by
    intro w
    rw [mulVecE_eq_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ w
  have h1 : |⟪u - v, mulVecE J u⟫| ≤ ‖u - v‖ * (C * ‖u‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop u) (norm_nonneg _))
  have h2 : |⟪v, mulVecE J (u - v)⟫| ≤ ‖v‖ * (C * ‖u - v‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hop (u - v)) (norm_nonneg _))
  calc |⟪u, mulVecE J u⟫ - ⟪v, mulVecE J v⟫|
      = |⟪u - v, mulVecE J u⟫ + ⟪v, mulVecE J (u - v)⟫| := by
        rw [inner_mulVecE_quadratic_sub]
    _ ≤ |⟪u - v, mulVecE J u⟫| + |⟪v, mulVecE J (u - v)⟫| := abs_add_le _ _
    _ ≤ ‖u - v‖ * (C * ‖u‖) + ‖v‖ * (C * ‖u - v‖) := add_le_add h1 h2
    _ = C * ‖u - v‖ * (‖u‖ + ‖v‖) := by ring

/-- **Tightness from weak convergence.** If the laws of `V n` under probability measures
`P n` converge weakly to a probability measure `ν`, then for every `α > 0` there is a radius
`K` beyond which the `V n` sit with probability at most `α`, for all large `n`.

The proof avoids the portmanteau theorem: the explicit bounded continuous cut-off
`x ↦ max 0 (min 1 (‖x‖ − j))` is squeezed between the indicators of `{‖x‖ ≥ j+1}` and
`{‖x‖ ≥ j}`, and `j` is chosen so that `ν{‖x‖ ≥ j}` is small — possible because the sets
`{‖x‖ ≥ j}` decrease to `∅` and `ν` is finite. -/
private lemma exists_radius_eventually_measureReal_norm_le
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {V : ∀ n, Ω n → E} (hV : ∀ n, Measurable (V n))
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hVw : WeakConverges (fun n => (P n).map (V n)) ν)
    {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, (P n).real {ω | K ≤ ‖V n ω‖} ≤ α := by
  classical
  -- The complements of the balls decrease to the empty set, so `ν` of them tends to `0`.
  have hmeasset : ∀ j : ℕ, MeasurableSet {x : E | (j : ℝ) ≤ ‖x‖} := fun j =>
    measurableSet_le measurable_const measurable_norm
  have hanti : Antitone (fun j : ℕ => {x : E | (j : ℝ) ≤ ‖x‖}) := by
    intro i j hij x hx
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_le.2 hij
    exact this.trans hx
  have hinter : (⋂ j : ℕ, {x : E | (j : ℝ) ≤ ‖x‖}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_nat_gt ‖x‖
  have htend : Tendsto (fun j : ℕ => ν {x : E | (j : ℝ) ≤ ‖x‖}) atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop (μ := ν)
      (fun j : ℕ => (hmeasset j).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
    rwa [hinter, measure_empty] at h
  obtain ⟨j, hj⟩ :=
    (htend.eventually_lt_const (u := ENNReal.ofReal (α / 2)) (by simpa using hα)).exists
  have hjreal : ν.real {x : E | (j : ℝ) ≤ ‖x‖} ≤ α / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) hj.le
  -- The cut-off test function.
  set c : ℝ := (j : ℝ) with hc
  have hcont : Continuous fun x : E => max 0 (min 1 (‖x‖ - c)) :=
    continuous_const.max (continuous_const.min (continuous_norm.sub continuous_const))
  set g : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => max 0 (min 1 (‖x‖ - c))) hcont 1 (by
        intro x
        have h0 : (0 : ℝ) ≤ max 0 (min 1 (‖x‖ - c)) := le_max_left _ _
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact max_le zero_le_one (min_le_left _ _)) with hg
  have hgval : ∀ x : E, g x = max 0 (min 1 (‖x‖ - c)) := fun _ => rfl
  refine ⟨c + 1, by positivity, ?_⟩
  -- Step 1: the event is dominated by the test function.
  have hstep1 : ∀ n : ℕ, (P n).real {ω | c + 1 ≤ ‖V n ω‖} ≤ ∫ x, g x ∂((P n).map (V n)) := by
    intro n
    have hset : MeasurableSet {ω : Ω n | c + 1 ≤ ‖V n ω‖} :=
      measurableSet_le measurable_const (hV n).norm
    have hgint : Integrable (fun ω => g (V n ω)) (P n) :=
      (integrable_const ‖g‖).mono'
        ((g.continuous.measurable.comp (hV n)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => g.norm_coe_le_norm _)
    have hle : ∀ ω : Ω n,
        Set.indicator {ω : Ω n | c + 1 ≤ ‖V n ω‖} (1 : Ω n → ℝ) ω ≤ g (V n ω) := by
      intro ω
      by_cases hω : ω ∈ {ω : Ω n | c + 1 ≤ ‖V n ω‖}
      · have h1 : (1 : ℝ) ≤ ‖V n ω‖ - c := by
          have := hω; simp only [Set.mem_setOf_eq] at this; linarith
        rw [Set.indicator_of_mem hω, hgval, min_eq_left h1]
        simp
      · rw [Set.indicator_of_notMem hω, hgval]
        exact le_max_left _ _
    calc (P n).real {ω | c + 1 ≤ ‖V n ω‖}
        = ∫ ω, Set.indicator {ω : Ω n | c + 1 ≤ ‖V n ω‖} (1 : Ω n → ℝ) ω ∂(P n) := by
          rw [integral_indicator_one hset]
      _ ≤ ∫ ω, g (V n ω) ∂(P n) :=
          integral_mono ((integrable_const (1 : ℝ)).indicator hset) hgint hle
      _ = ∫ x, g x ∂((P n).map (V n)) := by
          rw [integral_map (hV n).aemeasurable g.continuous.aestronglyMeasurable]
  -- Step 2: the limit of the test-function integrals is small.
  have hlim : ∫ x, g x ∂ν ≤ α / 2 := by
    have hle : ∀ x : E, g x ≤ Set.indicator {x : E | (j : ℝ) ≤ ‖x‖} (1 : E → ℝ) x := by
      intro x
      by_cases hx : x ∈ {x : E | (j : ℝ) ≤ ‖x‖}
      · rw [Set.indicator_of_mem hx, hgval]
        exact max_le zero_le_one (min_le_left _ _)
      · have hx' : ‖x‖ - c < 0 := by
          simp only [Set.mem_setOf_eq, not_le] at hx; rw [hc]; linarith
        rw [Set.indicator_of_notMem hx, hgval]
        exact max_le le_rfl ((min_le_right _ _).trans hx'.le)
    have hgint : Integrable (fun x => g x) ν :=
      (integrable_const ‖g‖).mono' g.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm _)
    calc ∫ x, g x ∂ν
        ≤ ∫ x, Set.indicator {x : E | (j : ℝ) ≤ ‖x‖} (1 : E → ℝ) x ∂ν :=
          integral_mono hgint ((integrable_const (1 : ℝ)).indicator (hmeasset j)) hle
      _ = ν.real {x : E | (j : ℝ) ≤ ‖x‖} := integral_indicator_one (hmeasset j)
      _ ≤ α / 2 := hjreal
  filter_upwards [(hVw g).eventually_le_const (u := α) (by linarith)] with n hn
  exact (hstep1 n).trans hn

/-- **The efficient-influence vector `Vₙ = J⁻¹Zₙ` is asymptotically `N(0, J⁻¹)`.** The score
central limit theorem gives `Zₙ ⇝ N(0, J)`; applying the linear map `J⁻¹` and using
`J⁻¹ J (J⁻¹)ᴴ = J⁻¹` turns this into the stated limit. -/
private lemma scoreSum_mulVecE_inv_weakConverges
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  have hpush : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
      (GaussianShift.matrixAction J⁻¹)
      = ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ := by
    have hfun : GaussianShift.matrixAction J⁻¹
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ :
            EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) :=
      funext (GaussianShift.matrixAction_eq_toEuclideanCLM J⁻¹)
    rw [hfun, ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM J⁻¹ 0
      hJ_pd.posSemidef]
    have hHerm : J⁻¹ᴴ = J⁻¹ := hJ_pd.inv.isHermitian
    congr 1
    · simp
    · rw [hHerm, Matrix.nonsing_inv_mul J hdet, Matrix.one_mul]
  have hmap := hScore.map (GaussianShift.matrixAction_continuous J⁻¹)
    (GaussianShift.matrixAction_measurable J⁻¹)
  rw [hpush] at hmap
  have hseqV : (fun n => (productMeasure M μ θ₀ n).map
      (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
      = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (GaussianShift.matrixAction J⁻¹)) := by
    funext n
    rw [Measure.map_map (GaussianShift.matrixAction_measurable J⁻¹)
      (measurable_scoreSum ℓ hℓ n)]
    rfl
  rw [hseqV]; exact hmap

/-! ## Asymptotic equivalence and the chi-squared limits -/

/-- **Measurability of the likelihood-ratio statistic.** For measurable estimator sequences and
a jointly measurable density, the map `ω ↦ 2 ∑ᵢ log(p_{θ̂}(ωᵢ)/p_{θ̂₀}(ωᵢ))` is measurable.

The hypothesis `hjoint` is *not* redundant: the `ParametricFamily` structure records only
per-`θ` measurability (`density_meas : ∀ θ, Measurable (density θ)`), and that is genuinely
too weak here.  Take `𝓧 = ℝ` with `μ` Lebesgue measure, `S ⊆ [0,1]` nonmeasurable, and
`p_θ = 1_{[0,1]} + 1_{\{f θ\}}` where `f θ = θ` for `θ ∈ S` and `f θ = θ + 1` otherwise.  Each
`p_θ` is Borel measurable (it differs from `1_{[0,1]}` on one point) and every `p_θ`
integrates to `1`, so all the frozen hypotheses hold; but for `n = 1` and the measurable
estimator `est 1 ω = ω 0` the statistic equals `2 log 2 · 1_S(ω 0)` on `[0,1]`, which is not
measurable.  Joint measurability of `(θ, x) ↦ p_θ(x)` is therefore forced, and it is the
standard regularity assumption (Carathéodory measurability) under which the source works. -/
private lemma measurable_logLRStatistic
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (hjoint : Measurable (Function.uncurry M.density))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n)) (hest₀ : ∀ n, Measurable (est₀ n)) (n : ℕ) :
    Measurable (logLRStatistic M est est₀ n) := by
  unfold logLRStatistic
  refine Measurable.const_mul (Finset.univ.measurable_sum fun i _ => ?_) 2
  refine Measurable.log (Measurable.div ?_ ?_)
  · exact hjoint.comp ((hest n).prodMk (measurable_pi_apply i))
  · exact hjoint.comp ((hest₀ n).prodMk (measurable_pi_apply i))

/-- **Wald − score is `o_P(1)`.** Under `P^n_{θ₀}` the Wald and Rao score statistics differ by a
quantity tending to zero in probability.

Writing `Uₙ = √n(θ̂ₙ−θ₀)` and `Vₙ = J⁻¹Zₙ`, one has `Wₙ = ⟪Uₙ, J Uₙ⟫` and `Rₙ = ⟪Vₙ, J Vₙ⟫`
(`waldStatistic_eq_quadratic`, `scoreStatistic_eq_quadratic`), so `Wₙ − Rₙ` is the bilinear
remainder `⟪Uₙ−Vₙ, J Uₙ⟫ + ⟪Vₙ, J(Uₙ−Vₙ)⟫`, bounded by `‖J‖·‖Uₙ−Vₙ‖·(‖Uₙ‖+‖Vₙ‖)`.
`IsAsymptoticallyLinear` makes `‖Uₙ−Vₙ‖` small in probability, and the score CLT makes `Vₙ`
tight (`exists_radius_eventually_measureReal_norm_le`); the event `{ε ≤ |Wₙ − Rₙ|}` is
therefore contained in `{η ≤ ‖Uₙ−Vₙ‖} ∪ {K ≤ ‖Vₙ‖}` for a suitable `η`, and subadditivity
of the measure finishes.  No LAN expansion is used. -/
private lemma wald_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  intro ε hε
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  set C : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) J‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hV := scoreSum_mulVecE_inv_weakConverges M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro α hα
  obtain ⟨K, hK0, hKev⟩ :=
    exists_radius_eventually_measureReal_norm_le hVmeas hV (α := α / 4) (by positivity)
  -- The tolerance on `‖Uₙ − Vₙ‖` that makes the bilinear remainder smaller than `ε`.
  have hD : (0 : ℝ) < C * (1 + 2 * K) + 1 := by positivity
  set η : ℝ := min 1 (ε / (C * (1 + 2 * K) + 1)) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηlt : C * η * (η + 2 * K) < ε := by
    have h1 : η * (C * (1 + 2 * K) + 1) ≤ ε := by
      rw [← le_div_iff₀ hD]; exact min_le_right _ _
    have h2 : C * η * (η + 2 * K) ≤ C * η * (1 + 2 * K) := by
      have hCη : (0 : ℝ) ≤ C * η := mul_nonneg hC0 hη0.le
      nlinarith
    nlinarith
  -- The bad event splits into a "linearization failed" part and a "score is large" part.
  have hincl : ∀ n : ℕ,
      {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|}
        ⊆ {ω : Fin n → 𝓧 |
              η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
            ∪ {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖} := by
    intro n ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hkey : |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω| < ε := by
      rw [waldStatistic_eq_quadratic J θ₀ est n ω, scoreStatistic_eq_quadratic J hdet ℓ n ω]
      refine lt_of_le_of_lt
        (abs_inner_mulVecE_quadratic_sub_le J (Real.sqrt n • (est n ω - θ₀))
          (mulVecE J⁻¹ (scoreSum ℓ n ω))) ?_
      have hu : ‖Real.sqrt n • (est n ω - θ₀)‖ ≤ η + K := by
        have hsplit := norm_le_norm_add_norm_sub' (Real.sqrt n • (est n ω - θ₀))
          (mulVecE J⁻¹ (scoreSum ℓ n ω))
        linarith [h1.le, h2.le]
      refine lt_of_le_of_lt ?_ hηlt
      have hnn : (0 : ℝ) ≤ ‖Real.sqrt n • (est n ω - θ₀)
          - mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := norm_nonneg _
      have hVn : (0 : ℝ) ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := norm_nonneg _
      have hsum : ‖Real.sqrt n • (est n ω - θ₀)‖ + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖
          ≤ η + 2 * K := by linarith [h2.le]
      have hprod : C * ‖Real.sqrt n • (est n ω - θ₀)
          - mulVecE J⁻¹ (scoreSum ℓ n ω)‖ ≤ C * η :=
        mul_le_mul_of_nonneg_left h1.le hC0
      have hnonneg : (0 : ℝ) ≤ ‖Real.sqrt n • (est n ω - θ₀)‖
          + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖ := by positivity
      calc C * ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖
              * (‖Real.sqrt n • (est n ω - θ₀)‖ + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖)
          ≤ (C * η) * (‖Real.sqrt n • (est n ω - θ₀)‖
              + ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖) := by
            exact mul_le_mul_of_nonneg_right hprod hnonneg
        _ ≤ (C * η) * (η + 2 * K) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hη0.le)
    exact absurd hω (not_le.2 hkey)
  -- Subadditivity, then the two eventual bounds.
  have hmono : ∀ n : ℕ,
      (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|}
        ≤ (productMeasure M μ θ₀ n).real
              {ω : Fin n → 𝓧 |
                η ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}
            + (productMeasure M μ θ₀ n).real
              {ω : Fin n → 𝓧 | K ≤ ‖mulVecE J⁻¹ (scoreSum ℓ n ω)‖} := fun n =>
    (measureReal_mono (hincl n) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  filter_upwards [(hlin η hη0).eventually_lt_const (u := α / 4) (by positivity), hKev]
    with n h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have := hmono n
  linarith

/-- **logLR − score is `o_P(1)`** (simple null). Under `P^n_{θ₀}` and the second-order envelope
condition, the likelihood-ratio and Rao score statistics differ by a quantity tending to zero
in probability. -/
-- TODO: The uniform LAN expansion `sup_LAN_remainder_tendsto` (in `UniformLAN.lean`, itself an
-- open sorry) evaluated at the random direction `ĥₙ = √n(θ̂ₙ−θ₀)` gives
-- `2[ℓₙ(θ̂)−ℓₙ(θ₀)] = 2⟪ĥₙ, Zₙ⟫ − ⟪ĥₙ, J ĥₙ⟫ + o_P(1)`; substituting `ĥₙ = J⁻¹Zₙ + o_P(1)`
-- (`IsAsymptoticallyLinear`) collapses the leading terms to `⟪Zₙ, J⁻¹Zₙ⟫ = Rₙ`.  Blocked on the
-- upstream expansion plus tightness bookkeeping.  Sanctioned lifted sorry.
private lemma logLR_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  sorry

/-- **Asymptotic equivalence of the trinity.**

Under `P^n_{θ₀}`, the Wald and likelihood ratio statistics each differ from the Rao score
statistic by a quantity tending to zero in probability. Consequently the three tests reject
the same data sets with probability tending to one. -/
theorem trinity_asymptotically_equivalent
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) :=
  ⟨wald_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin,
    logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
      Menv hMenv_meas hMenv_int δ hδ henv⟩

/-- **The Rao score statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `Zₙᵀ I⁻¹(θ₀) Zₙ ⇝ χ²ₖ`. This part needs no estimator and no envelope
condition: the score central limit theorem plus the continuous mapping theorem suffice, the
quadratic form of a `N(0, I)` vector in the metric `I⁻¹` being `χ²ₖ`. -/
theorem score_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      (MultipleTesting.chiSquared k) := by
  -- Score CLT under the null: `Zₙ ⇝ N(0, J)`.
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  -- The quadratic form `q z = ⟪z, J⁻¹ z⟫` is continuous, and `scoreStatistic = q ∘ scoreSum`.
  have hcont := continuous_gaussQuadratic (k := k) J⁻¹
  have hmeas := hcont.measurable
  -- Rewrite the pushforward of the statistic as a composed pushforward of the score sum.
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (fun z => ⟪z, mulVecE J⁻¹ z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (measurable_scoreSum ℓ hℓ n)]
    rfl
  rw [hseq, ← multivariateGaussian_map_quadratic_eq_chiSquared hk J hJ_pd]
  exact hScore.map hcont hmeas

/-- **The Wald statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `n(θ̂ₙ − θ₀)ᵀ I(θ₀)(θ̂ₙ − θ₀) ⇝ χ²ₖ` for any efficient estimator
sequence. Follows from the assumed expansion and the score limit; no envelope condition is
needed. -/
theorem wald_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      (MultipleTesting.chiSquared k) := by
  -- `Vₙ = mulVecE J⁻¹ Zₙ ⇝ N(0, J⁻¹)`, by the score CLT and the linear pushforward.
  have hJinv_pd : J⁻¹.PosDef := hJ_pd.inv
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  have hV := scoreSum_mulVecE_inv_weakConverges M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ
  -- `Uₙ = √n·(θ̂ₙ − θ₀) ⇝ N(0, J⁻¹)` by Slutsky, since `‖Uₙ − Vₙ‖ →_P 0`.
  have hUmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => Real.sqrt n • (est n ω - θ₀)) :=
    fun n => ((hest n).sub measurable_const).const_smul (Real.sqrt n)
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hU : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => Real.sqrt n • (est n ω - θ₀)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
    refine WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := fun n ω => mulVecE J⁻¹ (scoreSum ℓ n ω))
      (Y := fun n ω => Real.sqrt n • (est n ω - θ₀))
      (fun n => (hVmeas n).aemeasurable) (fun n => (hUmeas n).aemeasurable) hV ?_
    intro ε hε
    have hset : (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ dist (mulVecE J⁻¹ (scoreSum ℓ n ω))
          (Real.sqrt n • (est n ω - θ₀))})
        = (fun n => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}) := by
      funext n; congr 1; ext ω
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm, norm_sub_rev]
    rw [hset]; exact hlin ε hε
  -- Continuous mapping: `Wₙ = ⟪Uₙ, J Uₙ⟫`, and `N(0, J⁻¹)` pushes to `χ²ₖ`.
  have hcont := continuous_gaussQuadratic (k := k) J
  have hmeas := hcont.measurable
  have hmapU := hU.map hcont hmeas
  have hlim : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹).map
      (fun z => ⟪z, mulVecE J z⟫) = MultipleTesting.chiSquared k := by
    have h := multivariateGaussian_map_quadratic_eq_chiSquared hk J⁻¹ hJinv_pd
    rwa [Matrix.nonsing_inv_nonsing_inv J hdet] at h
  rw [hlim] at hmapU
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      = (fun n => ((productMeasure M μ θ₀ n).map
          (fun ω => Real.sqrt n • (est n ω - θ₀))).map (fun z => ⟪z, mulVecE J z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (hUmeas n)]
    congr 1
    funext ω
    exact waldStatistic_eq_quadratic J θ₀ est n ω
  rw [hseq]; exact hmapU

/-- **The likelihood ratio statistic is asymptotically chi-squared (simple null).**

Under `P^n_{θ₀}` and the second-order envelope condition,
`2 log(Lₙ(θ̂ₙ)/Lₙ(θ₀)) ⇝ χ²ₖ` for any efficient estimator sequence. -/
theorem logLR_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: joint measurability of `(θ, x) ↦ p_θ(x)`; needed for the likelihood-ratio
    -- statistic to be a measurable function of the sample (see `measurable_logLRStatistic`,
    -- where the counterexample showing that per-`θ` measurability does not suffice is given)
    (hjoint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (logLRStatistic M est (fun _ _ => θ₀) n))
      (MultipleTesting.chiSquared k) := by
  -- Rao score statistic converges to `χ²ₖ`; the LR statistic differs from it by `o_P(1)`.
  haveI : NeZero k := ⟨hk.ne'⟩
  have hscore := score_tendsto_chiSquared M μ hPDF hk θ₀ ℓ hℓ hDQM J hJ_pd hJ
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n => scoreStatistic J ℓ n)
    (Y := fun n => logLRStatistic M est (fun _ _ => θ₀) n)
    (fun n => ((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).aemeasurable)
    (fun n => (measurable_logLRStatistic M hjoint est (fun _ _ => θ₀) hest
        (fun _ => measurable_const) n).aemeasurable)
    hscore ?_
  intro ε hε
  have h := logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
    Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω)
        (logLRStatistic M est (fun _ _ => θ₀) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

/-- **Score-difference surrogate converges to `χ²ₚ`** (affine composite null). The difference of
the full-model and restricted-model Rao score statistics converges in law to `χ²ₚ`, `p = k − m`
the codimension. -/
-- TODO: The classical fact `Zₙᵀ J⁻¹ Zₙ − (B*Zₙ)ᵀ JB⁻¹ (B*Zₙ) = ‖Π Zₙ‖²_{J⁻¹} ⇝ χ²ₚ`, where `Π`
-- is the rank-`p` `J`-orthogonal projection off `range B` (`B* = adjoint B`, and
-- `scoreSum ℓB = B* (scoreSum ℓ)` by linearity of `B*`).  Needs the restricted-model score CLT
-- together with a *degenerate* (rank-`p`) Gaussian-quadratic ↔ chi-squared bridge, which
-- generalises `multivariateGaussian_map_inner_inv_eq_chiSquared` (full-rank only) and is not yet
-- available.  Sanctioned lifted sorry.
private lemma affineScoreDiff_tendsto_chiSquared {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (hdim : m + p = k) (hp : 0 < p)
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)] :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω))
      (MultipleTesting.chiSquared p) := by
  sorry

/-- **logLR − score-difference is `o_P(1)`** (affine composite null). The affine likelihood-ratio
statistic differs from the score-difference surrogate by a quantity tending to zero in
probability. -/
-- TODO: Apply the uniform LAN expansion (`sup_LAN_remainder_tendsto`, open sorry upstream) in the
-- full model at `ĥₙ = √n(θ̂ₙ−θ₀)` and in the restricted model at `√n(β̂ₙ−β₀)`, then subtract; the
-- efficient-estimator substitutions (`hlin`, `hlin₀`) collapse each expansion to its score
-- quadratic, leaving `ZₙᵀJ⁻¹Zₙ − (B*Zₙ)ᵀJB⁻¹(B*Zₙ)`.  Blocked on the upstream expansion.
-- Sanctioned lifted sorry.
private lemma logLR_affine_sub_scoreDiff_tendstoInMeasure {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m)) (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|})
        atTop (𝓝 0) := by
  sorry

/-- **The likelihood ratio statistic is asymptotically chi-squared (affine composite null).**

Let the null hypothesis restrict `θ` to the affine subspace `a + range B` of codimension
`p = k − m` (equivalently, `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p`), let `θ̂ₙ` be
efficient in the full model and let `β̂ₙ` be efficient in the restricted model
`β ↦ P_{a + Bβ}`. Then, under `P^n_{θ₀}` for any `θ₀ = a + Bβ₀` in the null,
`2 log(Lₙ(θ̂ₙ)/Lₙ(a + Bβ̂ₙ)) ⇝ χ²ₚ`: the degrees of freedom count the restrictions, i.e. the
dimension of the full parameter space minus that of the null. -/
theorem logLR_tendsto_chiSquared_affine {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the full model; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: joint measurability of `(θ, x) ↦ p_θ(x)`; needed for the likelihood-ratio
    -- statistic to be a measurable function of the sample (see `measurable_logLRStatistic`)
    (hjoint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: the codimension is the difference of dimensions and is nondegenerate
    (hdim : m + p = k) (hp : 0 < p)
    -- USER-INPUT: a chart of the affine null subspace: base point and injective direction map
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    -- USER-INPUT: the null parameter, given in the chart
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- LEAN-ONLY: name for the score of the restricted model — the adjoint image of `ℓ`
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    -- LEAN-ONLY: matrix form of the restricted model's Fisher information at `β₀`
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the restricted model
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)]
    -- USER-INPUT: an efficient estimator sequence in the full model
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: an efficient estimator sequence in the restricted model, in the chart
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n))
      (MultipleTesting.chiSquared p) := by
  -- Score-difference surrogate converges to `χ²ₚ`; the affine LR differs from it by `o_P(1)`.
  haveI : NeZero p := ⟨hp.ne'⟩
  have hℓB' : Measurable ℓB := by
    rw [hℓB]; exact (ContinuousLinearMap.adjoint B).continuous.measurable.comp hℓ
  have hscorediff := affineScoreDiff_tendsto_chiSquared M μ hPDF hdim hp a B hB β₀ θ₀ hθ₀
    ℓ hℓ hDQM J hJ_pd hJ ℓB hℓB JB hJB
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
    (Y := fun n => logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n)
    (fun n => (((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).sub
        ((continuous_gaussQuadratic JB⁻¹).measurable.comp
          (measurable_scoreSum ℓB hℓB' n))).aemeasurable)
    (fun n => (measurable_logLRStatistic M hjoint est (fun n ω => a + B (est₀ n ω)) hest
        (fun n => (B.continuous.measurable.comp (hest₀ n)).const_add a) n).aemeasurable)
    hscorediff ?_
  intro ε hε
  have h := logLR_affine_sub_scoreDiff_tendstoInMeasure M μ hPDF θ₀ a B β₀ ℓ hℓ J ℓB JB
    est hest hlin est₀ hest₀ hlin₀ Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

end StatLean.HypothesisTesting

