import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
import StatLean.AsymptoticStatistics.ForMathlib.SlutskyVec
import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Efficient estimators under local alternatives

Let `X₁, …, Xₙ` be i.i.d. from a model that is differentiable in quadratic mean at `θ₀` with
nonsingular Fisher information `I(θ₀)`, and let `θ̂ₙ` be an **asymptotically linear**
(efficient) estimator sequence, i.e. one satisfying, under `P^n_{θ₀}`,
$$ \sqrt{n}\,(\hat\theta_n - \theta_0) \;=\; I^{-1}(\theta_0)\, Z_n + o_{P}(1), \qquad
   Z_n = \frac{1}{\sqrt n}\sum_{i\le n} \tilde\eta_{\theta_0}(X_i) $$
(`Z_n` the normalized score). The expansion is assumed **only at `θ₀`**; the point of this
file is that it nevertheless determines the limiting behaviour of `θ̂ₙ` along every local
alternative sequence `θₙ = θ₀ + hₙ/√n` (`hₙ → h`), because the local experiments are
mutually contiguous:

* `weak_limit_estimator_under_local_alternatives` — `√n(θ̂ₙ − θₙ) ⇝ N(0, I⁻¹(θ₀))` under
  `P^n_{θₙ}`;
* `weak_limit_estimator_centered_under_local_alternatives` — equivalently
  `√n(θ̂ₙ − θ₀) ⇝ N(h, I⁻¹(θ₀))` under `P^n_{θₙ}`;
* `weak_limit_g_estimator_under_local_alternatives` — the delta-method consequence
  `√n(g(θ̂ₙ) − g(θₙ)) ⇝ N(0, ġ(θ₀)I⁻¹(θ₀)ġ(θ₀)ᵀ)` for a differentiable real `g` with
  nonvanishing gradient.

This "weak robustness" of the limiting law under perturbations of size `n^{-1/2}` is what
makes such estimator sequences usable as the backbone of asymptotic testing theory.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.4 (Likelihood Methods in Parametric Models), Theorem 14.4.1
(§14.4.1, Efficient Likelihood Estimation): the limit law of an asymptotically linear
estimator under `θ₀ + h/√n`. (`TSH4 §14.4 Thm 14.4.1`.)

**Proof formalization notes.**
* Statements are built on the area conventions of the asymptotic-statistics development:
  the model is a `ParametricFamily` with a dominating measure and `IsPDFOf`, the i.i.d.
  law of the sample is `productMeasure M μ θ n` on `Fin n → 𝓧`, the score sum is
  `scoreSum ℓ n`, weak convergence is `WeakConverges`, and quadratic-mean
  differentiability is `DifferentiableQuadraticMean`. The parameter set is the whole of
  `EuclideanSpace ℝ (Fin k)`, which is open, so the source's "Ω an open subset of `ℝᵏ`"
  needs no separate hypothesis.
* `o_P(1)` along a triangular array cannot be `TendstoInMeasure` (each `n` lives on its own
  sample space), so it is spelled out as the measure of the exceptional event tending to
  zero — the same shape as the area's LAN-residual statement.
* The Fisher information enters as a matrix `J` tied to the bilinear form
  `fisherInformation` by `hJ`, matching the area's convention; `mulVecE` is that
  convention's `(WithLp.equiv 2 _).symm ∘ mulVec ∘ (WithLp.equiv 2 _)` sandwich, given a
  name so that the statements below stay readable (it unfolds definitionally, so the
  area's lemmas apply after `simp only [mulVecE]`).
* Nonsingularity of the information matrix is `IsUnit J.det`, matching the source's
  "nonsingular"; the stronger `Matrix.PosDef J` is used only where the source says
  "positive definite".
* The proof route is: contiguity of `P^n_{θₙ}` to `P^n_{θ₀}` (from quadratic-mean
  differentiability) plus Le Cam's third lemma, applied to the pair
  `(⟪I⁻¹(θ₀)Z_n, t⟫, log L_{n,h})`, followed by the Cramér–Wold device.

**Bibliographic comments.** Contiguity, local asymptotic normality and the third lemma are
due to L. Le Cam ("Locally asymptotically normal families of distributions," *Univ.
California Publ. Statist.* **3** (1960), 37–98), with quadratic-mean differentiability
introduced in L. Le Cam ("On the assumptions used to prove asymptotic normality of maximum
likelihood estimates," *Ann. Math. Statist.* **41** (1970), 802–828). The systematic use of
contiguity to transfer limit laws to local alternatives, and the notion of a regular
estimator sequence, are due to J. Hájek ("Asymptotically most powerful rank-order tests,"
*Ann. Math. Statist.* **33** (1962), 1124–1147).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal Matrix BoundedContinuousFunction MatrixOrder

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- The action of a `k × k` matrix on `EuclideanSpace ℝ (Fin k)`, transported through the
`WithLp` equivalence: `mulVecE J v = J·v`. This is the sandwich in which the Fisher
information matrix is tied to the Fisher information bilinear form throughout the
asymptotic development; it is given a name only for readability and unfolds
definitionally. -/
noncomputable def mulVecE (J : Matrix (Fin k) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))

/-- The **local alternative sequence** `θₙ = θ₀ + hₙ/√n`. At `n = 0` the scaling factor
`(√0)⁻¹ = 0`, so `localAlt θ₀ h_n 0 = θ₀`. -/
noncomputable def localAlt (θ₀ : EuclideanSpace ℝ (Fin k))
    (h_n : ℕ → EuclideanSpace ℝ (Fin k)) (n : ℕ) : EuclideanSpace ℝ (Fin k) :=
  θ₀ + (Real.sqrt n)⁻¹ • h_n n

/-- **Asymptotic linearity (efficiency) of an estimator sequence at `θ₀`.**

`√n(θ̂ₙ − θ₀) = I⁻¹(θ₀)·Zₙ + o_P(1)` under the i.i.d. law `P^n_{θ₀}`, where `Zₙ` is the
normalized score sum. The `o_P(1)` is spelled as: for every `ε > 0` the `P^n_{θ₀}`-measure
of the event that the remainder has norm at least `ε` tends to `0`.

Estimator sequences with this property are exactly those the asymptotic testing theory calls
efficient; maximum likelihood estimators and one-step estimators satisfy it under classical
smoothness conditions, but the property — not any particular construction — is what the
theorems consume.

Edge behaviour: `J⁻¹` is the `Matrix` inverse, which is the junk value `0` when `J` is
singular; the theorems consuming this predicate all assume `J` nonsingular, and with a
singular `J` the condition degenerates to `√n(θ̂ₙ − θ₀) →_P 0`. -/
def IsAsymptoticallyLinear (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 |
        ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖})
      atTop (𝓝 0)


/-! ## Helpers -/

open scoped MatrixOrder in
/-- **Translating a multivariate Gaussian shifts its mean.** Immediate from the definition
`multivariateGaussian m S = (stdGaussian).map (x ↦ m + √S x)`; no positive-semidefiniteness
is needed (the degenerate `CFC.sqrt S = 0` branch translates a Dirac mass). -/
private lemma multivariateGaussian_map_add_right
    (m v : EuclideanSpace ℝ (Fin k)) (S : Matrix (Fin k) (Fin k) ℝ) :
    (ProbabilityTheory.multivariateGaussian m S).map (fun y => y + v)
      = ProbabilityTheory.multivariateGaussian (m + v) S := by
  classical
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin k) =>
      m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).continuous.measurable.const_add m
  rw [ProbabilityTheory.multivariateGaussian, ProbabilityTheory.multivariateGaussian,
    Measure.map_map (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin k) => y + v)
      hmeas]
  congr 1
  funext x
  simp only [Function.comp_apply]
  abel

/-- Weak convergence only depends on the tail of the sequence of measures. -/
private lemma weakConverges_of_eventually_eq {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] {νn νn' : ℕ → Measure E} {ν : Measure E}
    (heq : ∀ᶠ n in atTop, νn n = νn' n) (hw : WeakConverges νn ν) : WeakConverges νn' ν := by
  intro f
  refine (hw f).congr' ?_
  filter_upwards [heq] with n hn
  rw [hn]

/-- `mulVecE J` is the action of `Matrix.toEuclideanCLM J`; definitionally equal. -/
lemma mulVecE_apply_clm (J : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    mulVecE J v = Matrix.toEuclideanCLM (𝕜 := ℝ) J v := rfl

/-- **The Fisher information matrix is positive semidefinite.** The bilinear form
`(u, v) ↦ ∫ ⟪u, ℓ⟫⟪v, ℓ⟫ p_{θ₀}` is symmetric with nonnegative diagonal, and `hJ` transports
those two facts to the matrix. This is used to feed the Gaussian pushforward lemmas, which
are vacuous for non-positive-semidefinite covariances; it makes the source's bare
nonsingularity hypothesis `IsUnit J.det` equivalent to positive definiteness, so no extra
hypothesis is needed. -/
lemma posSemidef_of_fisherInformation
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    J.PosSemidef := by
  classical
  have hsymm : ∀ u v : EuclideanSpace ℝ (Fin k),
      ⟪u, mulVecE J v⟫ = ⟪v, mulVecE J u⟫ := by
    intro u v
    rw [← hJ u v, ← hJ v u]
    unfold fisherInformation
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hnn : ∀ u : EuclideanSpace ℝ (Fin k), 0 ≤ ⟪u, mulVecE J u⟫ := by
    intro u
    rw [← hJ u u]
    unfold fisherInformation
    exact integral_nonneg fun x =>
      mul_nonneg (mul_self_nonneg _) (M.density_nonneg θ₀ x)
  -- Transport both facts to plain vectors through `Matrix.inner_toEuclideanCLM`.
  have hsymm' : ∀ x y : Fin k → ℝ,
      dotProduct x (J.mulVec y) = dotProduct y (J.mulVec x) := by
    intro x y
    have h := hsymm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simp only [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM] at h
    simpa using h
  have hnn' : ∀ x : Fin k → ℝ, (0 : ℝ) ≤ dotProduct x (J.mulVec x) := by
    intro x
    have h := hnn (WithLp.toLp 2 x)
    simp only [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM] at h
    simpa using h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    have h := hsymm' (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
    simpa [Matrix.conjTranspose_apply, Matrix.mulVec_single, single_dotProduct] using h
  · simpa using hnn' x

/-- **Tightness from weak convergence.** If the laws of `V n` under probability measures
`P n` converge weakly to a probability measure `ν`, then for every `α > 0` there is a radius
`K` beyond which the `V n` sit with probability at most `α`, for all large `n`.

The proof avoids the portmanteau theorem: the explicit bounded continuous cut-off
`x ↦ max 0 (min 1 (‖x‖ − j))` is squeezed between the indicators of `{‖x‖ ≥ j+1}` and
`{‖x‖ ≥ j}`, and `j` is chosen so that `ν{‖x‖ ≥ j}` is small — possible because the sets
`{‖x‖ ≥ j}` decrease to `∅` and `ν` is finite. -/
lemma exists_radius_eventually_measureReal_norm_le
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

/-- **Transfer of a weak limit across a vanishing integral discrepancy.**

If the laws of `f n` under two sequences of measures have asymptotically the same integrals
against every bounded continuous test function, then a weak limit for one is a weak limit for
the other.

This is the brick that reduces the *varying*-direction local-alternative limit to the
*fixed*-direction one: with `Q n = P^n_{θ₀ + hₙ/√n}` and `Q' n = P^n_{θ₀ + h/√n}` the
hypothesis `hclose` is implied by `‖Q n − Q' n‖_TV → 0`, which for a quadratic-mean
differentiable family follows from `n·H²(P_{θ₀+hₙ/√n}, P_{θ₀+h/√n}) → ⅛⟪h−hₙ, J(h−hₙ)⟫ → 0`.
See the discussion at `weak_limit_estimator_under_local_alternatives`. -/
private lemma weakConverges_of_integral_close
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Q Q' : ∀ n, Measure (Ω n)} {f : ∀ n, Ω n → E} {ν : Measure E}
    (hmeas : ∀ n, AEMeasurable (f n) (Q n))
    (hmeas' : ∀ n, AEMeasurable (f n) (Q' n))
    (hclose : ∀ g : E →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, g (f n ω) ∂(Q n) - ∫ ω, g (f n ω) ∂(Q' n)) atTop (𝓝 0))
    (hw : WeakConverges (fun n => (Q' n).map (f n)) ν) :
    WeakConverges (fun n => (Q n).map (f n)) ν := by
  intro g
  have h1 : ∀ n, ∫ x, g x ∂((Q n).map (f n)) = ∫ ω, g (f n ω) ∂(Q n) := fun n =>
    integral_map (hmeas n) g.continuous.aestronglyMeasurable
  have h2 : ∀ n, ∫ x, g x ∂((Q' n).map (f n)) = ∫ ω, g (f n ω) ∂(Q' n) := fun n =>
    integral_map (hmeas' n) g.continuous.aestronglyMeasurable
  have hB : Tendsto (fun n => ∫ ω, g (f n ω) ∂(Q' n)) atTop (𝓝 (∫ x, g x ∂ν)) := by
    refine (hw g).congr ?_
    intro n
    rw [h2 n]
  have hsum := (hclose g).add hB
  simp only [sub_add_cancel, zero_add] at hsum
  simpa only [h1] using hsum

/-! ### The exact change of measure, and the Le Cam-3 tilt of the limit law -/

/-- **Exact change of measure under a common-support hypothesis.**

`P^n_{θ₀+h/√n} = (P^n_{θ₀}).withDensity (exp ∘ Lₙ)` — the identity that
`contiguous_local_alternatives` consumes as `hL_is_log_ratio`.

**Why the hypothesis is needed.** Without it the identity is FALSE at the Lean junk values,
in *both* directions of the support comparison, and neither failure is a formalisation
artefact one can quotient away:

* where `p_{θ₀} x = 0 < p_{θ'} x`, the left side carries the mass `p_{θ'} x` while the right
  side carries none — `Real.log (a / 0) = 0`, so the ratio density is `1` there rather than
  `+∞`, and `1` multiplied into a vanishing base density is still `0`;
* where `p_{θ'} x = 0 < p_{θ₀} x`, the left side carries none while the right side carries
  `p_{θ₀} x · exp (Real.log 0) = p_{θ₀} x`.

So the minimal repair is the two-sided condition — the `HasCommonSupport` pattern of
`PointEstimation/InformationInequality/Basic.lean`, spelled out inline here to avoid an
import — and it is the same defect, with the same repair, as the one already carried by
`TrinityChiSquared.logLR_affine_sub_scoreDiff_tendstoInMeasure`. It is *not* a positivity
assumption on the model (`∀ θ x, 0 < p_θ x` would be false for many standard models); it says
only that no two parameters disagree about which points are impossible, which is what the
source assumes implicitly whenever it writes a likelihood ratio. -/
private lemma productMeasure_eq_withDensity_exp_logLikelihood
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hsupp : ∀ (θ θ' : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ x ≠ 0 → M.density θ' x ≠ 0)
    (h : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n
      = (productMeasure M μ θ₀ n).withDensity
          (fun ω => ENNReal.ofReal (Real.exp (logLikelihood M θ₀ h n ω))) := by
  refine logLikelihood_is_log_ratio M μ θ₀ h n (hPDF.density_integrable _)
    (Filter.Eventually.of_forall fun x => ?_)
  constructor
  · exact fun hx => lt_of_le_of_ne (M.density_nonneg _ _)
      (Ne.symm (hsupp θ₀ _ x (ne_of_gt hx)))
  · exact fun hx => lt_of_le_of_ne (M.density_nonneg _ _)
      (Ne.symm (hsupp _ θ₀ x (ne_of_gt hx)))

/-- **The Le Cam third-lemma tilt of the limiting joint law is `N(h, J⁻¹)`.**

The joint limit of `(√n(θ̂ₙ − θ₀), Δₙ)` under `P^n_{θ₀}` is the law of `(J⁻¹Δ, Δ)` with
`Δ ∼ N(0, J)` — a *degenerate* joint, carried by the graph of `J⁻¹`, because asymptotic
linearity makes the first coordinate a deterministic function of the second in the limit.
Le Cam's third lemma then tilts it by `e^{⟪h,Δ⟫ − ½⟪h,Jh⟫}` and reads off the first marginal.
This lemma computes that marginal in closed form.

The computation is three moves, each an existing `GaussianMGF` identity:
`Measure.withDensity_map_eq_map_withDensity` pulls the density back through the joint map, so
the tilt acts on `N(0, J)` itself; `multivariateGaussian_withDensity_exp_shift` turns the
exponential tilt of `N(0, J)` into the mean shift `N(Jh, J)`; and
`multivariateGaussian_map_toEuclideanCLM` pushes that forward along `J⁻¹`, giving mean
`J⁻¹(Jh) = h` and covariance `J⁻¹ J (J⁻¹)ᴴ = J⁻¹` (the transpose is harmless because a
positive semidefinite `J` is symmetric).

Deriving this as a lemma — rather than assuming the Gaussian-MGF pair as hypotheses — is what
lets `limit_law_under_h`'s companions `h_exp_int_πtilt` / `h_exp_int_πtilt_eq_one` be
discharged from `GaussianMGF.integrable_exp_tilt` / `integral_exp_tilt_eq_one`, whose only
input is that the second marginal of the joint is `N(0, J)`. -/
private lemma map_fst_withDensity_exp_tilt_graphJoint
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_psd : J.PosSemidef) (hJ_inv : IsUnit J.det)
    (h : EuclideanSpace ℝ (Fin k)) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
          (fun δ : EuclideanSpace ℝ (Fin k) =>
            (mulVecE J⁻¹ δ, ⟪h, δ⟫ - (1 / 2 : ℝ) * ⟪h, mulVecE J h⟫))).withDensity
        (fun q : EuclideanSpace ℝ (Fin k) × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst
      = multivariateGaussian h J⁻¹ := by
  classical
  have hJsymm : Jᵀ = J := by
    have := hJ_psd.1
    simpa [Matrix.conjTranspose, Matrix.transpose] using this
  have hquad : ⟪h, mulVecE J h⟫ = h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    simp [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM]
  set c : ℝ := (1 / 2 : ℝ) * ⟪h, mulVecE J h⟫ with hc
  set H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) × ℝ :=
    fun δ => (mulVecE J⁻¹ δ, ⟪h, δ⟫ - c) with hH
  have hH_meas : Measurable H := by
    refine Measurable.prodMk ?_ ?_
    · exact (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹).continuous.measurable
    · exact ((continuous_const.inner continuous_id).measurable).sub measurable_const
  have hw_meas : Measurable
      (fun q : EuclideanSpace ℝ (Fin k) × ℝ => ENNReal.ofReal (Real.exp q.2)) :=
    (Real.measurable_exp.comp measurable_snd).ennreal_ofReal
  -- Pull the density back through `H`, then compose `Prod.fst ∘ H = mulVecE J⁻¹`.
  rw [Measure.withDensity_map_eq_map_withDensity _ _ hH_meas _ hw_meas,
    Measure.map_map measurable_fst hH_meas]
  -- The tilt now acts on `N(0, J)` itself, with the exponent in `GaussianMGF` normal form.
  have hdens :
      ((fun q : EuclideanSpace ℝ (Fin k) × ℝ => ENNReal.ofReal (Real.exp q.2)) ∘ H)
        = fun y : EuclideanSpace ℝ (Fin k) =>
          ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2)) := by
    funext y
    simp only [hH, Function.comp_apply, hc, hquad]
    congr 2
    ring
  have hfst : (Prod.fst ∘ H) = fun δ : EuclideanSpace ℝ (Fin k) =>
      (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹) δ := by
    funext δ
    simp only [hH, Function.comp_apply]
    rfl
  rw [hdens, hfst, multivariateGaussian_withDensity_exp_shift hJ_psd h,
    multivariateGaussian_map_toEuclideanCLM J⁻¹ _ hJ_psd]
  -- Mean `J⁻¹(Jh) = h` and covariance `J⁻¹ J (J⁻¹)ᴴ = J⁻¹`.
  have hinvmul : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJ_inv
  have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹)
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h) = h := by
    have : (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹) * (Matrix.toEuclideanCLM (𝕜 := ℝ) J)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (J⁻¹ * J) := (map_mul _ _ _).symm
    have happ := congrArg (fun A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) =>
      A h) this
    simpa [hinvmul] using happ
  have hcov : J⁻¹ * J * (J⁻¹)ᴴ = J⁻¹ := by
    have hH' : (J⁻¹)ᴴ = J⁻¹ := by
      have : (J⁻¹)ᵀ = (Jᵀ)⁻¹ := Matrix.transpose_nonsing_inv J
      simpa [Matrix.conjTranspose, Matrix.transpose, hJsymm] using
        congrArg id (this.trans (by rw [hJsymm]))
    rw [hinvmul, one_mul, hH']
  rw [hmean, hcov]

/-- **Limit law of an efficient estimator under local alternatives.**

Under `P^n_{θₙ}` with `θₙ = θ₀ + hₙ/√n` and `hₙ → h`, the recentred estimator
`√n(θ̂ₙ − θₙ)` converges weakly to `N(0, I⁻¹(θ₀))` — the same law as under `θ₀`. -/
theorem weak_limit_estimator_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the estimators; needed to push measures forward
    (hest : ∀ n, Measurable (est n))
    -- USER-INPUT: the estimator sequence is asymptotically linear at `θ₀`
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n)))
      (multivariateGaussian 0 J⁻¹) := by
  -- TODO (obstruction RE-DERIVED this session; the previous note is confirmed on its three
  -- factual claims and superseded on the shape of the route and on the size of the gap).
  --
  -- The mathematical route is standard and the algebra is already in place downstream (the
  -- two companion theorems below and `ScoreUnderAlternatives` are *proved from this one*):
  --   (i)  `√n(θ̂ₙ−θ₀) = Vₙ + o_P(1)` under `P^n_{θ₀}` (`hlin`, with `Vₙ = J⁻¹Zₙ`);
  --   (ii) contiguity `P^n_{θₙ} ◅ P^n_{θ₀}` transfers that `o_P(1)` to `P^n_{θₙ}`;
  --   (iii) Le Cam's third lemma gives `Vₙ ⇝ N(h, J⁻¹)` under `P^n_{θₙ}`;
  --   (iv) `√n(θ̂ₙ−θₙ) = Vₙ − hₙ + o_P(1) ⇝ N(h,J⁻¹)` shifted by `−h`, i.e. `N(0, J⁻¹)`.
  --
  -- RE-VERIFIED (the three claims of the previous note all still hold, checked against the
  -- current `AsymptoticRepresentation.lean`):
  --   * `lanResidual_tendsto_productMeasure` does call `LAN_expansion_iii`, but with the
  --     CONSTANT sequence `h_n = h` (`tendsto_const_nhds`); the varying-`h_n` capability of
  --     `LAN_expansion_iii` is never transported to `productMeasure`, and the bridge it uses
  --     (the restriction map `(ℕ → 𝓧) → (Fin n → 𝓧)`) is built only for the constant case.
  --   * `productMeasure_integral_comparison` produces its slack `ρ n` from the `h`-dependent
  --     `goodSet M θ₀ h n` / `expLogFactor M θ₀ h n`, so uniformity over a compact set of
  --     directions is a genuine new argument, not a re-parenthesization.
  --   * `contiguous_local_alternatives` consumes the exact change-of-measure identity
  --     `hL_is_log_ratio`, which is not among this theorem's hypotheses.
  --
  -- NEW, AND WORSE THAN THE PREVIOUS NOTE SAID: the FIXED-direction case is blocked too, and
  -- the third bullet is not a bookkeeping omission. `hL_is_log_ratio` asks for
  --   `P^n_{θ₀+h/√n} = (P^n_{θ₀}).withDensity (exp ∘ logLikelihood M θ₀ h n)`,
  -- and that identity is FALSE at the Lean junk values whenever `p_{θ₀}` vanishes somewhere
  -- `p_{θ₀+h/√n}` does not: on `{p_{θ₀} = 0}` the left side carries mass while the right side
  -- carries none (`log (a/0) = 0`, so the density is `1` there rather than `+∞`). It is
  -- therefore *underivable* from `hPDF`/`hDQM`; it needs a common-support hypothesis. That is
  -- the same defect, with the same minimal repair, as the one now carried by
  -- `TrinityChiSquared.logLR_affine_sub_scoreDiff_tendstoInMeasure`
  -- (`hsupp : ∀ θ x, M.density θ₀ x ≠ 0 → M.density θ x ≠ 0`); the `goodSet` device of
  -- `productMeasure_integral_comparison` is the alternative, and is exactly why that theorem
  -- exists.
  --
  -- ROUTE, RESTRUCTURED. The varying direction need not be handled by making `ρ` uniform over
  -- a compact set of directions. `weakConverges_of_integral_close` above reduces the varying
  -- case to the fixed one: it suffices that the two local-alternative product laws
  -- `P^n_{θ₀+hₙ/√n}` and `P^n_{θ₀+h/√n}` become indistinguishable by bounded continuous test
  -- functions, which for a DQM family is the standard Hellinger estimate
  -- `n·H²(P_{θ₀+hₙ/√n}, P_{θ₀+h/√n}) → ⅛⟪h−hₙ, J(h−hₙ)⟫ → 0` plus `TV ≤ √2·H`. So the
  -- missing bricks are now: (A) the fixed-direction statement, i.e. the composite of
  -- `contiguous_local_alternatives` + Le Cam 3 under a common-support amendment (or via
  -- `productMeasure_integral_comparison`); and (B) the `n`-fold Hellinger bound above.
  --
  -- RE-VERIFIED AGAIN (wave 5), with one new finding that makes (A) *larger*, not smaller:
  --   * `contiguous_local_alternatives` still carries `hL_is_log_ratio` verbatim (it is passed
  --     straight to `Contiguity.mutuallyContiguous_of_asymptotically_log_normal`), so the
  --     common-support defect recorded above is unchanged.
  --   * The file's Le Cam third-lemma vehicle is `limit_law_under_h`. It does NOT produce a
  --     weak limit under the local alternative: the convergence
  --     `(P^n_{θ₀+h/√n}).map (T n) ⇝ L_h` is one of its *hypotheses* (`h_weak_under_h`), and
  --     its conclusion only *identifies* `L_h` as the tilted law
  --     `(fst)_*(π·e^{⟪h,δ⟫−½⟪h,Jh⟫})`. Existence of the limit is a separate step — the
  --     subsequence/tightness argument `joint_weak_subsequence` — and it is not packaged for
  --     the full sequence. So (A) is not "compose two existing theorems": it is
  --     existence-plus-identification, and the identification itself additionally consumes a
  --     Gaussian-MGF pair (`h_exp_int_πtilt`, `h_exp_int_πtilt_eq_one`) about the limiting
  --     joint law which is not among this theorem's hypotheses either.
  -- SCOPE. Both (A) and (B) live in
  -- `AsymptoticStatistics/LocalAsymptoticNormality/AsymptoticRepresentation.lean`, which this
  -- wave is not permitted to touch; nothing in this file can close them. The one brick this
  -- file can own is the varying-to-fixed reduction, and that is `weakConverges_of_integral_close`
  -- above — proved, and waiting only for (B).
  -- Sanctioned lifted sorry: no false statement, and every other theorem in this lane
  -- (`weak_limit_estimator_centered_under_local_alternatives`,
  -- `weak_limit_g_estimator_under_local_alternatives`, and
  -- `ScoreUnderAlternatives.weak_limit_scoreSum_under_local_alternatives`) is proved *from* it.
  sorry

/-- **Limit law of an efficient estimator under local alternatives, centred at `θ₀`.**

The equivalent form of the previous theorem: under `P^n_{θₙ}`, `√n(θ̂ₙ − θ₀)` converges
weakly to `N(h, I⁻¹(θ₀))`; the local shift `h` appears as the mean. -/
theorem weak_limit_estimator_centered_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the estimators
    (hest : ∀ n, Measurable (est n))
    -- USER-INPUT: the estimator sequence is asymptotically linear at `θ₀`
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - θ₀)))
      (multivariateGaussian h J⁻¹) := by
  -- The recentred limit.
  have h1 := weak_limit_estimator_under_local_alternatives M μ hPDF θ₀ ℓ hℓ hDQM J hJ hJ_inv
    est hest hlin h h_n hconv
  -- `Xₙ = √n(θ̂ₙ − θₙ) + (hₙ − h)` has the same limit `N(0, I⁻¹)` (deterministic shift → 0).
  have hXmeas : ∀ n : ℕ, Measurable
      (fun ω : Fin n → 𝓧 =>
        Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + (h_n n - h)) :=
    fun n => (((hest n).sub measurable_const).const_smul (Real.sqrt n)).add_const _
  have hcn : Tendsto (fun n : ℕ => h - h_n n) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := h) (f := atTop (α := ℕ))).sub hconv
    simpa using this
  have hX : WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + (h_n n - h)))
      (multivariateGaussian 0 J⁻¹) := by
    refine AsymptoticStatistics.ForMathlib.vec_slutsky_recentering (cn := fun n => h - h_n n)
      (fun n => (hXmeas n).aemeasurable) ?_ hcn
    have hfun : (fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + (h_n n - h) + (h - h_n n)))
        = fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
          (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n)) := by
      funext n
      congr 1
      funext ω
      abel
    rw [hfun]
    exact h1
  -- Translate by `h`.
  have hmap := hX.map (f := fun y : EuclideanSpace ℝ (Fin k) => y + h)
    (by fun_prop) (by fun_prop)
  rw [multivariateGaussian_map_add_right 0 h J⁻¹, zero_add] at hmap
  have hcomp : (fun n : ℕ => ((productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + (h_n n - h))).map
        (fun y : EuclideanSpace ℝ (Fin k) => y + h))
      = fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + (h_n n - h) + h) := by
    funext n
    rw [Measure.map_map (by fun_prop) (hXmeas n)]
    rfl
  rw [hcomp] at hmap
  -- For `n ≥ 1` the composite is exactly `√n(θ̂ₙ − θ₀)`.
  refine weakConverges_of_eventually_eq ?_ hmap
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 1
  funext ω
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs : Real.sqrt n • ((Real.sqrt n)⁻¹ • h_n n) = h_n n := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hsq), one_smul]
  simp only [localAlt]
  rw [show est n ω - (θ₀ + (Real.sqrt n)⁻¹ • h_n n)
      = (est n ω - θ₀) - (Real.sqrt n)⁻¹ • h_n n from by abel, smul_sub, hs]
  abel

/-- **Delta-method form under local alternatives.**

For a differentiable real-valued `g` with nonvanishing gradient `ġ`, the plug-in estimator
satisfies, under `P^n_{θₙ}`,
`√n(g(θ̂ₙ) − g(θₙ)) ⇝ N(0, σ²)` with `σ² = ġ(θ₀)·I⁻¹(θ₀)·ġ(θ₀)ᵀ`. -/
theorem weak_limit_g_estimator_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence, measurable and asymptotically linear at `θ₀`
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h))
    -- USER-INPUT: a differentiable real-valued parameter functional with gradient `gr`
    (g : EuclideanSpace ℝ (Fin k) → ℝ)
    (gr : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (hg : ∀ θ, HasGradientAt g (gr θ) θ)
    -- USER-INPUT: the gradient does not vanish at `θ₀`
    (hgr_ne : gr θ₀ ≠ 0)
    -- USER-INPUT: the asymptotic variance `σ² = ġ(θ₀)I⁻¹(θ₀)ġ(θ₀)ᵀ`
    (σ : NNReal) (hσ : (σ : ℝ) = ⟪gr θ₀, mulVecE J⁻¹ (gr θ₀)⟫) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n))))
      (gaussianReal 0 σ) := by
  classical
  have hJ_psd : J.PosSemidef := posSemidef_of_fisherInformation M μ θ₀ ℓ J hJ
  have hJ_pd : J.PosDef :=
    hJ_psd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det J).mpr hJ_inv)
  have hJinv_psd : J⁻¹.PosSemidef := hJ_pd.inv.posSemidef
  have hgc : Continuous g :=
    continuous_iff_continuousAt.2 fun θ => (hg θ).hasFDerivAt.differentiableAt.continuousAt
  -- The recentred estimator limit.
  have h1 := weak_limit_estimator_under_local_alternatives M μ hPDF θ₀ ℓ hℓ hDQM J hJ hJ_inv
    est hest hlin h h_n hconv
  have hWmeas : ∀ n : ℕ,
      Measurable (fun ω : Fin n → 𝓧 => Real.sqrt n • (est n ω - localAlt θ₀ h_n n)) :=
    fun n => ((hest n).sub measurable_const).const_smul (Real.sqrt n)
  -- Step 1: the linear functional of the recentred estimator is asymptotically `N(0, σ²)`.
  have hLmeas : Measurable fun z : EuclideanSpace ℝ (Fin k) => ⟪gr θ₀, z⟫ :=
    (continuous_const.inner continuous_id).measurable
  have hlinmap := h1.map (f := fun z : EuclideanSpace ℝ (Fin k) => ⟪gr θ₀, z⟫)
    (continuous_const.inner continuous_id) hLmeas
  rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal
    (gr θ₀) hJinv_psd] at hlinmap
  have hσeq : (dotProduct (gr θ₀).ofLp (J⁻¹.mulVec (gr θ₀).ofLp)).toNNReal = σ := by
    have hd : dotProduct (gr θ₀).ofLp (J⁻¹.mulVec (gr θ₀).ofLp)
        = ⟪gr θ₀, mulVecE J⁻¹ (gr θ₀)⟫ := by
      rw [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM]
    rw [hd, ← hσ, Real.toNNReal_coe]
  rw [hσeq] at hlinmap
  have hXcomp : (fun n : ℕ => ((productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n))).map
        (fun z : EuclideanSpace ℝ (Fin k) => ⟪gr θ₀, z⟫))
      = fun n : ℕ => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => ⟪gr θ₀, Real.sqrt n • (est n ω - localAlt θ₀ h_n n)⟫) := by
    funext n
    rw [Measure.map_map hLmeas (hWmeas n)]
    rfl
  rw [hXcomp] at hlinmap
  -- Step 2: Slutsky — the delta-method remainder is `o_P(1)`.
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => ⟪gr θ₀, Real.sqrt n • (est n ω - localAlt θ₀ h_n n)⟫)
    (Y := fun n ω => Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n)))
    (fun n => (hLmeas.comp (hWmeas n)).aemeasurable)
    (fun n => ((((hgc.measurable).comp (hest n)).sub measurable_const).const_mul
      (Real.sqrt n)).aemeasurable)
    hlinmap ?_
  -- The delta-method remainder.
  intro ε hε
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro α hα
  -- Tightness of `√n(θ̂ₙ − θₙ)`.
  obtain ⟨K, hK0, hKev⟩ :=
    exists_radius_eventually_measureReal_norm_le hWmeas h1 (α := α / 2) (by positivity)
  set H : ℝ := ‖h‖ + 1 with hHdef
  have hH0 : 0 < H := by positivity
  have hHev : ∀ᶠ n : ℕ in atTop, ‖h_n n‖ ≤ H := by
    have hnorm : Tendsto (fun n : ℕ => ‖h_n n‖) atTop (𝓝 ‖h‖) := hconv.norm
    have hmem := hnorm (Iio_mem_nhds (show ‖h‖ < H by rw [hHdef]; linarith))
    filter_upwards [hmem] with n hn using le_of_lt hn
  -- The little-o constant of the first-order expansion at `θ₀`.
  set c : ℝ := ε / (4 * (K + H + 1)) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hcKH : c * (K + H) < ε / 4 := by
    rw [hcdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  -- First-order expansion of `g` at `θ₀`, with remainder `Rf`.
  set Rf : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun θ => g θ - g θ₀ - ⟪gr θ₀, θ - θ₀⟫ with hRfdef
  have hlo := (hg θ₀).hasFDerivAt.isLittleO
  have hdef := hlo.def hc0
  rw [Metric.eventually_nhds_iff] at hdef
  obtain ⟨ρ0, hρ00, hρ⟩ := hdef
  set ρ : ℝ := ρ0 / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hRf : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ ρ → |Rf θ| ≤ c * ‖θ - θ₀‖ := by
    intro θ hθ
    have hd : dist θ θ₀ < ρ0 := by
      rw [dist_eq_norm]
      rw [hρdef] at hθ
      linarith
    have := hρ hd
    simpa [hRfdef, Real.norm_eq_abs, InnerProductSpace.toDual_apply] using this
  -- Eventually the whole picture sits inside the ball of radius `ρ`.
  have hsqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * (K + H)) atTop (𝓝 0) := by
    have h1' : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2' : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1'
    simpa using h2'.mul_const (K + H)
  have hρev : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ * (K + H) ≤ ρ := by
    filter_upwards [hsqrt (Iio_mem_nhds hρ0)] with n hn using le_of_lt hn
  filter_upwards [hKev, hHev, hρev, eventually_ge_atTop 1] with n hnK hnH hnρ hn1
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsqinv : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := le_of_lt (inv_pos.2 hsq)
  have hincl : {ω : Fin n → 𝓧 |
        ε ≤ dist (⟪gr θ₀, Real.sqrt n • (est n ω - localAlt θ₀ h_n n)⟫)
          (Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n)))}
      ⊆ {ω : Fin n → 𝓧 | K ≤ ‖Real.sqrt n • (est n ω - localAlt θ₀ h_n n)‖} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_le] at hcon
    -- Both `θ̂ₙ` and `θₙ` are within `ρ` of `θ₀`.
    have hU : ‖Real.sqrt n • (est n ω - θ₀)‖ ≤ K + H := by
      have hsplit : Real.sqrt n • (est n ω - θ₀)
          = Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + h_n n := by
        have hs : Real.sqrt n • ((Real.sqrt n)⁻¹ • h_n n) = h_n n := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hsq), one_smul]
        have haux : Real.sqrt n • (est n ω - localAlt θ₀ h_n n) + h_n n
            = Real.sqrt n • (est n ω - θ₀) := by
          simp only [localAlt]
          rw [show est n ω - (θ₀ + (Real.sqrt n)⁻¹ • h_n n)
              = (est n ω - θ₀) - (Real.sqrt n)⁻¹ • h_n n from by abel, smul_sub, hs]
          abel
        exact haux.symm
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (by linarith)
    have hnormsmul : ∀ u : EuclideanSpace ℝ (Fin k),
        ‖Real.sqrt n • u‖ = Real.sqrt n * ‖u‖ := by
      intro u
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq.le]
    have hestρ : ‖est n ω - θ₀‖ ≤ ρ := by
      have h' : Real.sqrt n * ‖est n ω - θ₀‖ ≤ K + H := by
        rw [← hnormsmul]; exact hU
      have := mul_le_mul_of_nonneg_left h' hsqinv
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsq), one_mul] at this
      exact le_trans this hnρ
    have hθnρ : ‖localAlt θ₀ h_n n - θ₀‖ ≤ ρ := by
      simp only [localAlt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hsqinv]
      have : (Real.sqrt n)⁻¹ * ‖h_n n‖ ≤ (Real.sqrt n)⁻¹ * (K + H) :=
        mul_le_mul_of_nonneg_left (by linarith) hsqinv
      linarith [hnρ]
    -- The remainder identity.
    have hXY : ⟪gr θ₀, Real.sqrt n • (est n ω - localAlt θ₀ h_n n)⟫
        - Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n))
        = Real.sqrt n * Rf (localAlt θ₀ h_n n) - Real.sqrt n * Rf (est n ω) := by
      have hsplit : ⟪gr θ₀, est n ω - localAlt θ₀ h_n n⟫
          = ⟪gr θ₀, est n ω - θ₀⟫ - ⟪gr θ₀, localAlt θ₀ h_n n - θ₀⟫ := by
        rw [← inner_sub_right]
        congr 1
        abel
      rw [real_inner_smul_right, hsplit, hRfdef]
      ring
    -- Both remainder terms are smaller than `ε/4`.
    have hb1 : Real.sqrt n * |Rf (est n ω)| < ε / 4 := by
      have := hRf _ hestρ
      have h2 : Real.sqrt n * |Rf (est n ω)| ≤ Real.sqrt n * (c * ‖est n ω - θ₀‖) :=
        mul_le_mul_of_nonneg_left this hsq.le
      have h3 : Real.sqrt n * (c * ‖est n ω - θ₀‖) = c * (Real.sqrt n * ‖est n ω - θ₀‖) := by
        ring
      have h4 : c * (Real.sqrt n * ‖est n ω - θ₀‖) ≤ c * (K + H) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0.le
        rw [← hnormsmul]; exact hU
      linarith
    have hb2 : Real.sqrt n * |Rf (localAlt θ₀ h_n n)| < ε / 4 := by
      have hbase := hRf _ hθnρ
      have hn' : ‖localAlt θ₀ h_n n - θ₀‖ = (Real.sqrt n)⁻¹ * ‖h_n n‖ := by
        simp only [localAlt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hsqinv]
      have h2 : Real.sqrt n * |Rf (localAlt θ₀ h_n n)|
          ≤ Real.sqrt n * (c * ((Real.sqrt n)⁻¹ * ‖h_n n‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hsq.le
        rw [← hn']; exact hbase
      have h3 : Real.sqrt n * (c * ((Real.sqrt n)⁻¹ * ‖h_n n‖)) = c * ‖h_n n‖ := by
        field_simp
      have h4 : c * ‖h_n n‖ ≤ c * (K + H) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0.le
      linarith
    have hfinal : dist (⟪gr θ₀, Real.sqrt n • (est n ω - localAlt θ₀ h_n n)⟫)
        (Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n))) < ε := by
      rw [Real.dist_eq, hXY]
      have := abs_sub (Real.sqrt n * Rf (localAlt θ₀ h_n n)) (Real.sqrt n * Rf (est n ω))
      rw [abs_mul, abs_mul, abs_of_nonneg hsq.le] at this
      linarith
    exact absurd hω (not_le.2 hfinal)
  have hmono := measureReal_mono (μ := productMeasure M μ (localAlt θ₀ h_n n) n) hincl
    (measure_ne_top _ _)
  linarith

end StatLean.HypothesisTesting
