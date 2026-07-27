import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The asymptotic maximin transfer for multisided local alternatives

The two maximin theorems of this directory — for Pearson's chi-squared test and for the
smooth test — are instances of one and the same statement about an asymptotically normal
sequence of experiments. This file isolates that statement, in the "lite" form the two
consumers actually need, together with the one geometric ingredient its proof rests on.

Setting: a triangular array of local experiments `Q_{n,h}` indexed by a local parameter
`h ∈ ℝ^k` (in the applications, `Q_{n,h}` is the law of the sample under
`θ₀ + h\,n^{-1/2}`), asymptotically normal with information matrix `I`: there are
statistics `Zₙ` with `Zₙ ⇒ N(0, I)` under `Q_{n,0}` and a log-likelihood-ratio expansion
$$ \log\frac{dQ_{n,h}}{dQ_{n,0}}
   \;=\; \langle h, Z_n\rangle - \tfrac12\, h^{\top} I\, h + o_{P}(1). $$
The alternatives are the shell `{h : h⊤ I h ≥ b²}`, i.e. `|I^{1/2}h| ≥ b`. The assertion
is that no asymptotically level-`α` test sequence can beat the noncentral chi-squared
value `P{χ²_k(b²) > c_{k,1−α}}` in minimum power over that shell:

* `asymptotic_maximin_upper_bound` — the upper bound (the transfer lemma);
* `sphereAverage_lr_monotone` — the sphere-averaged likelihood-ratio helper.

**Why these two, and how they fit together.** The bound is proved by the mixture route:
the minimum power over the shell is at most the *average* power against any probability
distribution `σ` supported on the shell, i.e. the power against the mixture
`∫ Q_{n,h} dσ(h)`; by the Neyman–Pearson lemma the latter is at most the power of the
likelihood-ratio test of `Q_{n,0}` against that mixture; and asymptotic normality
identifies the limit of that power with the corresponding quantity in the Gaussian shift
experiment. Taking `σ` uniform on the sphere `{|I^{1/2}h| = b}` makes the limiting
likelihood ratio
$$ x \;\longmapsto\; \int e^{\langle h, x\rangle - |h|^2/2} \, d\sigma(h) $$
a *monotone function of `|x|`* — that is `sphereAverage_lr_monotone` — so the limiting
Neyman–Pearson test is exactly the chi-squared test `{|x|² > c_{k,1−α}}`, whose power
against the least favourable shell is `P{χ²_k(b²) > c_{k,1−α}}`. The helper is thus the
step that turns an abstract mixture bound into the concrete chi-squared number, and it is
also the reason the *same* number appears in both consumers.

**DEFERRAL-ELIGIBLE.** `asymptotic_maximin_upper_bound` is registered in the batch ledger
as a conditional fallback: it is to be proved by the mixture–Neyman–Pearson route above,
but if that route stalls it is the pre-agreed named debt for this work item, and the two
consuming maximin theorems (`ChiSquaredMaximin.lean`, `SmoothTest.lean`) close modulo it.
`sphereAverage_lr_monotone` is not deferral-eligible.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.3 (Pearson's Chi-Squared Statistic), the least-favorable spherical mixture
underlying Theorem 16.3.2, in the form transferred to the smooth tests of §16.4 (Theorem
16.4.1). (`TSH4 §16.3 Thm 16.3.2; §16.4 Thm 16.4.1`.)

**Proof formalization notes.**
* The alternative shell is written `b² ≤ h⊤ I h` rather than `b ≤ |I^{1/2} h|`, which
  avoids introducing a matrix square root altogether. The two are the same condition, and
  the quadratic-form version is what both consumers supply: `∑ⱼ hⱼ²/πⱼ ≥ b²` for the
  multinomial information, and `|h|² ≥ b²` for the smooth model, where `I` is the
  identity.
* Asymptotic normality is spelled out inline (a likelihood-ratio field `L` making
  `Q_{n,h}` an explicit density with respect to `Q_{n,0}`, plus convergence in
  `Q_{n,0}`-probability of the expansion remainder) instead of being imported from the
  local-asymptotic-normality development. This keeps the file self-contained, keeps the
  hypothesis list auditable, and keeps the dependency on that development read-only.
* The minimum power over the shell is `sInf` of the image of the power function; the
  shell is nonempty for `b > 0` and `I` positive definite, and powers lie in `[0,1]`, so
  the `sInf` junk conventions are never reached.
* `sphereAverage_lr_monotone` quantifies over *any* rotation-invariant probability measure
  concentrated on the sphere of radius `b`, rather than constructing the uniform measure:
  the hypotheses characterize that measure, and the extra generality costs nothing.
* The helper is stated in the standardized experiment (covariance the identity); the
  general positive-definite case is obtained by the linear change of variables
  `x ↦ I^{-1/2} x`, which is why the consumers may assume `I = Iₖ` without loss.
* `noncentralChiSquared` takes its noncentrality parameter in `ℝ≥0`; `b² ≥ 0` is passed
  through `Real.toNNReal`, which is the identity on the value used.

**Bibliographic comments.** The maximin principle for tests and the least-favourable
mixture device are due to J. Neyman and E. S. Pearson ("On the problem of the most
efficient tests of statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933),
289–337) and to A. Wald ("Statistical decision functions which minimize the maximum
risk," *Ann. of Math.* **46** (1945), 265–280). The rotation-invariant mixture that
produces the chi-squared test as a maximin procedure in the Gaussian shift experiment
goes back to S. N. Roy and R. C. Bose and, in the invariance formulation, to
C. Stein ("Some problems in multivariate analysis, Part I," Technical Report 6, Stanford,
1956). The reduction of local testing problems to a Gaussian shift experiment is due to
L. Le Cam ("Locally asymptotically normal families of distributions," *Univ. California
Publ. Statist.* **3** (1960), 37–98).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace Matrix

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

/-! ### The least-favourable mixing measure

The mixture route needs one rotation-invariant probability measure carried by the sphere
of radius `b`.  It is not constructed by hand: it is the law of the *direction* of a
standard Gaussian vector, rescaled to length `b`.  Rotation invariance is then inherited
from `stdGaussian_map`, because the radial projection commutes with every linear isometry.
-/

section MixingMeasure

variable {k : ℕ}

/-- For `k ≥ 1` the standard Gaussian puts no mass at the origin. -/
private lemma stdGaussian_ae_ne_zero (hk : 0 < k) :
    ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ≠ 0 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have hzero : (stdGaussian (EuclideanSpace ℝ (Fin k))) {0} = 0 := by
    rw [← map_pi_eq_stdGaussian,
      Measure.map_apply (WithLp.measurable_toLp 2 (Fin k → ℝ)) (measurableSet_singleton _)]
    refine measure_mono_null (t := (fun x : Fin k → ℝ => x (0 : Fin k)) ⁻¹' {0}) ?_ ?_
    · intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [show x = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)).ofLp from rfl, hx]
      rfl
    · rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
        Measure.pi_map_eval]
      haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
      simp
  have : ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ∉ ({0} : Set _) := by
    rw [ae_iff]
    simpa using hzero
  filter_upwards [this] with z hz using by simpa using hz

/-- **The least-favourable mixing measure exists.**  For `k ≥ 1` and `b > 0` there is a
rotation-invariant probability measure carried by the sphere of radius `b`, namely the law
of `b‖y‖⁻¹ y` for a standard Gaussian `y`. -/
private lemma exists_sphere_mixing_measure (hk : 0 < k) {b : ℝ} (hb : 0 < b) :
    ∃ σ : Measure (EuclideanSpace ℝ (Fin k)), IsProbabilityMeasure σ ∧
      (∀ᵐ h ∂σ, ‖h‖ = b) ∧
      (∀ e : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k), σ.map (⇑e) = σ) := by
  classical
  set E := EuclideanSpace ℝ (Fin k)
  set γ : Measure E := stdGaussian E with hγ
  set p : E → E := fun y => (b * ‖y‖⁻¹) • y with hp
  have hpmeas : Measurable p := by
    refine Measurable.smul ?_ measurable_id
    exact measurable_const.mul measurable_norm.inv
  refine ⟨γ.map p, Measure.isProbabilityMeasure_map hpmeas.aemeasurable, ?_, ?_⟩
  · have hset : MeasurableSet {z : E | ¬ ‖z‖ = b} :=
      (measurableSet_eq_fun measurable_norm measurable_const).compl
    rw [ae_iff, Measure.map_apply hpmeas hset]
    refine measure_mono_null (t := {y : E | y = 0}) ?_ ?_
    · intro y hy
      by_contra hy0
      simp only [Set.mem_setOf_eq] at hy0
      have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine hy ?_
      simp only [Set.mem_setOf_eq, hp, norm_smul, Real.norm_eq_abs,
        abs_mul, abs_inv, abs_norm, abs_of_pos hb]
      field_simp
      exact (abs_of_nonneg (norm_nonneg y)).symm
    · have := stdGaussian_ae_ne_zero (k := k) hk
      rw [ae_iff] at this
      simpa [hγ, Set.compl_setOf] using this
  · intro e
    have hemeas : Measurable (⇑e) := e.continuous.measurable
    have hcomm : (⇑e) ∘ p = p ∘ (⇑e) := by
      funext y
      simp only [Function.comp_apply, hp, map_smul, e.norm_map]
    calc (γ.map p).map (⇑e) = γ.map ((⇑e) ∘ p) := by
          rw [Measure.map_map hemeas hpmeas]
      _ = γ.map (p ∘ (⇑e)) := by rw [hcomm]
      _ = (γ.map (⇑e)).map p := by rw [Measure.map_map hpmeas hemeas]
      _ = γ.map p := by rw [hγ, stdGaussian_map e]

end MixingMeasure

/-! ### The sphere-averaged likelihood ratio -/

/-- **The sphere-averaged likelihood ratio, radial form.**  Strengthening of
`sphereAverage_lr_monotone` for `k ≥ 1`: the radial profile `g` is not merely monotone but
*continuous* and *strictly* increasing on `[0, ∞)`.  Both strengthenings are needed by the
mixture–Neyman–Pearson argument: continuity to push `g ‖Z_n‖` through the continuous
mapping theorem, strict monotonicity to identify the limiting Neyman–Pearson rejection
region `{g ‖x‖ > g √c}` with the chi-squared region `{‖x‖² > c}` *exactly* (an inclusion in
one direction only would leave a positive slack in the final bound). -/
private lemma sphereAverage_radial {k : ℕ} {b : ℝ}
    {σ : Measure (EuclideanSpace ℝ (Fin k))} (hk : 0 < k) (hb : 0 < b)
    (hσ : IsProbabilityMeasure σ) (hsphere : ∀ᵐ h ∂σ, ‖h‖ = b)
    (hrot : ∀ e : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k), σ.map (⇑e) = σ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ StrictMonoOn g (Set.Ici 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin k),
        (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ) = g ‖x‖ := by
  classical
  haveI := hσ
  haveI : NeZero k := ⟨hk.ne'⟩
  set E := EuclideanSpace ℝ (Fin k)
  -- Radial invariance: the sphere average depends on `x` only through `‖x‖`.
  have hradial : ∀ x y : E, ‖x‖ = ‖y‖ →
      (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ)
        = ∫ h, Real.exp (⟪h, y⟫_ℝ - b ^ 2 / 2) ∂σ := by
    intro x y hxy
    obtain ⟨e, he⟩ : ∃ e : E ≃ₗᵢ[ℝ] E, e y = x := ⟨_, Submodule.reflection_sub hxy.symm⟩
    have hmeas : Measurable (⇑e) := e.continuous.measurable
    have hg : AEStronglyMeasurable
        (fun h : E => Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)) (σ.map e) := by
      rw [hrot e]
      exact (by fun_prop : Continuous fun h : E =>
        Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable
    calc (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ)
        = ∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂(σ.map e) := by rw [hrot e]
      _ = ∫ h, Real.exp (⟪e h, x⟫_ℝ - b ^ 2 / 2) ∂σ := integral_map hmeas.aemeasurable hg
      _ = ∫ h, Real.exp (⟪h, y⟫_ℝ - b ^ 2 / 2) ∂σ := by
          apply integral_congr_ae; filter_upwards with h
          rw [show (⟪e h, x⟫_ℝ) = ⟪h, y⟫_ℝ from by rw [← he]; exact e.inner_map_map h y]
  set u : E := EuclideanSpace.single (0 : Fin k) (1 : ℝ) with hu
  have hunorm : ‖u‖ = 1 := by rw [hu, EuclideanSpace.single, PiLp.norm_single, norm_one]
  have hbound : ∀ᵐ h ∂σ, |⟪h, u⟫_ℝ| ≤ b := by
    filter_upwards [hsphere] with h hh
    have := abs_real_inner_le_norm h u; rw [hh, hunorm, mul_one] at this; exact this
  -- Integrability of the one-parameter family and of its `cosh` form.
  have hintu : ∀ s : ℝ, Integrable (fun h : E => Real.exp (s * ⟪h, u⟫_ℝ - b ^ 2 / 2)) σ := by
    intro s
    refine (integrable_const (Real.exp (|s| * b))).mono'
      ((by fun_prop : Continuous fun h : E =>
        Real.exp (s * ⟪h, u⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable) ?_
    filter_upwards [hbound] with h ht
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    have hsb : s * ⟪h, u⟫_ℝ ≤ |s| * b := by
      calc s * ⟪h, u⟫_ℝ ≤ |s * ⟪h, u⟫_ℝ| := le_abs_self _
        _ = |s| * |⟪h, u⟫_ℝ| := abs_mul s _
        _ ≤ |s| * b := mul_le_mul_of_nonneg_left ht (abs_nonneg s)
    nlinarith [sq_nonneg b]
  have hcosh_int : ∀ r : ℝ,
      Integrable (fun h : E => Real.cosh (r * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2))) σ := by
    intro r
    refine (integrable_const (Real.cosh (|r| * b) * Real.exp (-(b ^ 2 / 2)))).mono'
      ((by fun_prop : Continuous fun h : E =>
        Real.cosh (r * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2))).aestronglyMeasurable) ?_
    filter_upwards [hbound] with h ht
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_abs, abs_of_pos hb]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg r)
  -- The reflection identity, and the resulting `cosh` form of the average.
  have hR : ∀ r : ℝ, (∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ)
      = ∫ h, Real.exp (-(r * ⟪h, u⟫_ℝ) - b ^ 2 / 2) ∂σ := by
    intro r
    have hmeas : Measurable (⇑(LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)) :=
      (LinearIsometryEquiv.neg ℝ).continuous.measurable
    have hg : AEStronglyMeasurable
        (fun h : E => Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2))
        (σ.map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)) := by
      rw [hrot (LinearIsometryEquiv.neg ℝ)]
      exact (by fun_prop : Continuous fun h : E =>
        Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable
    calc (∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ)
        = ∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2)
            ∂(σ.map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)) := by
          rw [hrot (LinearIsometryEquiv.neg ℝ)]
      _ = ∫ h, Real.exp (r * ⟪(LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) h, u⟫_ℝ - b ^ 2 / 2) ∂σ :=
          integral_map hmeas.aemeasurable hg
      _ = ∫ h, Real.exp (-(r * ⟪h, u⟫_ℝ) - b ^ 2 / 2) ∂σ := by
          apply integral_congr_ae; filter_upwards with h
          have hneg : (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) h = -h := by
            simp [LinearIsometryEquiv.coe_neg]
          rw [hneg, inner_neg_left]
          congr 1; ring
  have hsymm : ∀ r : ℝ, (∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ)
      = ∫ h, Real.cosh (r * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2)) ∂σ := by
    intro r
    have hint₂ : Integrable (fun h : E => Real.exp (-(r * ⟪h, u⟫_ℝ) - b ^ 2 / 2)) σ := by
      have h1 := hintu (-r)
      simp only [neg_mul] at h1
      exact h1
    have havg : (∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ)
        = (1 / 2) * ((∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ)
            + ∫ h, Real.exp (-(r * ⟪h, u⟫_ℝ) - b ^ 2 / 2) ∂σ) := by
      rw [← hR r]; ring
    rw [havg, ← integral_add (hintu r) hint₂, ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with h
    rw [Real.cosh_eq, sub_eq_add_neg (r * ⟪h, u⟫_ℝ), sub_eq_add_neg (-(r * ⟪h, u⟫_ℝ)),
      Real.exp_add, Real.exp_add]
    ring
  -- The direction functional is non-null: otherwise `σ` would sit at the origin.
  have hpos : σ {h : E | ⟪h, u⟫_ℝ ≠ 0} ≠ 0 := by
    intro hzero
    set B : OrthonormalBasis (Fin k) ℝ E := EuclideanSpace.basisFun (Fin k) ℝ with hB
    have hall : ∀ i : Fin k, ∀ᵐ h ∂σ, ⟪h, B i⟫_ℝ = 0 := by
      intro i
      have hni : ‖(B i : E)‖ = ‖u‖ := by rw [hunorm, B.orthonormal.1 i]
      obtain ⟨e, he⟩ : ∃ e : E ≃ₗᵢ[ℝ] E, e u = B i := ⟨_, Submodule.reflection_sub hni.symm⟩
      have hu0 : ∀ᵐ h ∂σ, ⟪h, u⟫_ℝ = 0 := by
        rw [ae_iff]; simpa using hzero
      have hstep : ∀ᵐ h ∂σ, ⟪(e h : E), B i⟫_ℝ = 0 := by
        filter_upwards [hu0] with h hh
        rw [← he, e.inner_map_map]
        exact hh
      rw [← hrot e, ae_map_iff e.continuous.measurable.aemeasurable
        (measurableSet_eq_fun (by fun_prop) measurable_const)]
      exact hstep
    have hzeroae : ∀ᵐ h ∂σ, h = 0 := by
      rw [← ae_all_iff] at hall
      filter_upwards [hall] with h hh
      have h0 : B.repr h = 0 := by
        ext i
        rw [OrthonormalBasis.repr_apply_apply]
        simpa [real_inner_comm] using hh i
      simpa using congrArg B.repr.symm h0
    have hcontra : ∀ᵐ h ∂σ, False := by
      filter_upwards [hsphere, hzeroae] with h h1 h2
      rw [h2, norm_zero] at h1
      exact hb.ne h1
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hcontra
    exact (hσ.ne_zero σ) hcontra
  refine ⟨fun r => ∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ, ?_, ?_, ?_⟩
  · -- Continuity, by dominated convergence with a locally constant bound.
    rw [continuous_iff_continuousAt]
    intro r₀
    refine continuousAt_of_dominated
      (F := fun (r : ℝ) (h : E) => Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2))
      (bound := fun _ : E => Real.exp ((|r₀| + 1) * b)) ?_ ?_ (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun r =>
        (by fun_prop : Continuous fun h : E =>
          Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds r₀ one_pos] with r hr
      have hrle : |r| ≤ |r₀| + 1 := by
        have hd : |r - r₀| < 1 := by simpa [Real.dist_eq] using hr
        have hd2 : |r| - |r₀| ≤ |r - r₀| := abs_sub_abs_le_abs_sub r r₀
        linarith
      filter_upwards [hbound] with h ht
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      refine Real.exp_le_exp.mpr ?_
      have h1 : r * ⟪h, u⟫_ℝ ≤ |r| * b := by
        calc r * ⟪h, u⟫_ℝ ≤ |r * ⟪h, u⟫_ℝ| := le_abs_self _
          _ = |r| * |⟪h, u⟫_ℝ| := abs_mul _ _
          _ ≤ |r| * b := mul_le_mul_of_nonneg_left ht (abs_nonneg r)
      have h2 : |r| * b ≤ (|r₀| + 1) * b := mul_le_mul_of_nonneg_right hrle hb.le
      nlinarith [sq_nonneg b]
    · exact Filter.Eventually.of_forall fun h => by fun_prop
  · -- Strict monotonicity, via the `cosh` form and the non-null direction functional.
    intro r₁ hr₁ r₂ hr₂ hr
    simp only [Set.mem_Ici] at hr₁ hr₂
    simp only
    rw [hsymm r₁, hsymm r₂]
    set F : E → ℝ := fun h => Real.cosh (r₂ * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2))
      - Real.cosh (r₁ * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2)) with hF
    have hFint : Integrable F σ := (hcosh_int r₂).sub (hcosh_int r₁)
    have hFnn : ∀ h : E, 0 ≤ F h := by
      intro h
      rw [hF]
      simp only [sub_nonneg]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hr₁, abs_of_nonneg hr₂]
      exact mul_le_mul_of_nonneg_right hr.le (abs_nonneg _)
    have hsupp : {h : E | ⟪h, u⟫_ℝ ≠ 0} ⊆ Function.support F := by
      intro h hh
      simp only [Set.mem_setOf_eq] at hh
      have hlt : Real.cosh (r₁ * ⟪h, u⟫_ℝ) < Real.cosh (r₂ * ⟪h, u⟫_ℝ) := by
        refine Real.cosh_lt_cosh.mpr ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hr₁, abs_of_nonneg hr₂]
        exact mul_lt_mul_of_pos_right hr (abs_pos.mpr hh)
      have : 0 < F h := by
        rw [hF]
        simp only [sub_pos]
        exact mul_lt_mul_of_pos_right hlt (Real.exp_pos _)
      exact ne_of_gt this
    have hposF : 0 < ∫ h, F h ∂σ := by
      rw [integral_pos_iff_support_of_nonneg (fun h => hFnn h) hFint]
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hpos) (measure_mono hsupp)
    have hsplit : (∫ h, F h ∂σ)
        = (∫ h, Real.cosh (r₂ * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2)) ∂σ)
          - ∫ h, Real.cosh (r₁ * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2)) ∂σ :=
      integral_sub (hcosh_int r₂) (hcosh_int r₁)
    linarith [hsplit ▸ hposF]
  · -- The radial value.
    intro x
    have hxu : ‖x‖ = ‖(‖x‖ : ℝ) • u‖ := by
      rw [norm_smul, hunorm, mul_one, Real.norm_of_nonneg (norm_nonneg x)]
    rw [hradial x ((‖x‖ : ℝ) • u) hxu]
    simp only
    apply integral_congr_ae; filter_upwards with h
    rw [real_inner_smul_right]

/-- **The sphere-averaged likelihood ratio is a monotone function of the norm.**

For the Gaussian shift experiment `N(h, Iₖ)` against `N(0, Iₖ)`, the likelihood ratio at
`x` is `exp(⟨h, x⟩ − |h|²/2)`. Averaging it over a rotation-invariant probability measure
`σ` carried by the sphere of radius `b` produces a function of `x` that depends on `x`
only through `|x|`, and is nondecreasing in `|x|`.

Consequently the Neyman–Pearson test of `N(0, Iₖ)` against the mixture `∫ N(h, Iₖ) dσ(h)`
rejects for large `|x|`, i.e. it *is* the chi-squared test; this is the step that pins the
maximin value to a noncentral chi-squared tail probability. -/
theorem sphereAverage_lr_monotone {k : ℕ} {b : ℝ}
    {σ : Measure (EuclideanSpace ℝ (Fin k))}
    -- USER-INPUT: the shell has positive radius; `b = 0` is the null itself
    (hb : 0 < b)
    -- USER-INPUT: `σ` is a probability distribution (the mixing distribution)
    (hσ : IsProbabilityMeasure σ)
    -- USER-INPUT: `σ` is carried by the sphere of radius `b`
    (hsphere : ∀ᵐ h ∂σ, ‖h‖ = b)
    -- USER-INPUT: `σ` is rotation invariant; together with the previous hypothesis this
    -- characterizes the uniform distribution on that sphere
    (hrot : ∀ e : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      σ.map (⇑e) = σ) :
    ∃ g : ℝ → ℝ, MonotoneOn g (Set.Ici 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin k),
        (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ) = g ‖x‖ := by
  classical
  set E := EuclideanSpace ℝ (Fin k)
  -- Radial invariance: the sphere average depends on `x` only through `‖x‖`.  This is the
  -- one place the rotation invariance of `σ` is used.
  have hradial : ∀ x y : E, ‖x‖ = ‖y‖ →
      (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ)
        = ∫ h, Real.exp (⟪h, y⟫_ℝ - b ^ 2 / 2) ∂σ := by
    intro x y hxy
    obtain ⟨e, he⟩ : ∃ e : E ≃ₗᵢ[ℝ] E, e y = x := ⟨_, Submodule.reflection_sub hxy.symm⟩
    have hmeas : Measurable (⇑e) := e.continuous.measurable
    have hg : AEStronglyMeasurable
        (fun h : E => Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)) (σ.map e) := by
      rw [hrot e]
      exact (by fun_prop : Continuous fun h : E =>
        Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable
    calc (∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂σ)
        = ∫ h, Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2) ∂(σ.map e) := by rw [hrot e]
      _ = ∫ h, Real.exp (⟪e h, x⟫_ℝ - b ^ 2 / 2) ∂σ := integral_map hmeas.aemeasurable hg
      _ = ∫ h, Real.exp (⟪h, y⟫_ℝ - b ^ 2 / 2) ∂σ := by
          apply integral_congr_ae; filter_upwards with h
          rw [show (⟪e h, x⟫_ℝ) = ⟪h, y⟫_ℝ from by rw [← he]; exact e.inner_map_map h y]
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: the space is a point, so the average is constant.
    subst hk0
    refine ⟨fun _ => Real.exp (-(b ^ 2 / 2)), fun a _ b' _ _ => le_refl _, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp only [inner_zero_right, zero_sub, norm_zero, integral_const, probReal_univ, one_smul]
  · -- `k ≥ 1`: the strengthened radial form of this same average, proved above.
    obtain ⟨g, -, hmono, hval⟩ := sphereAverage_radial hk hb hσ hsphere hrot
    exact ⟨g, hmono.monotoneOn, hval⟩

/-! ### Cameron–Martin, and the value of the sphere average on the chi-squared region

The mixture route ends by evaluating the sphere-averaged likelihood ratio over the
limiting Neyman–Pearson rejection region.  Everything here stays at the level of measures
(`withDensity`, `lintegral`), so no integrability side conditions on Gaussian exponential
moments are ever needed. -/

section CameronMartin

variable {k : ℕ}

/-- **1-D Gaussian Girsanov shift**, measure form. -/
private lemma gaussianReal_withDensity_shift' (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0),
    ← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  ext x
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Product-form Gaussian Girsanov shift** on `ι → ℝ`. -/
private lemma pi_gaussianReal_withDensity_shift' {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
        = gaussianReal (a i) 1 :=
    fun i => gaussianReal_withDensity_shift' (a i)
  haveI : ∀ i : ι, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  have hdensity : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - (a i) ^ 2 / 2)) := by
    funext y
    rw [show ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)
          = ∑ i, (a i * y i - (a i) ^ 2 / 2) from by
          rw [Finset.sum_sub_distrib, Finset.sum_div],
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hdensity, pi_withDensity_prod
    (f := fun i (x : ℝ) => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- Transport of a `withDensity` through the coordinate map `WithLp.toLp 2`. -/
private lemma map_toLp_withDensity' (μ : Measure (Fin k → ℝ))
    {w : (Fin k → ℝ) → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = (μ.map (WithLp.toLp 2)).withDensity (fun z => w z.ofLp) := by
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hw' : Measurable (fun z : EuclideanSpace ℝ (Fin k) => w z.ofLp) :=
    hw.comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))
  ext A hA
  rw [Measure.map_apply hT hA, withDensity_apply _ (hT hA), withDensity_apply _ hA,
    ← lintegral_indicator (hT hA), ← lintegral_indicator hA,
    lintegral_map (hw'.indicator hA) hT]
  classical
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply, Set.mem_preimage]

/-- **Cameron–Martin identity, measure form.**  Translating the standard Gaussian on
`EuclideanSpace ℝ (Fin k)` by `v` is the same as tilting it by `exp(⟪v, ·⟫ − ‖v‖²/2)`. -/
private lemma stdGaussian_map_add_eq_withDensity' (v : EuclideanSpace ℝ (Fin k)) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).withDensity
          (fun z => ENNReal.ofReal (Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have hshiftpi : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  have hLHS : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (π₀.map (fun x i => a i + x i)).map (WithLp.toLp 2) := by
    rw [← hmapT, Measure.map_map (by fun_prop) hT,
      Measure.map_map hT
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i)))]
    congr 1
  rw [hLHS, hshiftpi, ← pi_gaussianReal_withDensity_shift' a, ← hπ₀,
    map_toLp_withDensity' π₀ (by fun_prop), hmapT]
  congr 1
  funext z
  rw [hsum, hnorm]

/-- With unit covariance, `multivariateGaussian` is a translate of the standard Gaussian. -/
private lemma mvGaussian_one_eq_map_add' (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The chi-squared rejection region is measurable. -/
private lemma measurableSet_normSq_gt (c : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin k) | c < ‖x‖ ^ 2} :=
  measurableSet_lt measurable_const (by fun_prop)

/-- **Shifted Gaussian mass of the chi-squared region.**  For a shift of length `b` the
standard Gaussian mass of `{‖x‖² > c}` after translation is the noncentral chi-squared
upper tail with noncentrality `b²`. -/
private lemma stdGaussian_shift_normSq_tail {b c : ℝ} (hb : 0 ≤ b)
    {v : EuclideanSpace ℝ (Fin k)} (hv : ‖v‖ = b) :
    ((stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z))
        {x : EuclideanSpace ℝ (Fin k) | c < ‖x‖ ^ 2}
      = noncentralChiSquared k (b ^ 2).toNNReal (Set.Ioi c) := by
  have hnorm : ‖v‖ = Real.sqrt (((b ^ 2).toNNReal : ℝ)) := by
    rw [hv, Real.coe_toNNReal _ (sq_nonneg b), Real.sqrt_sq hb]
  have h1 : noncentralChiSquared k (b ^ 2).toNNReal
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖v + x‖ ^ 2) := by
    rw [← map_normSq_multivariateGaussian_of_norm_eq k _ hnorm, mvGaussian_one_eq_map_add',
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h1, Measure.map_apply (by fun_prop) measurableSet_Ioi,
    Measure.map_apply (by fun_prop) (measurableSet_normSq_gt c)]
  rfl

/-- **The central chi-squared as a standard-Gaussian region.** -/
private lemma stdGaussian_normSq_tail (hk : 0 < k) (c : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))) {x : EuclideanSpace ℝ (Fin k) | c < ‖x‖ ^ 2}
      = chiSquared k (Set.Ioi c) := by
  have h0 : ‖(0 : EuclideanSpace ℝ (Fin k))‖ = 0 := norm_zero
  have := stdGaussian_shift_normSq_tail (k := k) (b := 0) (c := c) le_rfl h0
  rw [show ((0 : ℝ) ^ 2).toNNReal = 0 from by norm_num, noncentralChiSquared_zero hk] at this
  rw [← this]
  congr 1
  rw [show (fun z : EuclideanSpace ℝ (Fin k) => (0 : EuclideanSpace ℝ (Fin k)) + z) = id from by
    funext z; simp]
  exact (Measure.map_id).symm

/-- **Value of the sphere-averaged likelihood ratio over the chi-squared region.**
Integrating the mixture likelihood ratio over `{‖x‖² > c}` against the standard Gaussian
returns exactly the noncentral chi-squared upper tail — the maximin value.  This is
Fubini–Tonelli followed by Cameron–Martin, the shifted mass being constant on the sphere by
direction invariance. -/
private lemma setLIntegral_sphereAverage {b c : ℝ} {σ : Measure (EuclideanSpace ℝ (Fin k))}
    (hb : 0 < b) (hσ : IsProbabilityMeasure σ) (hsphere : ∀ᵐ h ∂σ, ‖h‖ = b) :
    ∫⁻ x in {x : EuclideanSpace ℝ (Fin k) | c < ‖x‖ ^ 2},
        (∫⁻ h, ENNReal.ofReal (Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)) ∂σ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = noncentralChiSquared k (b ^ 2).toNNReal (Set.Ioi c) := by
  haveI := hσ
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set A : Set (EuclideanSpace ℝ (Fin k)) := {x | c < ‖x‖ ^ 2} with hA
  have hAmeas : MeasurableSet A := measurableSet_normSq_gt c
  have hjoint : AEMeasurable
      (Function.uncurry fun (x : EuclideanSpace ℝ (Fin k)) (h : EuclideanSpace ℝ (Fin k)) =>
        ENNReal.ofReal (Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2))) ((γ.restrict A).prod σ) := by
    refine Measurable.aemeasurable ?_
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (by fun_prop)))
  rw [lintegral_lintegral_swap hjoint]
  have hinner : ∀ᵐ h ∂σ,
      (∫⁻ x in A, ENNReal.ofReal (Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2)) ∂γ)
        = noncentralChiSquared k (b ^ 2).toNNReal (Set.Ioi c) := by
    filter_upwards [hsphere] with h hh
    have hrew : ∀ x : EuclideanSpace ℝ (Fin k),
        ENNReal.ofReal (Real.exp (⟪h, x⟫_ℝ - b ^ 2 / 2))
          = ENNReal.ofReal (Real.exp (⟪h, x⟫_ℝ - ‖h‖ ^ 2 / 2)) := by
      intro x; rw [hh]
    simp_rw [hrew]
    rw [← withDensity_apply _ hAmeas, ← stdGaussian_map_add_eq_withDensity' h]
    exact stdGaussian_shift_normSq_tail hb.le hh
  rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]

end CameronMartin

/-! ### The transfer lemma -/

/-- **Asymptotic maximin upper bound for multisided local alternatives.**

Let `{Q_{n,h}}` be an asymptotically normal array of local experiments, standardized so
that the centring statistics converge to the *standard* Gaussian, and let `φₙ` be any
sequence of tests whose null power tends to `α`. Then the minimum power of `φₙ` over any
family `S n` of local alternatives containing the sphere `‖h‖ = b` cannot exceed, in the
limit, the noncentral chi-squared value
$$ P\bigl\{\chi^2_k(b^2) > c_{k,1-\alpha}\bigr\}. $$

**Two amendments to the frozen statement, both forced and both strengthenings for the
consumers** (see the module docstring and the proof note below).

* *Shell-parametrised conclusion.* The frozen statement concluded for the single shell
  `{h : h⊤ I h ≥ b²}`, which is **not** the shell of either consumer: `SmoothTest` uses the
  bounded shell `{b ≤ ‖h‖ ≤ B}` and `ChiSquaredMaximin` uses `multinomialShell π b n`, which
  carries the extra sample-size dependent constraint `πⱼ + hⱼ/√n ≥ 0`. Both are *subsets*,
  and `sInf` over a subset is larger, so the frozen conclusion transfers to neither. The
  proof, on the other hand, gives all of them at once: the least-favourable mixing measure
  is carried by the compact sphere `‖h‖ = b`, which sits inside every one of these shells.
  Quantifying over `S` with `{h | ‖h‖ = b} ⊆ S n` is therefore the correct — and strictly
  stronger — statement.
* *Standardized information.* The information matrix is taken to be the identity, i.e.
  `Zₙ ⇒ N(0, Iₖ)` and the log-likelihood expansion is `⟪h, Zₙ⟫ − ‖h‖²/2`. The general
  positive-definite case is a pure reparametrisation and is *not* a further theorem: with
  `A = I^{1/2}` and `η = A h` one has `⟪h, Zₙ⟫ = ⟪η, A⁻¹Zₙ⟫`, `h⊤ I h = ‖η‖²` and
  `A⁻¹Zₙ ⇒ N(0, Iₖ)`, so the array `Q'ₙ,η := Q_{n, A⁻¹η}` satisfies the hypotheses below and
  has the same power function; the shell `{h⊤ I h ≥ b²}` is the `A`-preimage of
  `{‖η‖ ≥ b}`. Since the shell is now a parameter, the consumer performs that change of
  variables on its own shell, which is where it belongs.

Two further hypotheses are honest regularity requirements of the mixture argument rather
than restrictions: joint measurability of the log-likelihood field `L` in `(h, ω)` (without
it the mixture likelihood ratio `∫ exp(L n h ·) dσ(h)` is not even a random variable), and
a *uniform-over-the-sphere* LAN remainder, supplied as a measurable envelope `D n` that
tends to `0` in `Q_{n,0}`-probability. The frozen pointwise-in-`h` remainder does not imply
the uniform one, and the mixture step genuinely needs the uniform one; both applications
have it, the sphere being compact. -/
theorem asymptotic_maximin_upper_bound {k : ℕ} {b c α : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {φ : ℕ → Ω → ℝ} {Z : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {L : ℕ → EuclideanSpace ℝ (Fin k) → Ω → ℝ} {D : ℕ → Ω → ℝ}
    {S : ℕ → Set (EuclideanSpace ℝ (Fin k))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the shell has positive radius
    (hb : 0 < b)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the competitors are randomized tests
    (hφ : ∀ n, IsCriticalFn (φ n))
    -- USER-INPUT: the competitors are asymptotically of level `α`
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α))
    -- USER-INPUT: the centring statistics are measurable
    (hZmeas : ∀ n, Measurable (Z n))
    -- USER-INPUT: asymptotic normality, first half: `Zₙ ⇒ N(0, Iₖ)` under the null;
    -- Le Cam 1960
    (hZ : WeakConverges (fun n => (Q n 0).map (Z n))
      (stdGaussian (EuclideanSpace ℝ (Fin k))))
    -- USER-INPUT: the log-likelihood field is jointly measurable in the local parameter
    -- and the sample point
    (hLmeas : ∀ n, Measurable fun p : EuclideanSpace ℝ (Fin k) × Ω => L n p.1 p.2)
    -- USER-INPUT: the local experiments are dominated by the null one, with
    -- log-likelihood ratio `L n h`; Le Cam 1960
    (hdens : ∀ n h, Q n h
      = (Q n 0).withDensity fun ω => ENNReal.ofReal (Real.exp (L n h ω)))
    -- USER-INPUT: the LAN remainder envelope is measurable
    (hDmeas : ∀ n, Measurable (D n))
    -- USER-INPUT: asymptotic normality, second half: the quadratic expansion of the
    -- log-likelihood ratio holds uniformly over the sphere `‖h‖ = b`, with remainder
    -- dominated by the envelope `D n`; Le Cam 1960
    (hLAN : ∀ n h ω, ‖h‖ = b →
      |L n h ω - (⟪h, Z n ω⟫_ℝ - b ^ 2 / 2)| ≤ D n ω)
    -- USER-INPUT: the envelope is `o_P(1)` under the null
    (hD0 : ∀ ε > 0, Tendsto (fun n => ((Q n 0) {ω | ε ≤ D n ω}).toReal) atTop (nhds 0))
    -- USER-INPUT: the alternative families contain the least-favourable sphere
    (hS : ∀ n, {h : EuclideanSpace ℝ (Fin k) | ‖h‖ = b} ⊆ S n) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) '' S n)) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  sorry

end StatLean.HypothesisTesting
