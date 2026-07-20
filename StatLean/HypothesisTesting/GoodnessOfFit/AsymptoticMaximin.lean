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

/-! ### The sphere-averaged likelihood ratio -/

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
  · -- `k ≥ 1`: fix a unit vector `u` and set `g r = ∫ exp(r ⟪h,u⟫ − b²/2)`; then
    -- `g ‖x‖` is the radial value, and the reflection `h ↦ -h` turns `g` into a `cosh`
    -- average, which is monotone in `r ≥ 0`.
    haveI : NeZero k := ⟨hk.ne'⟩
    set u : E := EuclideanSpace.single (0 : Fin k) (1 : ℝ) with hu
    have hunorm : ‖u‖ = 1 := by rw [hu, EuclideanSpace.single, PiLp.norm_single, norm_one]
    -- Integrability of the (one-parameter) integrand, uniformly bounded on the sphere.
    have hintu : ∀ s : ℝ,
        Integrable (fun h : E => Real.exp (s * ⟪h, u⟫_ℝ - b ^ 2 / 2)) σ := by
      intro s
      refine (integrable_const (Real.exp (|s| * b))).mono'
        ((by fun_prop : Continuous fun h : E =>
          Real.exp (s * ⟪h, u⟫_ℝ - b ^ 2 / 2)).aestronglyMeasurable) ?_
      filter_upwards [hsphere] with h hh
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp.mpr
      have ht : |⟪h, u⟫_ℝ| ≤ b := by
        have := abs_real_inner_le_norm h u; rw [hh, hunorm, mul_one] at this; exact this
      have hsb : s * ⟪h, u⟫_ℝ ≤ |s| * b := by
        calc s * ⟪h, u⟫_ℝ ≤ |s * ⟪h, u⟫_ℝ| := le_abs_self _
          _ = |s| * |⟪h, u⟫_ℝ| := abs_mul s _
          _ ≤ |s| * b := mul_le_mul_of_nonneg_left ht (abs_nonneg s)
      nlinarith [sq_nonneg b]
    -- Integrability of the `cosh` form.
    have hcosh_int : ∀ r : ℝ,
        Integrable (fun h : E => Real.cosh (r * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2))) σ := by
      intro r
      refine (integrable_const (Real.cosh (|r| * b) * Real.exp (-(b ^ 2 / 2)))).mono'
        ((by fun_prop : Continuous fun h : E =>
          Real.cosh (r * ⟪h, u⟫_ℝ) * Real.exp (-(b ^ 2 / 2))).aestronglyMeasurable) ?_
      filter_upwards [hsphere] with h hh
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_abs, abs_of_pos hb]
      have ht : |⟪h, u⟫_ℝ| ≤ b := by
        have := abs_real_inner_le_norm h u; rw [hh, hunorm, mul_one] at this; exact this
      exact mul_le_mul_of_nonneg_left ht (abs_nonneg r)
    -- The reflection identity `I(r) = I(−r)`.
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
    -- Symmetrization: the one-exponential average equals the `cosh` average.
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
    refine ⟨fun r => ∫ h, Real.exp (r * ⟪h, u⟫_ℝ - b ^ 2 / 2) ∂σ, ?_, ?_⟩
    · -- Monotonicity via the `cosh` average.
      intro r₁ hr₁ r₂ hr₂ hr
      simp only [Set.mem_Ici] at hr₁ hr₂
      simp only
      rw [hsymm r₁, hsymm r₂]
      apply integral_mono_ae (hcosh_int r₁) (hcosh_int r₂)
      filter_upwards with h
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hr₁, abs_of_nonneg hr₂]
      exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    · -- The radial value is `g ‖x‖`.
      intro x
      have hxu : ‖x‖ = ‖(‖x‖ : ℝ) • u‖ := by
        rw [norm_smul, hunorm, mul_one, Real.norm_of_nonneg (norm_nonneg x)]
      rw [hradial x ((‖x‖ : ℝ) • u) hxu]
      simp only
      apply integral_congr_ae; filter_upwards with h
      rw [real_inner_smul_right]

/-! ### The transfer lemma -/

/-- **Asymptotic maximin upper bound for multisided local alternatives.**

Let `{Q_{n,h}}` be an asymptotically normal array of local experiments with information
matrix `I`, and let `φₙ` be any sequence of tests whose null power tends to `α`. Then the
minimum power of `φₙ` over the local shell `{h : h⊤ I h ≥ b²}` cannot exceed, in the
limit, the noncentral chi-squared value
$$ P\bigl\{\chi^2_k(b^2) > c_{k,1-\alpha}\bigr\}. $$

This is the single statement consumed by both maximin theorems of the directory: with the
multinomial information matrix it gives the upper bound for Pearson's test, and with
`I = Iₖ` it gives the upper bound for the smooth test.

DEFERRAL-ELIGIBLE: registered in the batch ledger as the conditional fallback of this work
item — see the module docstring for the intended mixture–Neyman–Pearson proof. -/
theorem asymptotic_maximin_upper_bound {k : ℕ} {b c α : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {φ : ℕ → Ω → ℝ} {Z : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    {L : ℕ → EuclideanSpace ℝ (Fin k) → Ω → ℝ} {I : Matrix (Fin k) (Fin k) ℝ}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the shell has positive radius
    (hb : 0 < b)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the information matrix is positive definite (nondegenerate experiment)
    (hI : I.PosDef)
    -- USER-INPUT: the competitors are randomized tests
    (hφ : ∀ n, IsCriticalFn (φ n))
    -- USER-INPUT: the competitors are asymptotically of level `α`
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α))
    -- USER-INPUT: the centring statistics are measurable
    (hZmeas : ∀ n, Measurable (Z n))
    -- USER-INPUT: asymptotic normality, first half: `Zₙ ⇒ N(0, I)` under the null;
    -- Le Cam 1960
    (hZ : WeakConverges (fun n => (Q n 0).map (Z n))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) I))
    -- USER-INPUT: the local experiments are dominated by the null one, with
    -- log-likelihood ratio `L n h`; Le Cam 1960
    (hdens : ∀ n h, Q n h
      = (Q n 0).withDensity fun ω => ENNReal.ofReal (Real.exp (L n h ω)))
    -- USER-INPUT: asymptotic normality, second half: the quadratic expansion of the
    -- log-likelihood ratio holds in `Q_{n,0}`-probability, for each fixed local parameter
    (hLAN : ∀ h : EuclideanSpace ℝ (Fin k), ∀ ε > 0, Tendsto
      (fun n => ((Q n 0) {ω | ε ≤ |L n h ω
          - (⟪h, Z n ω⟫_ℝ - (h.ofLp ⬝ᵥ I.mulVec h.ofLp) / 2)|}).toReal)
      atTop (nhds 0)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) ''
        {h : EuclideanSpace ℝ (Fin k) | b ^ 2 ≤ h.ofLp ⬝ᵥ I.mulVec h.ofLp})) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  -- TODO (DEFERRAL-ELIGIBLE — pre-agreed batch-ledger debt).  Intended mixture–NP–Le Cam
  -- proof (module docstring):  the shell infimum is ≤ the average power against the uniform
  -- mixture `σ` on the sphere `{|I^{1/2}h| = b}`; by Neyman–Pearson this is ≤ the power of
  -- the likelihood-ratio test of `Q_{n,0}` against `∫ Q_{n,h} dσ(h)`; asymptotic normality
  -- (the `hZ`/`hdens`/`hLAN` package, Le Cam's third lemma) identifies the limit of that
  -- power with the Gaussian-shift quantity, where `sphereAverage_lr_monotone` makes the
  -- limiting NP test the χ² test `{|x|² > c}`, whose power against the least-favourable
  -- sphere mixture is `ncχ²_k(b²)(c, ∞)`.  Requires a weak-convergence + Neyman–Pearson +
  -- Le Cam apparatus not yet present in the project.
  --
  -- NOTE for the `SmoothTest` consumer: the *bounded* shell `{b ≤ |I^{1/2}h| ≤ B}` (for any
  -- `B ≥ b`) is reachable by the *same* argument, because the least-favourable mixture `σ`
  -- is supported on the sphere `{|I^{1/2}h| = b}`, which lies inside the bounded shell just
  -- as it lies inside this unbounded one; the mixture bound `sInf … ≤ average power vs σ`
  -- therefore holds verbatim for the bounded shell.  (It cannot be *derived* from this
  -- unbounded statement — `sInf` over a subset is larger — but the proof, once written,
  -- yields both.)
  sorry

end StatLean.HypothesisTesting
