import StatLean.HypothesisTesting.MLR.Defs
import StatLean.HypothesisTesting.NeymanPearson.Lemma
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-!
# One-sided testing under a monotone likelihood ratio

For a real parameter and a family with monotone likelihood ratio in a statistic `T`, the
one-sided problem `H : θ ≤ θ₀` against `K : θ > θ₀` has a **uniformly** most powerful
solution — the same test works against every alternative — namely
$$ \varphi(x) = 1 \ \text{ if } T(x) > C, \qquad \gamma \ \text{ if } T(x) = C,
\qquad 0 \ \text{ if } T(x) < C, $$
with `C` and `γ` fixed by the exact-size requirement `E_{θ₀}φ = α`. Beyond optimality, the
test's power function is strictly increasing wherever it is not already `0` or `1`, the
test is simultaneously UMP for every shifted null, and it minimizes the rejection
probability below `θ₀`.

Contents:
* `oneSidedTest T C γ` — the test displayed above;
* `isUMP_oneSided` — existence of `(C, γ)` with size exactly `α`, and uniform optimality;
* `power_strictMono_oneSided` — strict monotonicity of the power function;
* `isUMP_oneSided_shifted` — the same test is UMP at every other null boundary `θ'`, at
  the level it happens to have there;
* `power_min_oneSided` — among all tests of size exactly `α` at `θ₀`, it minimizes the
  rejection probability at every `θ < θ₀`;
* `testRisk`, `essentiallyComplete_oneSidedTest` — the family of one-sided tests is an
  essentially complete class for the two-decision problem with monotone losses;
* `hasMLR_expFamily`, `isUMP_oneSided_expFamily` — the one-parameter exponential family
  has monotone likelihood ratio in its natural statistic, hence a UMP one-sided test;
* `integral_mono_of_hasMLR` — a monotone statistic has monotone expectation.

**Proof formalization notes.**
* The frozen `HasMLR` is the division-free cross-product condition; it does **not**
  include the classical requirement that `P_θ ≠ P_{θ'}` for `θ < θ'`. That requirement is
  irrelevant for existence and optimality, but it is exactly what makes the power function
  *strictly* increasing (a constant family satisfies `HasMLR` vacuously and has constant
  power). It is therefore carried as an explicit hypothesis of
  `power_strictMono_oneSided` only, and nowhere else.
* The threshold `C` here is a real number, not an extended one: it is a level of the
  statistic `T`, not a likelihood-ratio threshold. Extended thresholds appear only at the
  likelihood-ratio layer.
* The risk of a test is written directly in terms of its power,
  `R(θ, φ) = β_φ(θ)·L₁(θ) + (1 - β_φ(θ))·L₀(θ)`, which agrees with the integral form
  `∫ p_θ {φ L₁ + (1-φ)L₀} dμ` because `∫ p_θ dμ = 1`.
* The minimal-essential-completeness clause (which additionally assumes that the support
  `{x : p_θ(x) > 0}` does not depend on `θ`) is not stated here; only essential
  completeness is.
* The decreasing-`Q` half of the exponential-family corollary is obtained by applying the
  increasing case to `-T`, and is not stated separately.
* `integral_mono_of_hasMLR` is stated in the one-dimensional form, generalized from
  "nondecreasing in `x`" to "nondecreasing along `T`" (taking `𝓧 = ℝ`, `T = id` recovers
  the printed statement). The `n`-sample clause — a function nondecreasing in each of `n`
  independent coordinates has nondecreasing expectation — is a separate induction and is
  not stated here.

**Bibliographic comments.** Monotone likelihood ratio, the resulting uniformly most
powerful one-sided tests, and the complete-class property of the family they form are due
to S. Karlin and H. Rubin ("The theory of decision procedures for distributions with
monotone likelihood ratio," *Ann. Math. Statist.* **27** (1956), 272–299); the
one-parameter exponential-family case and the underlying optimality argument go back to
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **one-sided test** based on the statistic `T` with critical value `C` and boundary
randomization `γ`: reject when `T > C`, reject with probability `γ` when `T = C`, accept
when `T < C`. No constraint on `γ` is imposed by the definition; for `γ ∉ [0,1]` the
result is not a critical function, so the theorems carry `γ ∈ [0,1]` explicitly. -/
noncomputable def oneSidedTest (T : 𝓧 → ℝ) (C γ : ℝ) : 𝓧 → ℝ := fun x =>
  if C < T x then 1 else if T x = C then γ else 0

/-- The **risk** of a test in the two-decision problem: `L₀ θ` is the loss incurred by
accepting the null at `θ` and `L₁ θ` the loss incurred by rejecting it, so the risk is the
power-weighted average `β_φ(θ)·L₁(θ) + (1 - β_φ(θ))·L₀(θ)`. For a probability model this
is the integral form `∫ p_θ {φ L₁ + (1-φ) L₀} dμ`. -/
noncomputable def testRisk {Θ : Type*} (P : Θ → Measure 𝓧) (L₀ L₁ : Θ → ℝ) (φ : 𝓧 → ℝ)
    (θ : Θ) : ℝ :=
  power P φ θ * L₁ θ + (1 - power P φ θ) * L₀ θ

/-- **Existence of a UMP one-sided test.** Under a monotone likelihood ratio in `T` there
are a critical value `C` and a boundary weight `γ ∈ [0,1]` for which the one-sided test has
size exactly `α` at `θ₀` and is uniformly most powerful at level `α` for `H : θ ≤ θ₀`
against `K : θ > θ₀`. -/
theorem isUMP_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model, a family of probability measures indexed by a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: its densities with respect to `μ`
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic in which the likelihood ratio is monotone
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: the monotone-likelihood-ratio property — the whole content of the setup
    (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary and the nominal level
    (θ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (oneSidedTest T C γ) θ₀ = α ∧
      IsUMP P (Set.Iic θ₀) (Set.Ioi θ₀) α (oneSidedTest T C γ) := by
  sorry

/-- **Strict monotonicity of the power function.** On the set of parameter values where
the power is neither `0` nor `1`, the power function of the one-sided test is strictly
increasing.

The distinctness hypothesis `P θ ≠ P θ'` for `θ < θ'` is part of the classical definition
of a monotone likelihood ratio but not of the division-free `HasMLR`; it is what rules out
a constant family, for which the conclusion is false. -/
theorem power_strictMono_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: distinctness of the members — the clause of the classical MLR
    -- definition that `HasMLR` omits; without it the family may be constant
    (hdist : ∀ θ θ' : ℝ, θ < θ' → P θ ≠ P θ')
    -- USER-INPUT: the critical value and the boundary weight of the test under study
    {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ θ θ' : ℝ, θ < θ' →
      0 < power P (oneSidedTest T C γ) θ → power P (oneSidedTest T C γ) θ < 1 →
      0 < power P (oneSidedTest T C γ) θ' → power P (oneSidedTest T C γ) θ' < 1 →
      power P (oneSidedTest T C γ) θ < power P (oneSidedTest T C γ) θ' := by
  sorry

/-- **The same test is UMP at every null boundary.** For any `θ'`, the one-sided test is
uniformly most powerful for `H' : θ ≤ θ'` against `K' : θ > θ'` at the level it happens to
have there, namely `α' = β(θ')`. -/
theorem isUMP_oneSided_shifted
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the critical value and the boundary weight
    {C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (θ' : ℝ) :
    IsUMP P (Set.Iic θ') (Set.Ioi θ') (power P (oneSidedTest T C γ) θ')
      (oneSidedTest T C γ) := by
  sorry

/-- **Minimum rejection probability below the boundary.** Among all tests whose size at
`θ₀` is exactly `α`, the one-sided test minimizes the probability of rejection — the
probability of an error of the first kind — at every `θ < θ₀`. -/
theorem power_min_oneSided
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary, level, and the constants of the test
    (θ₀ : ℝ) {α C γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the test is the one determined by the exact-size requirement
    (hsize : power P (oneSidedTest T C γ) θ₀ = α) :
    ∀ θ < θ₀, ∀ ψ, IsCriticalFn ψ → power P ψ θ₀ = α →
      power P (oneSidedTest T C γ) θ ≤ power P ψ θ := by
  sorry

/-- **The one-sided tests form an essentially complete class.** For the two-decision
problem whose losses satisfy `L₁ - L₀ > 0` below the boundary and `< 0` above it, every
test is matched or beaten, uniformly in `θ`, by a one-sided test. -/
theorem essentiallyComplete_oneSidedTest
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the null boundary and the two loss functions
    (θ₀ : ℝ) (L₀ L₁ : ℝ → ℝ)
    -- USER-INPUT: rejecting costs more than accepting strictly below the boundary …
    (hloss_lt : ∀ θ < θ₀, 0 < L₁ θ - L₀ θ)
    -- USER-INPUT: … and less strictly above it (the monotone-loss condition)
    (hloss_gt : ∀ θ, θ₀ < θ → L₁ θ - L₀ θ < 0) :
    ∀ ψ, IsCriticalFn ψ → ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ θ, testRisk P L₀ L₁ (oneSidedTest T C γ) θ ≤ testRisk P L₀ L₁ ψ θ := by
  sorry

/-- **The one-parameter exponential family has a monotone likelihood ratio** in its
natural statistic, provided the parametrization `θ ↦ η(θ)` is strictly increasing. The
densities are the canonical ones, `exp(η(θ)·T(x) - A(η(θ)))`. -/
theorem hasMLR_expFamily
    -- USER-INPUT: the exponential family (reference measure and natural statistic)
    (E : ExpFamily 𝓧 ℝ)
    -- USER-INPUT: the parametrization, strictly increasing — the printed hypothesis
    -- "`Q` is strictly monotone", in its increasing case
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) :
    HasMLR (fun θ x => Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))) E.stat := by
  intro θ θ' hθθ' x y hTxy
  have hηlt : ηmap θ < ηmap θ' := hη hθθ'
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg (sub_pos.mpr hηlt).le (sub_nonneg.mpr hTxy)]

/-- **UMP one-sided test in a one-parameter exponential family.** For a family presented
in canonical form through a strictly increasing `η`, the test rejecting for large values of
the natural statistic is UMP for `H : θ ≤ θ₀` against `K : θ > θ₀`. -/
theorem isUMP_oneSided_expFamily
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, a family of probability measures
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the parametrization, strictly increasing
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap)
    -- USER-INPUT: the model is the canonical family read through `ηmap`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: every parameter value is in the natural parameter set, so that each
    -- `P θ` really is the tilted probability measure and not the junk zero measure
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the null boundary and the nominal level
    (θ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (oneSidedTest E.stat C γ) θ₀ = α ∧
      IsUMP P (Set.Iic θ₀) (Set.Ioi θ₀) α (oneSidedTest E.stat C γ) := by
  sorry

/-- A density of a probability measure is integrable (local copy of the NP-layer lemma). -/
private lemma density_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- Expectation against a density-carrying measure equals the integral against the density. -/
private lemma integral_density_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (ψ : 𝓧 → ℝ) : ∫ x, ψ x ∂P = ∫ x, ψ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- The density integrates to `1`. -/
private lemma density_integral_one {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : ∫ x, p x ∂μ = 1 := by
  have h1 : ∫ x, (1 : ℝ) ∂P = ∫ x, (1 : ℝ) * p x ∂μ := integral_density_eq h (fun _ => 1)
  simp only [one_mul] at h1
  rw [← h1]; simp

/-- If `ψ` is `P`-integrable and `P` has density `p`, then `ψ·p` is `μ`-integrable. -/
private lemma density_mul_integrable {μ : Measure 𝓧} {p ψ : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (hψ : Integrable ψ P) : Integrable (fun x => ψ x * p x) μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq] at hψ
  refine ((integrable_withDensity_iff hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hψ).congr ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hnn x)]

/-- **Monotone statistics have monotone expectations.** Under a monotone likelihood ratio
in `T`, the expectation of any function that is nondecreasing along `T` is a nondecreasing
function of the parameter. Taking `𝓧 = ℝ` and `T = id` gives the classical statement for a
nondecreasing `ψ`. -/
theorem integral_mono_of_hasMLR
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic and the monotone-likelihood-ratio property
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the integrand
    (ψ : 𝓧 → ℝ) (hψ : Measurable ψ)
    -- USER-INPUT: it is nondecreasing along `T` (for `T = id`: nondecreasing)
    (hmono : ∀ x y, T x ≤ T y → ψ x ≤ ψ y)
    -- USER-INPUT: integrability under every member, so both sides are defined
    (hint : ∀ θ, Integrable ψ (P θ)) :
    Monotone fun θ => ∫ x, ψ x ∂(P θ) := by
  intro θ θ' hθθ'
  show ∫ x, ψ x ∂(P θ) ≤ ∫ x, ψ x ∂(P θ')
  rcases eq_or_lt_of_le hθθ' with h | hlt
  · rw [h]
  -- `θ < θ'`: the double-integral correlation identity `2·(D_θ' − D_θ) = ∫∫ F ≥ 0`.
  rw [integral_density_eq (hp θ) ψ, integral_density_eq (hp θ') ψ]
  have ha : Integrable (p θ) μ := density_integrable (hp θ)
  have hb : Integrable (p θ') μ := density_integrable (hp θ')
  have hψa : Integrable (fun x => ψ x * p θ x) μ := density_mul_integrable (hp θ) (hint θ)
  have hψb : Integrable (fun x => ψ x * p θ' x) μ := density_mul_integrable (hp θ') (hint θ')
  have hone_a : ∫ x, p θ x ∂μ = 1 := density_integral_one (hp θ)
  have hone_b : ∫ x, p θ' x ∂μ = 1 := density_integral_one (hp θ')
  have i1 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)) (μ.prod μ) :=
    Integrable.mul_prod ha hψb
  have i2 : Integrable (fun z : 𝓧 × 𝓧 => p θ' z.1 * (ψ z.2 * p θ z.2)) (μ.prod μ) :=
    Integrable.mul_prod hb hψa
  have i3 : Integrable (fun z : 𝓧 × 𝓧 => ψ z.1 * p θ z.1 * p θ' z.2) (μ.prod μ) :=
    Integrable.mul_prod hψa hb
  have i4 : Integrable (fun z : 𝓧 × 𝓧 => ψ z.1 * p θ' z.1 * p θ z.2) (μ.prod μ) :=
    Integrable.mul_prod hψb ha
  have hFnn : 0 ≤ᵐ[μ.prod μ] fun z : 𝓧 × 𝓧 =>
      p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2 := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    show (0 : ℝ) ≤ p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2
    have key : p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2
        = (ψ z.2 - ψ z.1) * (p θ z.1 * p θ' z.2 - p θ' z.1 * p θ z.2) := by ring
    rw [key]
    rcases le_total (T z.1) (T z.2) with hle | hle
    · exact mul_nonneg (by linarith [hmono z.1 z.2 hle])
        (by linarith [hMLR hlt z.1 z.2 hle])
    · refine mul_nonneg_of_nonpos_of_nonpos (by linarith [hmono z.2 z.1 hle]) ?_
      nlinarith [hMLR hlt z.2 z.1 hle]
  -- Compute the four product integrals separately, then combine.
  have e1 : ∫ z : 𝓧 × 𝓧, p θ z.1 * (ψ z.2 * p θ' z.2) ∂(μ.prod μ)
      = ∫ x, ψ x * p θ' x ∂μ := by
    rw [integral_prod_mul (p θ) (fun y => ψ y * p θ' y), hone_a, one_mul]
  have e2 : ∫ z : 𝓧 × 𝓧, p θ' z.1 * (ψ z.2 * p θ z.2) ∂(μ.prod μ)
      = ∫ x, ψ x * p θ x ∂μ := by
    rw [integral_prod_mul (p θ') (fun y => ψ y * p θ y), hone_b, one_mul]
  have e3 : ∫ z : 𝓧 × 𝓧, ψ z.1 * p θ z.1 * p θ' z.2 ∂(μ.prod μ)
      = ∫ x, ψ x * p θ x ∂μ := by
    rw [integral_prod_mul (fun x => ψ x * p θ x) (p θ'), hone_b, mul_one]
  have e4 : ∫ z : 𝓧 × 𝓧, ψ z.1 * p θ' z.1 * p θ z.2 ∂(μ.prod μ)
      = ∫ x, ψ x * p θ' x ∂μ := by
    rw [integral_prod_mul (fun x => ψ x * p θ' x) (p θ), hone_a, mul_one]
  have hf12 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)
      - p θ' z.1 * (ψ z.2 * p θ z.2)) (μ.prod μ) := i1.sub i2
  have hf123 : Integrable (fun z : 𝓧 × 𝓧 => p θ z.1 * (ψ z.2 * p θ' z.2)
      - p θ' z.1 * (ψ z.2 * p θ z.2) - ψ z.1 * p θ z.1 * p θ' z.2) (μ.prod μ) := hf12.sub i3
  have hFint : (0 : ℝ) ≤ ∫ z : 𝓧 × 𝓧,
      (p θ z.1 * (ψ z.2 * p θ' z.2) - p θ' z.1 * (ψ z.2 * p θ z.2)
        - ψ z.1 * p θ z.1 * p θ' z.2 + ψ z.1 * p θ' z.1 * p θ z.2) ∂(μ.prod μ) :=
    integral_nonneg_of_ae hFnn
  rw [integral_add hf123 i4, integral_sub hf12 i3, integral_sub i1 i2, e1, e2, e3, e4] at hFint
  linarith [hFint]

end StatLean.HypothesisTesting
