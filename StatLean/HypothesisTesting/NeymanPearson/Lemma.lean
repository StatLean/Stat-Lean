import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The fundamental lemma of testing a simple hypothesis against a simple alternative

Let `P₀` and `P₁` be probability measures with densities `p₀`, `p₁` with respect to a
σ-finite measure `μ`. The **likelihood-ratio test** with threshold `C` and boundary
randomization `γ`,
$$ \varphi(x) \;=\; \begin{cases} 1 & p_1(x) > C\,p_0(x), \\
\gamma & p_1(x) = C\,p_0(x), \\ 0 & p_1(x) < C\,p_0(x), \end{cases} $$
is optimal in the strongest possible sense: a suitable `(C, γ)` achieves **exactly** size
`α`, every test of that shape and size is most powerful, and — conversely — every most
powerful test has that shape almost everywhere.

Contents:
* `HasDensity μ p P` — `P = p·μ` for a nonnegative measurable `p` (the dominated setup);
* `npTest p₀ p₁ C γ` — the likelihood-ratio test above;
* `exists_mostPowerful` — existence of `(C, γ)` with size exactly `α`, and optimality;
* `isMostPowerful_of_npShape`, `isMostPowerful_npTest` — sufficiency;
* `npTest_necessity` — necessity of the shape a.e., plus the exact-size clause;
* `power_gt_alpha_of_ne`, `power_eq_alpha_of_eq` — strict unbiasedness, and the honest
  degenerate case.

**Proof formalization notes.**
* The threshold lives in `ℝ≥0∞`: this is what admits the corner value `C = ∞` needed for
  `α = 0`, and it makes the convention "`0 · ∞ = 0`" (used exactly at that corner) the
  ambient `ENNReal` arithmetic rather than a side convention. The comparison is therefore
  `C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x)` rather than a real inequality.
* The classical construction takes `α(c) = P₀{p₁/p₀ > c}`; `1 - α` is a cumulative
  distribution function, so `α(c)` is nonincreasing and right-continuous, and the
  boundary weight is `γ = (α - α(C))/(α(C⁻) - α(C))` whenever the denominator is nonzero.
  The `ℝ≥0∞` formulation avoids forming the ratio `p₁/p₀` at all.
* The necessity statement is transcribed with its escape clause: exact size `α` is forced
  only when no test of size `< α` already has power `1`.
* `HasDensity` is a local convenience predicate for the dominated setup; it is a
  candidate for promotion into the shared test-layer data model.

**Bibliographic comments.** The lemma, the randomized-test formulation, and the
existence/sufficiency/necessity trichotomy are due to J. Neyman and E. S. Pearson ("On
the problem of the most efficient tests of statistical hypotheses," *Phil. Trans. R. Soc.
Lond. A* **231** (1933), 289–337), with the systematic treatment of the boundary
randomization in J. Neyman and E. S. Pearson ("Contributions to the theory of testing
statistical hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37). Measure-theoretic
formulations under an arbitrary dominating measure were given by G. B. Dantzig and
A. Wald ("On the fundamental lemma of Neyman and Pearson," *Ann. Math. Statist.* **22**
(1951), 87–93).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- `P` **has density** `p` with respect to `μ`: `p` is measurable and nonnegative and
`P = p·μ`. This is the dominated setup "`P` possesses the density `p` with respect to
the measure `μ`"; nonnegativity is carried explicitly because densities are real-valued
here, and `ENNReal.ofReal` would otherwise silently truncate. -/
def HasDensity (μ : Measure 𝓧) (p : 𝓧 → ℝ) (P : Measure 𝓧) : Prop :=
  Measurable p ∧ (∀ x, 0 ≤ p x) ∧ P = μ.withDensity fun x => ENNReal.ofReal (p x)

/-- The **Neyman–Pearson (likelihood-ratio) test** with threshold `C : ℝ≥0∞` and boundary
randomization `γ`: reject when `p₁ > C·p₀`, reject with probability `γ` when
`p₁ = C·p₀`, accept when `p₁ < C·p₀`.

The threshold is extended-nonnegative-real so that the corner `C = ∞` (needed for
`α = 0`) is available and `0 · ∞ = 0` is the ambient arithmetic. For `C = 0` the test
rejects wherever `p₁ > 0`. No constraint is imposed on `γ` by the definition: for `γ`
outside `[0,1]` the result is not a critical function, and the theorems below therefore
carry `γ ∈ [0,1]` explicitly. -/
noncomputable def npTest (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (γ : ℝ) : 𝓧 → ℝ := fun x =>
  if C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) then 1
  else if ENNReal.ofReal (p₁ x) = C * ENNReal.ofReal (p₀ x) then γ
  else 0

/-- `φ` **has Neyman–Pearson shape** at threshold `C`: it rejects `μ`-a.e. where
`p₁ > C·p₀` and accepts `μ`-a.e. where `p₁ < C·p₀`, with no constraint on the boundary
set `{p₁ = C·p₀}`. This is the almost-everywhere form of the displayed test above, and
is the shape that most powerful tests are forced to have. -/
def HasNPShape (μ : Measure 𝓧) (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (φ : 𝓧 → ℝ) : Prop :=
  (∀ᵐ x ∂μ, C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) → φ x = 1) ∧
    (∀ᵐ x ∂μ, ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) → φ x = 0)

/-- A density of a probability measure is integrable. -/
private lemma hasDensity_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- The power of a critical function against a density-carrying measure is the integral of the
critical function times the density. -/
private lemma powerAgainst_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (φ : 𝓧 → ℝ) :
    powerAgainst P φ = ∫ x, φ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  unfold powerAgainst
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- Integrability of a critical function times a density. -/
private lemma integrable_crit_mul {μ : Measure 𝓧} {p φ : 𝓧 → ℝ} (hp : Integrable p μ)
    (hφ : IsCriticalFn φ) : Integrable (fun x => φ x * p x) μ :=
  hp.bdd_mul hφ.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2)

/-- **Fundamental inequality, finite threshold.** For a finite threshold `C`, any test of
Neyman–Pearson shape whose `P₀`-size dominates that of a competitor `ψ` dominates it in
`P₁`-power as well. This is the pointwise `(φ − ψ)(p₁ − C·p₀) ≥ 0` argument. -/
private lemma np_fundamental_finite (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {φ ψ : 𝓧 → ℝ}
    (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ C φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  have hp0nn := h₀.2.1
  have hp1nn := h₁.2.1
  set c := C.toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hCeq : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC).symm
  obtain ⟨hsp1, hsp0⟩ := hshape
  -- Pointwise `(φ − ψ)(p₁ − c·p₀) ≥ 0`.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * (p₁ x - c * p₀ x) := by
    filter_upwards [hsp1, hsp0] with x hx1 hx0
    have hp0x := hp0nn x; have hp1x := hp1nn x
    have hφ1 := (hφc.2 x).2; have hψ0 := (hψc.2 x).1; have hψ1 := (hψc.2 x).2
    rcases lt_trichotomy (c * p₀ x) (p₁ x) with hlt | heq | hgt
    · have hpos : 0 < p₁ x := lt_of_le_of_lt (by positivity) hlt
      have hcmp : C * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := by
        rw [hCeq, ← ENNReal.ofReal_mul hc0]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hlt
      rw [hx1 hcmp]
      exact mul_nonneg (by linarith) (by linarith)
    · have hz : p₁ x - c * p₀ x = 0 := by linarith
      simp [hz]
    · have hpos : 0 < c * p₀ x := lt_of_le_of_lt hp1x hgt
      have hcmp : ENNReal.ofReal (p₁ x) < C * ENNReal.ofReal (p₀ x) := by
        rw [hCeq, ← ENNReal.ofReal_mul hc0]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hgt
      rw [hx0 hcmp]
      have hrw : (0 - ψ x) * (p₁ x - c * p₀ x) = ψ x * (c * p₀ x - p₁ x) := by ring
      rw [hrw]
      exact mul_nonneg (by linarith) (by linarith)
  have hnn := integral_nonneg_of_ae hpt
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have hφp0 := integrable_crit_mul hp0i hφc
  have hψp0 := integrable_crit_mul hp0i hψc
  have key : ∫ x, (φ x - ψ x) * (p₁ x - c * p₀ x) ∂μ
      = (powerAgainst P₁ φ - powerAgainst P₁ ψ) - c * (powerAgainst P₀ φ - powerAgainst P₀ ψ) := by
    have hAB : Integrable (fun x => φ x * p₁ x - ψ x * p₁ x) μ := hφp1.sub hψp1
    have hDE : Integrable (fun x => c * (φ x * p₀ x - ψ x * p₀ x)) μ :=
      (hφp0.sub hψp0).const_mul c
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, powerAgainst_eq h₀ φ, powerAgainst_eq h₀ ψ,
      ← integral_sub hφp1 hψp1, ← integral_sub hφp0 hψp0, ← integral_const_mul,
      ← integral_sub hAB hDE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [key] at hnn
  have hc_nonneg : 0 ≤ c * (powerAgainst P₀ φ - powerAgainst P₀ ψ) :=
    mul_nonneg hc0 (by linarith)
  linarith

/-- **Fundamental inequality, infinite threshold** (the `α = 0` corner). A test of
Neyman–Pearson shape at `C = ∞` has `P₀`-size zero; any competitor with size `≤ 0` puts no
mass where `p₀ > 0`, so `φ` dominates it in `P₁`-power. -/
private lemma np_fundamental_top (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {φ ψ : 𝓧 → ℝ} (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ ⊤ φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  have hp0nn := h₀.2.1; have hp1nn := h₁.2.1
  obtain ⟨hsp1, hsp0⟩ := hshape
  have hp0i : Integrable p₀ μ := hasDensity_integrable h₀
  have hp1i : Integrable p₁ μ := hasDensity_integrable h₁
  have hφp0z : (fun x => φ x * p₀ x) =ᵐ[μ] 0 := by
    filter_upwards [hsp0] with x hx0
    show φ x * p₀ x = 0
    rcases eq_or_lt_of_le (hp0nn x) with h | h
    · rw [← h, mul_zero]
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h)]
        exact ENNReal.ofReal_lt_top
      rw [hx0 hc2, zero_mul]
  have hpAφ0 : powerAgainst P₀ φ = 0 := by
    rw [powerAgainst_eq h₀ φ, integral_congr_ae hφp0z]; simp
  have hψp0nn : 0 ≤ᵐ[μ] fun x => ψ x * p₀ x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hψc.2 x).1 (hp0nn x)
  have hψp0i : Integrable (fun x => ψ x * p₀ x) μ := integrable_crit_mul hp0i hψc
  have hψp0z : (fun x => ψ x * p₀ x) =ᵐ[μ] 0 := by
    have hle : ∫ x, ψ x * p₀ x ∂μ ≤ 0 := by
      rw [← powerAgainst_eq h₀ ψ]; rw [hpAφ0] at hsize; exact hsize
    have heq0 : ∫ x, ψ x * p₀ x ∂μ = 0 := le_antisymm hle (integral_nonneg_of_ae hψp0nn)
    exact (integral_eq_zero_iff_of_nonneg_ae hψp0nn hψp0i).mp heq0
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * p₁ x := by
    filter_upwards [hsp1, hsp0, hψp0z] with x hx1 hx0 hxψ0
    show 0 ≤ (φ x - ψ x) * p₁ x
    rcases eq_or_lt_of_le (hp0nn x) with hp0 | hp0
    · rcases eq_or_lt_of_le (hp1nn x) with hp1 | hp1
      · rw [← hp1]; simp
      · have hc1 : (⊤ : ℝ≥0∞) * ENNReal.ofReal (p₀ x) < ENNReal.ofReal (p₁ x) := by
          rw [← hp0, ENNReal.ofReal_zero, mul_zero]
          exact ENNReal.ofReal_pos.mpr hp1
        rw [hx1 hc1]
        exact mul_nonneg (by linarith [(hψc.2 x).2]) (le_of_lt hp1)
    · have hc2 : ENNReal.ofReal (p₁ x) < ⊤ * ENNReal.ofReal (p₀ x) := by
        rw [ENNReal.top_mul (by simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0)]
        exact ENNReal.ofReal_lt_top
      have hψ0 : ψ x = 0 := by
        simp only [Pi.zero_apply] at hxψ0
        rcases mul_eq_zero.mp hxψ0 with h | h
        · exact h
        · exact absurd h (ne_of_gt hp0)
      rw [hx0 hc2, hψ0]; simp
  have hnn := integral_nonneg_of_ae hpt
  have hφp1 := integrable_crit_mul hp1i hφc
  have hψp1 := integrable_crit_mul hp1i hψc
  have key : ∫ x, (φ x - ψ x) * p₁ x ∂μ = powerAgainst P₁ φ - powerAgainst P₁ ψ := by
    rw [powerAgainst_eq h₁ φ, powerAgainst_eq h₁ ψ, ← integral_sub hφp1 hψp1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [key] at hnn
  linarith

/-- The combined fundamental inequality for an arbitrary (possibly infinite) threshold. -/
private lemma np_fundamental (μ : Measure 𝓧) [SigmaFinite μ]
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} (h₀ : HasDensity μ p₀ P₀) (h₁ : HasDensity μ p₁ P₁)
    {C : ℝ≥0∞} {φ ψ : 𝓧 → ℝ}
    (hφc : IsCriticalFn φ) (hψc : IsCriticalFn ψ)
    (hshape : HasNPShape μ p₀ p₁ C φ)
    (hsize : powerAgainst P₀ ψ ≤ powerAgainst P₀ φ) :
    powerAgainst P₁ ψ ≤ powerAgainst P₁ φ := by
  rcases eq_or_ne C ⊤ with hC | hC
  · subst hC; exact np_fundamental_top μ P₀ P₁ h₀ h₁ hφc hψc hshape hsize
  · exact np_fundamental_finite μ P₀ P₁ h₀ h₁ hC hφc hψc hshape hsize

/-- The likelihood-ratio test has (exact, everywhere) Neyman–Pearson shape. -/
private lemma hasNPShape_npTest (μ : Measure 𝓧) (p₀ p₁ : 𝓧 → ℝ) (C : ℝ≥0∞) (γ : ℝ) :
    HasNPShape μ p₀ p₁ C (npTest p₀ p₁ C γ) := by
  refine ⟨Filter.Eventually.of_forall fun x hx => ?_, Filter.Eventually.of_forall fun x hx => ?_⟩
  · show npTest p₀ p₁ C γ x = 1
    unfold npTest; rw [if_pos hx]
  · show npTest p₀ p₁ C γ x = 0
    unfold npTest; rw [if_neg (not_lt.mpr hx.le), if_neg (ne_of_lt hx)]

/-- The likelihood-ratio test with a `[0,1]` boundary weight is a critical function. -/
private lemma isCriticalFn_npTest {p₀ p₁ : 𝓧 → ℝ} (hp0 : Measurable p₀) (hp1 : Measurable p₁)
    {C : ℝ≥0∞} {γ : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsCriticalFn (npTest p₀ p₁ C γ) := by
  refine ⟨?_, fun x => ?_⟩
  · unfold npTest
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
    · exact measurableSet_lt (measurable_const.mul hp0.ennreal_ofReal) hp1.ennreal_ofReal
    · exact measurableSet_eq_fun hp1.ennreal_ofReal (measurable_const.mul hp0.ennreal_ofReal)
  · unfold npTest
    split_ifs
    · exact ⟨zero_le_one, le_refl 1⟩
    · exact hγ
    · exact ⟨le_refl 0, zero_le_one⟩

/-- **Existence (i).** For every level `α ∈ [0,1]` there are a threshold `C` and a
boundary weight `γ ∈ [0,1]` for which the likelihood-ratio test has size **exactly** `α`
and is most powerful at that level. The corner cases `α = 0` and `α = 1` are covered by
the extended threshold (`C = ∞`, resp. `C = 0`). -/
theorem exists_mostPowerful
    -- USER-INPUT: dominating measure, σ-finite (free choice; `μ = P₀ + P₁` always works)
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative, given as probability measures
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    -- USER-INPUT: the two densities, supplied by the caller together with the model
    {p₀ p₁ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the nominal level, a free choice in the closed unit interval
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (C : ℝ≥0∞) (γ : ℝ), γ ∈ Set.Icc (0 : ℝ) 1 ∧
      powerAgainst P₀ (npTest p₀ p₁ C γ) = α ∧
      IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) := by
  -- TODO: the existence construction. The optimality half is `isMostPowerful_npTest`; what
  -- remains is choosing `(C, γ)` with `powerAgainst P₀ (npTest …) = α`, obtained by applying
  -- `exists_critical_constants` to the law under `P₀` of the likelihood ratio
  -- `ofReal (p₁ x) / ofReal (p₀ x)` (pushforward + `p₀ = 0` null-set bookkeeping).
  sorry

/-- **Sufficiency (ii).** Any critical function of Neyman–Pearson shape whose size equals
`α` is most powerful at level `α`. Only the shape and the size enter: the values of `φ`
on the boundary set `{p₁ = C·p₀}` are unconstrained. -/
theorem isMostPowerful_of_npShape
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {C : ℝ≥0∞} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the competitor class is the critical functions, so `φ` must be one
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the test has size exactly `α` — condition (3.7) of the classical form
    (hsize : powerAgainst P₀ φ = α)
    -- USER-INPUT: the test has likelihood-ratio shape at threshold `C` — condition (3.8)
    (hshape : HasNPShape μ p₀ p₁ C φ) :
    IsMostPowerful P₀ P₁ α φ := by
  refine ⟨hφ, hsize.le, fun ψ hψ hψsize => ?_⟩
  refine np_fundamental μ P₀ P₁ h₀ h₁ hφ hψ hshape ?_
  rw [hsize]; exact hψsize

/-- **Sufficiency (ii), specialized.** The likelihood-ratio test itself is most powerful
at its own size, for every threshold `C` and every boundary weight `γ ∈ [0,1]`. -/
theorem isMostPowerful_npTest
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {C : ℝ≥0∞} {γ α : ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: the boundary weight is a probability, so that `npTest` is a test
    (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the threshold/weight pair realizes size exactly `α`
    (hsize : powerAgainst P₀ (npTest p₀ p₁ C γ) = α) :
    IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) :=
  isMostPowerful_of_npShape μ P₀ P₁ h₀ h₁ (isCriticalFn_npTest h₀.1 h₁.1 hγ) hsize
    (hasNPShape_npTest μ p₀ p₁ C γ)

/-- **Necessity (iii).** A most powerful level-`α` test has likelihood-ratio shape almost
everywhere for some threshold `C`; and its size is exactly `α` **unless** there already
exists a test of size strictly below `α` whose power against the alternative is `1`.

Both clauses are transcribed as stated: the shape is only claimed `μ`-a.e. (nothing is
claimed on the boundary set), and the exact-size clause is guarded by its escape
hypothesis rather than asserted unconditionally. -/
theorem npTest_necessity
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: `φ` is most powerful at level `α` — the property being reverse-engineered
    (hφ : IsMostPowerful P₀ P₁ α φ) :
    (∃ C : ℝ≥0∞, HasNPShape μ p₀ p₁ C φ) ∧
      ((¬ ∃ ψ, IsCriticalFn ψ ∧ powerAgainst P₀ ψ < α ∧ powerAgainst P₁ ψ = 1) →
        powerAgainst P₀ φ = α) := by
  -- TODO: necessity/uniqueness. This is the converse of the sufficiency direction proved
  -- above and needs the likelihood-ratio law construction (`exists_mostPowerful`) together
  -- with the a.e. characterization of the boundary; it is the deepest clause of the lemma.
  sorry

/-- **Strict unbiasedness.** For `0 < α < 1` the power of a most powerful level-`α` test
strictly exceeds `α`, unless the null and the alternative are the same distribution. -/
theorem power_gt_alpha_of_ne
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the simple null and simple alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {p₀ p₁ : 𝓧 → ℝ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: `P₀` possesses the density `p₀` with respect to `μ`
    (h₀ : HasDensity μ p₀ P₀)
    -- USER-INPUT: `P₁` possesses the density `p₁` with respect to `μ`
    (h₁ : HasDensity μ p₁ P₁)
    -- USER-INPUT: nondegenerate level; at `α ∈ {0,1}` the conclusion genuinely fails
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: `φ` is most powerful at level `α`
    (hφ : IsMostPowerful P₀ P₁ α φ)
    -- USER-INPUT: the two hypotheses are distinct — the stated exception of the result
    (hne : P₀ ≠ P₁) :
    α < powerAgainst P₁ φ := by
  -- TODO: strict unbiasedness. The `≤` half is immediate from the constant test `ψ ≡ α`;
  -- the strict inequality needs the necessity structure (an MP test attaining power exactly
  -- `α` forces `p₀ = p₁` a.e., contradicting `P₀ ≠ P₁`), i.e. `npTest_necessity`.
  sorry

/-- **The degenerate case, stated honestly.** When the null and the alternative coincide,
every most powerful level-`α` test has power exactly `α`: no test can do better than the
constant test `φ ≡ α`, and the constant test shows `α` is attained. Together with
`power_gt_alpha_of_ne` this settles the power of a most powerful test in both cases. -/
theorem power_eq_alpha_of_eq
    -- USER-INPUT: the common distribution under the null and the alternative
    (P₀ P₁ : Measure 𝓧) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: nondegenerate level
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: `φ` is most powerful at level `α`
    (hφ : IsMostPowerful P₀ P₁ α φ)
    -- USER-INPUT: the excluded case of the previous theorem
    (heq : P₀ = P₁) :
    powerAgainst P₁ φ = α := by
  obtain ⟨hφc, hle, hmax⟩ := hφ
  have hconst : IsCriticalFn (fun _ : 𝓧 => α) := ⟨measurable_const, fun _ => ⟨hα₀.le, hα₁.le⟩⟩
  have hcP0 : powerAgainst P₀ (fun _ : 𝓧 => α) = α := by
    unfold powerAgainst
    rw [integral_const]; simp
  have hcP1 : powerAgainst P₁ (fun _ : 𝓧 => α) = α := by
    unfold powerAgainst
    rw [integral_const]; simp
  have h1 : powerAgainst P₁ (fun _ : 𝓧 => α) ≤ powerAgainst P₁ φ := hmax _ hconst hcP0.le
  rw [hcP1] at h1
  have hp01 : powerAgainst P₁ φ = powerAgainst P₀ φ := by rw [heq]
  linarith [hle]

end StatLean.HypothesisTesting
