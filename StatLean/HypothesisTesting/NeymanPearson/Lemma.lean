import StatLean.HypothesisTesting.Tests.Defs
import Mathlib.MeasureTheory.Measure.WithDensity

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
  sorry

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
    IsMostPowerful P₀ P₁ α (npTest p₀ p₁ C γ) := by
  sorry

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
  sorry

end StatLean.HypothesisTesting
