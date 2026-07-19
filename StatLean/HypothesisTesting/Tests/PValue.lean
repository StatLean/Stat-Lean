import StatLean.HypothesisTesting.Tests.Defs
import StatLean.MultipleTesting.PValues.Defs

/-!
# p-values from nested rejection regions

A family of rejection regions `R : ℝ → Set 𝓧` is **nested** when `R α ⊆ R α'` for `α ≤ α'`:
rejecting at a smaller significance level is a stronger verdict. For such a family the
**p-value** of an observation is the smallest level at which the hypothesis is rejected,
$$ \hat p(x) \;=\; \inf\{\alpha : x \in R_\alpha\}, $$
and the fundamental property is that a p-value built from *valid* regions is itself valid: if
each `R α` has null probability at most `α`, then `P_θ{\hat p ≤ u} ≤ u` for every null `θ` —
`\hat p` is **super-uniform**, the standing null assumption of the multiple-testing area.

The converse direction is recorded too: the test that rejects when `\hat p ≤ α` is a level-`α`
test.

**Reference.** Classical p-value theory; original sources in the bibliographic comments below.

**Proof formalization notes.**
* `nestedPValue` is the literal infimum, with the usual `Real.sInf` junk conventions (empty or
  unbounded-below set ↦ `0`). Both junk corners are genuinely dangerous here — an `x` that no
  region ever rejects would get p-value `0` and destroy super-uniformity (take `R ≡ ∅`) — so
  the two non-degeneracy hypotheses `hR_neg` ("no rejection at a negative level", which makes
  the set bounded below) and `hR_exh` ("every point is rejected at some level below one",
  which makes it nonempty) appear explicitly wherever the value of `nestedPValue` is used.
  They are properties of a genuine family of rejection regions, not regularity fat.
* Measurability of the regions is *not* assumed for super-uniformity: the argument only
  compares the measures of nested sets, `P_θ{\hat p ≤ u} ≤ P_θ(R v)` for `v > u`, and
  monotonicity of a measure needs no measurability. It reappears exactly where an integral is
  formed, as the measurability of the rejection event in `isLevel_pValueTest`.
* Super-uniformity is stated through the multiple-testing area's `SuperUniform` predicate, so
  that p-values produced here feed the FDR/FWER results unchanged. For `t > 1` the bound is
  trivial (probability measures), so the content is the range `0 ≤ t ≤ 1` of the classical
  statement.
* Only the inequality direction is formalized here. Under exact validity of the regions
  (`P_θ(R α) = α`) the same argument returns the exact-uniform conclusion; that strengthening
  is left to the consumer that needs it.

**Bibliographic comments.** Significance levels attained by the data go back to R. A. Fisher
(*Statistical Methods for Research Workers*, Oliver & Boyd, 1925); the systematic treatment of
the p-value as a random variable, and of its null distribution, is due to R. R. Bahadur
("Stochastic comparison of tests," *Ann. Math. Statist.* **31** (1960), 276–295). The validity
condition itself is folklore with no single seminal source. The underlying family of rejection
regions is the Neyman–Pearson construction ("On the problem of the most efficient tests of
statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (SuperUniform)

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **p-value of a nested family of rejection regions**: the smallest significance level at
which `x` is rejected, `p̂(x) = inf {α : x ∈ R α}`.

Junk conventions (`Real.sInf`): if no level rejects `x` the value is `0`, and so is the value
when the set of rejecting levels is unbounded below. Both corners are excluded by the
hypotheses `hR_exh` and `hR_neg` of the theorems below. -/
noncomputable def nestedPValue (R : ℝ → Set 𝓧) (x : 𝓧) : ℝ :=
  sInf {α : ℝ | x ∈ R α}

/-- The p-value is nonnegative as soon as no negative level rejects. -/
theorem nestedPValue_nonneg {R : ℝ → Set 𝓧}
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    (x : 𝓧) :
    0 ≤ nestedPValue R x := by
  sorry

/-- The p-value is at most one as soon as every point is rejected at some level below one. -/
theorem nestedPValue_le_one {R : ℝ → Set 𝓧}
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    -- USER-INPUT: every observation is rejected at some level below one; classical
    (hR_exh : ∀ x : 𝓧, ∃ α < 1, x ∈ R α)
    (x : 𝓧) :
    nestedPValue R x ≤ 1 := by
  sorry

/-- **Validity of the p-value of a nested family of valid rejection regions**: if the regions
are nested and each has null probability at most its level, the induced p-value is
super-uniform under every null distribution. -/
theorem superUniform_nestedPValue (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (Θ₀ : Set Θ) {R : ℝ → Set 𝓧}
    -- USER-INPUT: the rejection regions are nested in the significance level; classical
    (hmono : Monotone R)
    -- USER-INPUT: no rejection at a negative significance level; classical
    (hR_neg : ∀ α : ℝ, α < 0 → R α = ∅)
    -- USER-INPUT: every observation is rejected at some level below one; classical
    (hR_exh : ∀ x : 𝓧, ∃ α < 1, x ∈ R α)
    -- USER-INPUT: each region is valid at its own level, uniformly over the null; classical
    (hvalid : ∀ α : ℝ, 0 < α → α < 1 → ∀ θ ∈ Θ₀, P θ (R α) ≤ ENNReal.ofReal α) :
    ∀ θ ∈ Θ₀, SuperUniform (nestedPValue R) (P θ) := by
  sorry

/-- **The p-value test has level `α`**: rejecting when the p-value is at most `α` is a
level-`α` test, for any super-uniform p-value. -/
theorem isLevel_pValueTest (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (Θ₀ : Set Θ) (R : ℝ → Set 𝓧) {α : ℝ}
    -- USER-INPUT: a nonnegative significance level; classical
    (hα : 0 ≤ α)
    -- LEAN-ONLY: measurability of the rejection event; needed to integrate its indicator
    (hmeas : MeasurableSet {x : 𝓧 | nestedPValue R x ≤ α})
    -- USER-INPUT: the p-value is valid under every null distribution; classical
    (hsu : ∀ θ ∈ Θ₀, SuperUniform (nestedPValue R) (P θ)) :
    IsLevel P Θ₀ (Set.indicator {x : 𝓧 | nestedPValue R x ≤ α} (1 : 𝓧 → ℝ)) α := by
  sorry

end StatLean.HypothesisTesting
