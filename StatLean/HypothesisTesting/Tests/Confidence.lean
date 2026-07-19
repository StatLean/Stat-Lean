import StatLean.HypothesisTesting.Tests.Defs

/-!
# Tests and confidence sets: the duality

Testing a hypothesis for every parameter value at once *is* a confidence statement. If, for
each `θ`, `A θ ⊆ 𝓧` is the acceptance region of a level-`α` test of the simple hypothesis
`H(θ)`, then
$$ S(x) \;=\; \{\theta : x \in A(\theta)\} $$
is a family of confidence sets at confidence level `1 − α`, and conversely every confidence
family arises this way ("test inversion"). Optimality transfers as well: if each `A θ₀` comes
from a test that is uniformly most powerful against the alternatives `K(θ₀)`, then `S`
minimizes the probability of covering each *false* value `θ₀`, uniformly over `θ ∈ K(θ₀)` —
it is **uniformly most accurate**.

This file fixes:

* `confidenceSet A` — the inverted family `S(x) = {θ : x ∈ A θ}`;
* `IsConfidenceFamily P S γ` — coverage at level `γ`, `P_θ{θ ∈ S(X)} ≥ γ` for every `θ`;
* `IsUMAConfidence P K S γ` — uniformly most accurate at level `γ` against `K`;
* `acceptanceTest A` — the nonrandomized test with acceptance region `A`;

and states the two directions of the duality together with the optimality transfer.

**Reference.** Classical confidence-set theory; original sources in the bibliographic comments
below.

**Proof formalization notes.**
* `IsConfidenceFamily` compares in `ℝ≥0∞` (`ENNReal.ofReal γ ≤ P θ {x | θ ∈ S x}`), which
  keeps the definition free of `toReal` side conditions and makes a negative `γ` vacuous
  rather than junk.
* `IsUMAConfidence` quantifies over competitor families whose slices `{x | θ ∈ S' x}` are
  measurable. The restriction is a Lean-side necessity, not a weakening of the classical
  statement: the argument inverts the competitor into a genuine test, and a critical function
  must be measurable. Coverage of a non-measurable family is not a probability statement in
  the first place.
* Tests are the critical functions of the area's data model, so the acceptance region `A`
  enters through the nonrandomized test `acceptanceTest A = 1_{Aᶜ}`; the level condition of
  the book is then `IsLevel P {θ} (acceptanceTest (A θ)) α`, and `power_acceptanceTest`
  converts it into the measure statement `P_θ(A(θ)ᶜ) ≤ α` used in the proofs.
* Only the one-sided framing of the optimality transfer is stated: for each null value `θ₀`
  the competitor class is the tests of `H(θ₀)` against `K(θ₀)`, and the conclusion compares
  false-coverage probabilities at parameter points of `K(θ₀)`. The lower/upper confidence
  *bound* specialization (`S(x)` an interval determined by a monotone family) is a separate
  statement and is not derived here.

**Bibliographic comments.** Confidence sets, the confidence level, and the inversion of tests
are due to J. Neyman ("Outline of a theory of statistical estimation based on the classical
theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380); the accuracy
criterion and its link with the power of the underlying tests appear there and in
J. Neyman and E. S. Pearson's optimality program ("On the problem of the most efficient tests
of statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **inverted family of confidence sets** of a family of acceptance regions:
`S(x) = {θ : x ∈ A θ}`, the parameter values not rejected on observing `x`. -/
def confidenceSet (A : Θ → Set 𝓧) (x : 𝓧) : Set Θ :=
  {θ | x ∈ A θ}

/-- A **family of confidence sets at confidence level `γ`**: the random set `S(X)` covers the
true parameter with probability at least `γ`, whatever the true parameter is. -/
def IsConfidenceFamily (P : Θ → Measure 𝓧) (S : 𝓧 → Set Θ) (γ : ℝ) : Prop :=
  ∀ θ, ENNReal.ofReal γ ≤ P θ {x | θ ∈ S x}

/-- A **uniformly most accurate** family of confidence sets at level `γ` against the
alternatives `K`: it has level `γ`, and for every false value `θ₀` it covers `θ₀` with the
smallest possible probability, uniformly over the parameters `θ ∈ K θ₀` at which `θ₀` is
false, among all level-`γ` competitors (with measurable slices; see the file header). -/
def IsUMAConfidence (P : Θ → Measure 𝓧) (K : Θ → Set Θ) (S : 𝓧 → Set Θ) (γ : ℝ) : Prop :=
  IsConfidenceFamily P S γ ∧
    ∀ S' : 𝓧 → Set Θ, (∀ θ, MeasurableSet {x | θ ∈ S' x}) → IsConfidenceFamily P S' γ →
      ∀ θ₀ : Θ, ∀ θ ∈ K θ₀, P θ {x | θ₀ ∈ S x} ≤ P θ {x | θ₀ ∈ S' x}

/-- The **nonrandomized test with acceptance region `A`**: it rejects exactly off `A`. -/
noncomputable def acceptanceTest (A : Set 𝓧) : 𝓧 → ℝ :=
  Set.indicator Aᶜ (1 : 𝓧 → ℝ)

/-- Test inversion, pointwise: `θ` is in the confidence set at `x` exactly when `x` is accepted
by the test of `H(θ)`. -/
theorem mem_confidenceSet_iff (A : Θ → Set 𝓧) (x : 𝓧) (θ : Θ) :
    θ ∈ confidenceSet A x ↔ x ∈ A θ := by
  sorry

/-- The test with a measurable acceptance region is a critical function. -/
theorem isCriticalFn_acceptanceTest {A : Set 𝓧}
    -- LEAN-ONLY: measurability of the acceptance region; a test must be measurable
    (hA : MeasurableSet A) :
    IsCriticalFn (acceptanceTest A) := by
  sorry

/-- The power of a nonrandomized test is the probability of its rejection region. -/
theorem power_acceptanceTest (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {A : Set 𝓧}
    -- LEAN-ONLY: measurability of the acceptance region; needed to integrate the indicator
    (hA : MeasurableSet A) (θ : Θ) :
    power P (acceptanceTest A) θ = (P θ Aᶜ).toReal := by
  sorry

/-- **Test inversion produces confidence sets**: inverting a family of level-`α` tests gives a
family of confidence sets at confidence level `1 − α`. -/
theorem isConfidenceFamily_of_acceptance (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {A : Θ → Set 𝓧} {α : ℝ}
    -- USER-INPUT: a nonnegative significance level; classical
    (hα : 0 ≤ α)
    -- LEAN-ONLY: measurability of the acceptance regions; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: each `A θ` accepts `H(θ)` with a level-`α` test; Neyman (1937)
    (hlevel : ∀ θ, IsLevel P {θ} (acceptanceTest (A θ)) α) :
    IsConfidenceFamily P (confidenceSet A) (1 - α) := by
  sorry

/-- **Confidence sets produce tests** (the converse inversion): the slices of a confidence
family at level `γ` are acceptance regions of level-`(1 − γ)` tests. -/
theorem isLevel_acceptanceTest_of_isConfidenceFamily (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {S : 𝓧 → Set Θ} {γ : ℝ}
    -- USER-INPUT: a confidence level in `[0,1]`; classical
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    -- LEAN-ONLY: measurability of the slices; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet {x : 𝓧 | θ ∈ S x})
    -- USER-INPUT: the family has confidence level `γ`; Neyman (1937)
    (hS : IsConfidenceFamily P S γ) (θ : Θ) :
    IsLevel P {θ} (acceptanceTest {x : 𝓧 | θ ∈ S x}) (1 - γ) := by
  sorry

/-- **Optimality transfers along the duality**: inverting a family of uniformly most powerful
level-`α` tests — that of `H(θ₀)` against `K(θ₀)`, for each `θ₀` — gives a uniformly most
accurate family of confidence sets at level `1 − α`. -/
theorem isUMA_of_UMP (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {A : Θ → Set 𝓧} {K : Θ → Set Θ} {α : ℝ}
    -- USER-INPUT: a significance level in `[0,1]`; classical
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    -- LEAN-ONLY: measurability of the acceptance regions; a test must be measurable
    (hmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: for each null value, the test of `H(θ₀)` against `K(θ₀)` is UMP at level
    -- `α`; Neyman–Pearson (1933)
    (hUMP : ∀ θ₀ : Θ, IsUMP P {θ₀} (K θ₀) α (acceptanceTest (A θ₀))) :
    IsUMAConfidence P K (confidenceSet A) (1 - α) := by
  sorry

end StatLean.HypothesisTesting
