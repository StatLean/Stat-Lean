import StatLean.HypothesisTesting.Invariance.Defs
import StatLean.HypothesisTesting.Tests.Confidence

/-!
# Equivariant confidence sets and uniformly most accurate equivariance

The duality between tests and confidence sets — `θ ∈ S(x)` exactly when `x ∈ A(θ)` — is
independent of what the parameter is: real, vector-valued, or a label for an unknown
distribution. This file carries the invariance reduction across that duality.

A group acting on the data induces an action on the parameter space and hence on *sets* of
parameters, `g^*S = {ḡθ : θ ∈ S}`. A confidence family is **equivariant** when
`g^*S(x) = S(g·x)`: re-expressing the data in transformed coordinates transforms the
confidence statement in the matching way, so the statement does not depend on the
coordinate system. (The older name "invariant" is misleading — the sets do move.)

The dictionary is exact. A confidence family is equivariant precisely when its dual
acceptance-region family is equivariant, `A(ḡθ) = g·A(θ)`. Specializing to group elements
that *fix* `θ` — the transformations under which the hypothesis `θ' = θ` is itself
invariant — an equivariant confidence family has acceptance regions invariant under each
stabilizer. The optimality transfer follows: if for every `θ` the acceptance region is the
UMP invariant test of `θ' = θ` at level `α`, then every competing equivariant confidence
family at level `1 − α` yields invariant tests that are no more powerful, hence covers
every false parameter value at least as often. The original family is therefore uniformly
most accurate among equivariant families.

**Main results.**
* `IsEquivariantConfidence`, `IsUMAEquivariant` — equivariance and uniform accuracy;
* `isEquivariantConfidence_iff_acceptance_equivariant` — the dictionary, both directions;
* `acceptance_invariant_of_equivariantConfidence` — equivariant confidence sets have
  stabilizer-invariant acceptance regions;
* `isUMAEquivariant_of_isUMPInvariant` — UMP invariant acceptance regions give uniformly
  most accurate equivariant confidence sets.

**Dependency note (stub gate).** `confidenceSet` and `IsConfidenceFamily` are the names
fixed by the sibling `Tests/Confidence.lean` (work item `ht/test-foundations`), which
carries the test–confidence-set duality. This file is written against those names and
**must be re-checked against that file's final signatures at the stub gate**; only the
arity/argument order can differ, not the content used here.

**Proof formalization notes.**
* The induced action on parameter sets is the image `(g • ·) '' S`, so equivariance reads
  `(g • ·) '' S x = S (g • x)`.
* The source's group `G_θ` is *any* group of transformations leaving the hypothesis
  `θ' = θ` invariant; the only property its proof uses is `ḡθ = θ`. The statements below
  are therefore given for the **stabilizer** of `θ`, which is the largest such group — so
  they specialize to every `G_θ` the source allows.
* Part (i) of the source's lemma follows from the dictionary; the dictionary itself is the
  honest two-directional statement, since stabilizer-invariance of the acceptance regions
  alone is *not* enough to recover equivariance of the confidence family (full
  equivariance `A(ḡθ) = g·A(θ)` is).
* Acceptance regions enter the optimality statement through the nonrandomized test
  rejecting off `A θ`, i.e. the indicator of `(A θ)ᶜ`.
* Uniform accuracy is stated as the source defines it: minimizing the probability of
  covering each *false* value `θ' ≠ θ`.

**Bibliographic comments.** The duality between families of tests and confidence sets is
due to J. Neyman ("Outline of a theory of statistical estimation based on the classical
theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380). Equivariance of
confidence sets and the transfer of invariance optimality across the duality belong to the
invariance program of G. A. Hunt and C. Stein ("Most stringent tests of statistical
hypotheses," unpublished manuscript, 1946) and C. Stein ("Some problems in multivariate
analysis, Part I," Technical Report 6, Department of Statistics, Stanford University,
1956), as developed in E. L. Lehmann's lecture tradition of the 1950s; the relation
between invariance and sufficiency in this setting is treated by W. J. Hall,
R. A. Wijsman and J. K. Ghosh ("The relationship between sufficiency and invariance with
applications in sequential analysis," *Ann. Math. Statist.* **36** (1965), 575–614).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **Equivariant confidence family**: applying the induced parameter action to the
confidence set computed from `x` gives the confidence set computed from `g·x`. -/
def IsEquivariantConfidence (G : Type*) [Group G] [MulAction G 𝓧] [MulAction G Θ]
    (S : 𝓧 → Set Θ) : Prop :=
  ∀ (g : G) (x : 𝓧), (fun θ => g • θ) '' S x = S (g • x)

/-- **Uniformly most accurate equivariant** at confidence level `lvl`: an equivariant
confidence family at that level which, among all such families, minimizes the probability
of covering every false parameter value. -/
def IsUMAEquivariant (G : Type*) [Group G] [MulAction G 𝓧] [MulAction G Θ]
    (P : Θ → Measure 𝓧) (lvl : ℝ) (S : 𝓧 → Set Θ) : Prop :=
  IsEquivariantConfidence G S ∧ IsConfidenceFamily P S lvl ∧
    ∀ S' : 𝓧 → Set Θ, IsEquivariantConfidence G S' → IsConfidenceFamily P S' lvl →
      ∀ (θ θ' : Θ), θ' ≠ θ → P θ {x | θ' ∈ S x} ≤ P θ {x | θ' ∈ S' x}

/-- **The dictionary between equivariant confidence sets and equivariant acceptance
regions.** A confidence family obtained by dualizing a family of acceptance regions is
equivariant exactly when the acceptance regions themselves are equivariant. -/
theorem isEquivariantConfidence_iff_acceptance_equivariant {A : Θ → Set 𝓧} :
    IsEquivariantConfidence G (confidenceSet A) ↔
      ∀ (g : G) (θ : Θ), A (g • θ) = (fun x => g • x) '' A θ := by
  sorry

/-- **Equivariant confidence sets have stabilizer-invariant acceptance regions** (part (i)
of the source's lemma). For each parameter value, the acceptance region of the hypothesis
`θ' = θ` is invariant under every transformation fixing `θ`. -/
theorem acceptance_invariant_of_equivariantConfidence {S : 𝓧 → Set Θ}
    -- USER-INPUT: the confidence family is equivariant
    (hS : IsEquivariantConfidence G S)
    (θ : Θ) {g : G}
    -- USER-INPUT: `g` fixes `θ`, i.e. it belongs to a group leaving the hypothesis
    -- `θ' = θ` invariant
    (hg : g • θ = θ) :
    (fun x => g • x) '' {x | θ ∈ S x} = {x | θ ∈ S x} := by
  sorry

/-- **UMP invariant acceptance regions give uniformly most accurate equivariant confidence
sets** (part (ii) of the source's lemma). If the dual confidence family is equivariant and
has confidence level `1 − α`, and if for each parameter value the acceptance region is UMP
among tests invariant under the stabilizer, then the confidence family is uniformly most
accurate among equivariant families at that level. -/
theorem isUMAEquivariant_of_isUMPInvariant {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {A : Θ → Set 𝓧} {α : ℝ}
    -- USER-INPUT: the dual confidence family is equivariant
    (hS : IsEquivariantConfidence G (confidenceSet A))
    -- USER-INPUT: the dual confidence family has confidence level `1 − α`
    (hlvl : IsConfidenceFamily P (confidenceSet A) (1 - α))
    -- LEAN-ONLY: measurability of the acceptance regions, needed to read them as tests
    (hAmeas : ∀ θ, MeasurableSet (A θ))
    -- USER-INPUT: for each `θ` the acceptance region is the UMP level-`α` test of
    -- `θ' = θ` among tests invariant under the stabilizer of `θ`
    (hUMP : ∀ θ : Θ, IsUMPInvariant ↥(MulAction.stabilizer G θ) P {θ} {θ' | θ' ≠ θ} α
      ((A θ)ᶜ.indicator fun _ => (1 : ℝ))) :
    IsUMAEquivariant G P (1 - α) (confidenceSet A) := by
  sorry

end StatLean.HypothesisTesting
