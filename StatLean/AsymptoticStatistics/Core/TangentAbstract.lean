import StatLean.AsymptoticStatistics.Core.Hilbert
import StatLean.AsymptoticStatistics.Core.QMDPath

/-!
# Tangent set and tangent space (abstract Hilbert version)

vdV §25.3. The unlabeled definitions following Lemma 25.14 introduce a *tangent
set* at `P` as a subset of `L²₀(P)`, and the *tangent space* as its closed
linear span. We separate the two: `TangentSpec P` bundles the set of score
directions; `tangentSpace T` is the derived closed-linear-span submodule.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.TangentAbstract

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *tangent specification* at a probability measure `P`: a set of score
functions in `↥(L2ZeroMean P)`, each realized as the score of a
quadratic-mean-differentiable submodel passing through `P`.

vdV §25.3 (paragraph after Lemma 25.14): a tangent set is, by definition, just a
subset of `L²₀(P)`. Closure under scaling, addition, or convex combinations is a
regularity property, not part of the definition: vdV §25.3 considers tangent
cones (one-sided submodels) where additive closure fails, so those properties do
not live as fields here. -/
structure TangentSpec (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.3: the set of admissible score directions at `P`. -/
  carrier : Set ↥(L2ZeroMean P)
  /-- vdV §25.3.1: every `g ∈ carrier` is the score of a
  quadratic-mean-differentiable submodel `t ↦ Pₜ` at `t = 0`. Per vdV's
  definition "we obtain a collection of score functions, which we call a
  tangent set", membership IS witnessed by a realizing path.

  Carrier-scoped (not `tangentSpace`-scoped): vdV asserts the realizing
  path only for carrier elements; the L²-closure `tangentSpace T_set`
  may contain limits not realized by any QMD path. -/
  submodelOf : ∀ g ∈ carrier, ∃ γ : AsymptoticStatistics.Core.QMDPath.QMDPath P,
    γ.score = g

/-- The *tangent space* at `P` associated to a tangent specification `T`: the
closed linear span of `T.carrier` inside `↥(L2ZeroMean P)`.

Reference: vdV §25.3 — "the closed linear span of the tangent set".

Edge behavior: when `T.carrier = ∅`, `Submodule.span ℝ ∅ = ⊥`, and the
topological closure of `⊥` (the singleton at `0`) is `⊥`. So a vacuous tangent
set yields the trivial tangent space, matching the book's convention that
"no admissible directions" means "no nontrivial tangent space". -/
noncomputable def tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P) :
    Submodule ℝ ↥(L2ZeroMean P) :=
  (Submodule.span ℝ T.carrier).topologicalClosure

/-- The *algebraic* span of the tangent set's carrier is contained in the tangent
space (its L²-closed linear span). vdV §25.3.2's regularity hypothesis quantifies
score directions over the algebraic span `Submodule.span ℝ T.carrier` ("for every
`g ∈ lin g_p`", p.366), while the efficient influence function and pathwise
differentiability live over the closure `tangentSpace T`. This coercion lifts
span-membership to closure-membership where the latter is needed. -/
theorem span_carrier_le_tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P) :
    Submodule.span ℝ T.carrier ≤ tangentSpace T :=
  (Submodule.span ℝ T.carrier).le_topologicalClosure

/-- Every element of the tangent space (the L²-closed linear span) is the
L²(P)-limit of a sequence drawn from the *algebraic* span `Submodule.span ℝ
T.carrier`. This is the sequential characterization of closure membership in the
first-countable (metric) space `↥(L2ZeroMean P)`. It is the analytic core of
vdV's argument that the efficient influence function — which lies in the closed
span — can be approximated arbitrarily well by its projections onto finite
algebraic spans of tangent-set elements (vdV §25.3.2, p.366). -/
theorem exists_seq_span_tendsto_of_mem_tangentSpace
    {P : Measure Ω} [IsProbabilityMeasure P] (T : TangentSpec P)
    {g : ↥(L2ZeroMean P)} (hg : g ∈ tangentSpace T) :
    ∃ a : ℕ → ↥(L2ZeroMean P),
      (∀ n, a n ∈ Submodule.span ℝ T.carrier) ∧
      Filter.Tendsto a Filter.atTop (nhds g) := by
  have hg' : g ∈ closure (↑(Submodule.span ℝ T.carrier) : Set ↥(L2ZeroMean P)) := hg
  exact mem_closure_iff_seq_limit.mp hg'

end AsymptoticStatistics.Core.TangentAbstract
