import StatLean.StatisticalModels.GraphicalModels.Core.CondIndep
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Coordinate subvectors — conditional independence between blocks of variables

A graphical model is a statement about a random vector `X : Ω → V → α` indexed by the vertex
set `V`: the blocks `X_A`, `X_B`, `X_C` for finite vertex sets `A`, `B`, `C`. This file fixes
the subvector operation and specialises `CondIndep` to it, so that everything downstream
(separation, the Markov properties, the discrete and Gaussian characterisations) speaks a
single vocabulary.

* `coords A X` — the subvector `X_A = (X_v)_{v ∈ A}`, a random element of `A → α`;
* `measurable_coords` — a subvector of a measurable vector is measurable
  (`Finset.measurable_restrict`);
* `coords_apply`, `restrict₂_comp_coords` — the two rewriting facts the later files need:
  a coordinate of a subvector is a coordinate, and restricting a bigger subvector to a smaller
  index set gives the smaller subvector;
* `CondIndepCoords μ X A B C` — `X_A ⫫ X_B ∣ X_C`;
* `CondIndepCoords.symm` / `CondIndepCoords.decomposition` — the two graphoid properties that
  are structural at this level, inherited from `CondIndep.symm` / `CondIndep.comp`.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996, §3.1, pp. 28–30 — conditional independence between blocks of a
random vector, and the properties (C1)–(C2) used here (`Lauritzen §3.1`).

**Proof formalization notes.** *Book vs Lean:* Lauritzen writes `X_A` for the restriction of a
vector indexed by a finite vertex set; the Lean carrier is `Finset.restrict`, whose value type
`↥A → α` is indexed by the coercion of the `Finset` to a subtype. Consequently the *type* of
`X_A` depends on `A`, and set-level manipulations (`A ⊆ B`, `A ∪ B`) become explicit transport
maps `Finset.restrict₂` rather than silent equalities — this is why `restrict₂_comp_coords` is
load-bearing and why decomposition at this level is an instance of `CondIndep.comp` rather
than a rewriting step.

The index type `V` is *not* assumed finite here: only the three blocks are finite sets, so the
vocabulary also covers infinite graphs. Finiteness of `V` enters only where the complement
`Finset.univ \ A` is formed (the Markov properties).

**Bibliographic comments.** The block notation `X_A` and the reading of a graphical model as a
family of conditional independence statements between blocks is Lauritzen's throughout;
the names for the properties (C1)–(C5) are J. Pearl's, *Probabilistic Reasoning in Intelligent
Systems*, Morgan Kaufmann, 1988.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α Ω : Type*}

/-- The **subvector** `X_A = (X_v)_{v ∈ A}` of the random vector `X` on the coordinates in `A`
(Lauritzen §3.1). Edge behaviour: for `A = ∅` the value type `↥(∅ : Finset V) → α` is a
singleton, so `coords ∅ X` is the (a.s. constant) trivial variable — conditioning on it is
conditioning on nothing, which is what the `∅`-conditioning corollaries in
`Core.Semigraphoid` rely on. -/
def coords (A : Finset V) (X : Ω → V → α) : Ω → (A → α) := fun ω => A.restrict (X ω)

@[simp]
theorem coords_apply (A : Finset V) (X : Ω → V → α) (ω : Ω) (i : A) :
    coords A X ω i = X ω i := rfl

/-- Restricting the subvector on `B` to the smaller index set `A` gives the subvector on `A`.
This is the transport map that makes the graphoid *decomposition* property available at the
coordinate level. -/
theorem restrict₂_comp_coords {A B : Finset V}
    -- USER-INPUT: the smaller index block; Lauritzen §3.1
    (hAB : A ⊆ B) (X : Ω → V → α) :
    (fun ω => Finset.restrict₂ (π := fun _ => α) hAB (coords B X ω)) = coords A X := rfl

section Measurability

variable [MeasurableSpace α] [MeasurableSpace Ω]

/-- A subvector of a measurable random vector is measurable. -/
theorem measurable_coords (A : Finset V) {X : Ω → V → α}
    -- LEAN-ONLY: measurability of the ambient random vector (product σ-algebra on `V → α`);
    -- Lauritzen works with random variables, for which this is part of the definition
    (hX : Measurable X) :
    Measurable (coords A X) :=
  (Finset.measurable_restrict (X := fun _ => α) A).comp hX

end Measurability

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → V → α}
  {A B C D : Finset V}

/-- **Conditional independence between coordinate blocks**: `X_A ⫫ X_B ∣ X_C`
(Lauritzen §3.1, p. 28). Edge behaviour: with `C = ∅` this is unconditional independence of
the two blocks in the sense of `CondIndep` with a degenerate conditioning variable (see
`CondIndep.const_right`); with `A = ∅` or `B = ∅` it holds for every law. -/
def CondIndepCoords (μ : Measure Ω) (X : Ω → V → α) (A B C : Finset V) : Prop :=
  CondIndep μ (coords A X) (coords B X) (coords C X)

/-- **(C1), symmetry** at the coordinate level (Lauritzen p. 29). -/
theorem CondIndepCoords.symm
    -- USER-INPUT: the block conditional independence to be reversed; Lauritzen §3.1 (C1)
    (hci : CondIndepCoords μ X A B C) :
    CondIndepCoords μ X B A C :=
  CondIndep.symm hci

/-- **(C2), decomposition** at the coordinate level (Lauritzen p. 29): dropping variables from
the second block preserves conditional independence. An instance of `CondIndep.comp` with the
transport map `Finset.restrict₂`. -/
theorem CondIndepCoords.decomposition
    -- USER-INPUT: the block to be kept is part of the block that is independent;
    -- Lauritzen §3.1 (C2)
    (hBD : B ⊆ D)
    -- USER-INPUT: the block conditional independence to be weakened; Lauritzen §3.1 (C2)
    (hci : CondIndepCoords μ X A D C) :
    CondIndepCoords μ X A B C := by
  sorry

end StatLean.StatisticalModels.GraphicalModels
