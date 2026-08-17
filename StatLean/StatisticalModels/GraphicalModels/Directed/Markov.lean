import StatLean.StatisticalModels.GraphicalModels.Directed.Factorization
import Mathlib.Data.List.TFAE

/-!
# The directed Markov properties — pairwise, local, global

Lauritzen's three Markov properties of a probability law relative to a **directed acyclic**
graph `D` (pp. 47, 50), stated — exactly as in `Undirected/Markov.lean` — over an **abstract**
conditional-independence relation `ci : Finset V → Finset V → Finset V → Prop`, read
`ci A B C` as `X_A ⫫ X_B ∣ X_C`:

* `IsDirectedPairwiseMarkov D ci` — **(DP)**, p. 50: `α ⫫ β ∣ nd(α) ∖ {β}` for non-adjacent
  `α`, `β` with `β ∈ nd(α)`;
* `IsDirectedLocalMarkov D ci` — **(DL)**, p. 50: `α ⫫ nd(α) ∖ pa(α) ∣ pa(α)`, "any variable is
  conditionally independent of its non-descendants, given its parents";
* `IsDirectedGlobalMarkov D ci` — **(DG)**, Lauritzen **Corollary 3.23**, p. 47: `A ⫫ B ∣ S`
  whenever `S` separates `A` from `B` in `(𝒢_{An(A ∪ B ∪ S)})^m`, the moral graph of the
  smallest ancestral set containing `A ∪ B ∪ S`. Stated by *consuming* `Separates`,
  `DAG.ancestralClosure` and the moralization of the induced sub-DAG (`inducedMoralGraph`);
  nothing is re-spelled.

and the results:

* **`recursivelyFactorizes_implies_directedGlobalMarkov`** — Lauritzen **Corollary 3.23**, p. 47,
  for the discrete instance: (DF) ⇒ (DG). This is the theorem the whole design exists to make
  cheap; it is *four* citations of existing work glued together — Proposition 3.22, Lemma 3.21,
  the round-1 undirected (F) ⇒ (G) (`factorizesOver_implies_globalMarkov`, Proposition 3.8), and
  a marginalisation transfer;
* `directedGlobalMarkov_implies_directedLocalMarkov` — (DG) ⇒ (DL), the middle implication of
  Theorem 3.27's proof (p. 51), pure graph theory: no property of `ci` is used;
* `directedLocalMarkov_implies_directedPairwiseMarkov` — (DL) ⇒ (DP), p. 50 ("As
  `pa(α) ⊆ nd(α)`, it follows from properties (C2) and (C3)…"), one application of weak union;
* `directedPairwiseMarkov_implies_directedLocalMarkov_of_nonempty` — the converse **under the
  intersection property** (Lauritzen p. 52: "If the probability distribution `P` satisfies
  (3.10), for example if the density is positive, then … (DP) implies (DL)"), i.e. our
  `IsGraphoid`. Restricted to vertices with `nd(v) ∖ pa(v) ≠ ∅`, for the reason given below;
* `blockMarginal_blockMarginal_of_subset`, `condIndepMass_of_condIndepMass_blockMarginal` — the
  marginalisation transfer that carries a conditional independence proved *for the marginal on
  an ancestral set* back to the law itself;
* **`directedMarkov_tfae`** — Lauritzen **Theorem 3.27**, p. 51: (DF) ⟺ (DG) ⟺ (DL) for a
  discrete probability mass function, here with positivity (see note 4 below).

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**, §3.2.2: **Corollary 3.23** (p. 47) defines the *directed
global Markov property* (DG); **(DP)** and **(DL)** are the two unnumbered displays on p. 50, the
latter with the remark that (DL) ⇒ (DP) follows from (C2) and (C3); **Example 3.26** (p. 51)
shows that the converse fails in general; **Theorem 3.27** (p. 51) is (DF) ⟺ (DG) ⟺ (DL) for a
distribution with a density with respect to a product measure, followed by the remark that (DL)
and (DG) are equivalent even without a density (Lauritzen *et al.* 1990) and by the remark
(p. 52) that under condition (3.10) — in particular for a positive density — (DP) implies (DL)
and all directed Markov properties are equivalent (`Lauritzen §3.2.2` in tags).

**Proof formalization notes.** *Book vs Lean, five deliberate differences.*

1. **Disjointness is carried by `IsDirectedGlobalMarkov`.** Corollary 3.23 states (DG) without
   naming the disjointness convention, but Proposition 3.25 — the d-separation reading of the
   very same property, two pages later — opens with "Let `A`, `B` and `S` be **disjoint** subsets
   of a directed acyclic graph". We follow round 1's `IsGlobalMarkov` and put the three
   `Disjoint` hypotheses in the definition. (DP) and (DL) need no such hypothesis: their blocks
   are disjoint by construction, `v ∉ nd(v)` and `pa(v) ⊆ nd(v)`.
2. **(DL) conditions on `nd(v) ∖ pa(v)`, not on `nd(v)`.** Lauritzen writes `α ⫫ nd(α) ∣ pa(α)`,
   with `pa(α) ⊆ nd(α)` occurring on both sides — harmless in prose, but our `IsSemigraphoid`
   ranges over *disjoint* blocks, as does the book's own (C1)–(C5). The proof of Theorem 3.27
   (p. 51) writes the same property as `pa(α)` separating `{α}` from `nd(α) ∖ pa(α)`, which is
   the form taken here.
3. **(DP)'s "non-adjacent" is `β ∉ pa(α)`.** The book asks for a pair `(α, β)` of *non-adjacent*
   vertices with `β ∈ nd(α)`. Given `β ∈ nd(α)` there can be no arrow `α → β` (that would make
   `β` a descendant), so non-adjacency reduces to the absence of `β → α`, i.e. to
   `β ∉ pa(α)`. `IsDirectedPairwiseMarkov` therefore quantifies over `β ∈ nd(v) ∖ pa(v)` — the
   same set of pairs, spelled with `DAG.parents` alone.
4. **Theorem 3.27 carries a positivity hypothesis the book does not.** Lauritzen assumes only
   that `P` has a density with respect to a product measure — automatic here, counting measure
   being the dominating measure — and his (DL) ⇒ (DF) step *chooses* a conditional density,
   which on the null set `{p_{pa(α)} = 0}` is arbitrary. Formalising that choice means adding a
   junk-value convention (e.g. uniform) to the kernel construction and then re-proving that the
   product is unchanged. `hpos` removes the null set instead. It is a **strictly stronger
   hypothesis than the book's**; dropping it is a designated follow-up, not a gap in the
   mathematics. Positivity is *also* what makes `CondIndepMass p` a graphoid
   (`isGraphoid_condIndepMass_of_pos`, Lauritzen Proposition 3.1), which is what
   `directedPairwiseMarkov_implies_directedLocalMarkov_of_pos` needs.
5. **A normalisation hypothesis is not optional.** (DG) and (DL) are statements about
   `CondIndepMass p`, which is homogeneous of degree two and therefore invariant under rescaling
   `p`; (DF) is not (`sum_eq_one_of_recursivelyFactorizes`). A TFAE without `∑ x, p x = 1` would
   be **false**, refuted by `2 • p` for any recursively factorizing `p`. Finiteness of `p` is
   *not* listed separately: it follows from the normalisation.

**Where the empty-block regime bites, exactly as in round 1.** `IsDirectedGlobalMarkov` demands
`ci ∅ ∅ ∅` of every instance (`separates_empty_left`), while (DP) and (DL) assert nothing at
empty blocks and every semi-graphoid axiom is a `ci → ci` implication. So for an **abstract**
`ci` neither "(DP) ⇒ (DL) at a vertex with `nd(v) = pa(v)`" nor "(DL) ⇒ (DG)" can hold in full
generality — the everywhere-false relation is a graphoid satisfying (DP) and (DL) vacuously
(take `V` empty, or any DAG in which every vertex has `nd(v) = pa(v)`) and failing (DG). This is
the same obstruction that `Undirected/Markov.not_forall_pairwiseMarkov_implies_globalMarkov`
records, and it is why `directedPairwiseMarkov_implies_directedLocalMarkov_of_nonempty` carries
a nonemptiness side condition. It costs nothing at the discrete instance: `CondIndepMass p`
*does* hold at empty blocks, by pure algebra, which is why
`directedPairwiseMarkov_implies_directedLocalMarkov_of_pos` and `directedMarkov_tfae` are stated
without any restriction. A machine-checked counterexample in the style of round 1 is **not**
recorded here because it needs a concrete `DAG` term, i.e. the constructor of a structure owned
by the concurrent `Directed/DAG.lean`; see the closing section.

**Reuse (binding).** From `Directed/DAG.lean`: `DAG`, `DAG.parents`, `DAG.nonDescendants`,
`DAG.AncestralSet`, `DAG.ancestralClosure`. From `Directed/Moralization.lean`: `DAG.moralGraph`
and the induced sub-DAG, via `inducedMoralGraph`. From `Core/Separation.lean`: `Separates` and
its whole monotonicity API — separation is never re-spelled. From `Core/Semigraphoid.lean`:
`IsSemigraphoid.weakUnion` and `IsGraphoid.intersection`. From `Discrete/CondIndep.lean`:
`CondIndepMass`, `blockMarginal`, `isSemigraphoid_condIndepMass`,
`isGraphoid_condIndepMass_of_pos`. From `Discrete/Factorization.lean`:
`factorizesOver_implies_globalMarkov` — the undirected (F) ⇒ (G), never re-proved. From
`Directed/Factorization.lean`: (DF), Lemma 3.21 and Proposition 3.22.

**Bibliographic comments.** The directed Markov properties and their equivalence are due to
H. Kiiveri, T. P. Speed and J. B. Carlin (1984), J. Pearl and T. Verma (1987), T. Verma and
J. Pearl (1990), J. Q. Smith (1989), D. Geiger and J. Pearl (1990), and S. L. Lauritzen,
A. P. Dawid, B. N. Larsen and H.-G. Leimer, "Independence properties of directed Markov fields,"
*Networks* **20** (1990), 491–505 — the last being the source of the density-free (DL) ⟺ (DG)
that Lauritzen records after Theorem 3.27. Pearl's d-separation reading of (DG) is Lauritzen's
Proposition 3.25 (p. 48) and is *not* formalized here. Mathlib has no directed-Markov
vocabulary.
-/

open SimpleGraph
open scoped ENNReal

namespace StatLean.StatisticalModels.GraphicalModels

section Abstract

variable {V : Type*} [Fintype V] [DecidableEq V] (D : DAG V)
  (ci : Finset V → Finset V → Finset V → Prop)

/-! ### The three directed Markov properties -/

/-- **(DP) The directed pairwise Markov property** (Lauritzen p. 50, unnumbered): for every
vertex `v` and every non-adjacent `β ∈ nd(v)`,
`X_v ⫫ X_β ∣ X_{nd(v) ∖ {β}}`.

*Book vs Lean.* The book's "non-adjacent pair `(α, β)` with `β ∈ nd(α)`" is exactly
`β ∈ nd(v) ∖ pa(v)`: membership of `nd(v)` already forbids the arrow `v → β`, so the only
adjacency left to forbid is `β → v`, i.e. `β ∈ pa(v)`. See module docstring, note 3.

*Edge behaviour.* Vacuous at a vertex with `nd(v) = pa(v)` (in particular at a vertex whose
non-descendants are all parents, and at every vertex of a DAG on a one-element vertex set). The
three blocks `{v}`, `{β}`, `nd(v) ∖ {β}` are pairwise disjoint by construction, since
`v ∉ nd(v)`. -/
def IsDirectedPairwiseMarkov : Prop :=
  ∀ v : V, ∀ β ∈ D.nonDescendants v \ D.parents v,
    ci {v} {β} (D.nonDescendants v \ {β})

/-- **(DL) The directed local Markov property** (Lauritzen p. 50, unnumbered): "any variable is
conditionally independent of its non-descendants, given its parents",
`X_v ⫫ X_{nd(v) ∖ pa(v)} ∣ X_{pa(v)}`.

*Book vs Lean.* Lauritzen writes `α ⫫ nd(α) ∣ pa(α)` with `pa(α) ⊆ nd(α)` on both sides; the
disjoint spelling used here is the one his own proof of Theorem 3.27 uses ("`pa(α)` obviously
separates `{α}` from `nd(α) ∖ pa(α)`"). See module docstring, note 2.

*Edge behaviour.* At a source vertex (`pa(v) = ∅`) this asserts unconditional independence of
`X_v` from all its non-descendants; at a vertex with `nd(v) = pa(v)` the middle block is empty
and the assertion is whatever `ci A ∅ C` means for the instance — nothing here forces it to be
trivially true, which is precisely the empty-block regime discussed in the module docstring. -/
def IsDirectedLocalMarkov : Prop :=
  ∀ v : V, ci {v} (D.nonDescendants v \ D.parents v) (D.parents v)

/-- **Lauritzen's `(𝒢_{An(T)})^m`** (Corollary 3.23, p. 47): moralize the sub-DAG induced on the
smallest ancestral set containing `T`. A one-line composite of `DAG.ancestralClosure` with
`inducedMoralGraph`, so that (DG) reads as the book does and so that the two concurrent
definitions are consumed at a single site. -/
abbrev ancestralMoralGraph (T : Finset V) : SimpleGraph V :=
  inducedMoralGraph D (D.ancestralClosure T)

/-- **(DG) The directed global Markov property** — Lauritzen **Corollary 3.23**, p. 47: for
disjoint blocks `A`, `B`, `S`,
`X_A ⫫ X_B ∣ X_S` whenever `S` separates `A` from `B` in `(𝒢_{An(A ∪ B ∪ S)})^m`.

*Book vs Lean.* The disjointness is Proposition 3.25's, not Corollary 3.23's, but it is the
book's standing convention for triples and it matches round 1's `IsGlobalMarkov`; see module
docstring, note 1. Separation is `Core/Separation.Separates` verbatim, the ancestral closure and
the moralization are the concurrent `Directed/` definitions — nothing is re-spelled here.

*Edge behaviour.* `Separates G S ∅ B` holds (`separates_empty_left`), so (DG) demands `ci ∅ B S`
of every instance; for the discrete relation `CondIndepMass p` that is free (both sides of the
identity coincide), for an abstract `ci` it is a real demand. This is the same asymmetry round 1
records under `IsGlobalMarkov`. -/
def IsDirectedGlobalMarkov : Prop :=
  ∀ A B S : Finset V, Disjoint A B → Disjoint A S → Disjoint B S →
    Separates (ancestralMoralGraph D (A ∪ B ∪ S)) S A B → ci A B S

/-! ### The directed hierarchy -/

variable {ci}

/-- **(DG) ⇒ (DL)** — the middle implication of Lauritzen's proof of **Theorem 3.27** (p. 51):
"(DG) implies (DL) follows by observing that `{α} ∪ nd(α)` is an ancestral set and that `pa(α)`
obviously separates `{α}` from `nd(α) ∖ pa(α)` in `(𝒢_{{α} ∪ nd(α)})^m`."

**No property of `ci` is used** — this is pure graph theory, exactly as round 1's
`globalMarkov_implies_localMarkov`. Two facts carry it. First, `{v} ∪ nd(v)` is ancestral (a
parent of a non-descendant is a non-descendant, else its child would be a descendant), so it is
its own ancestral closure and `{v} ∪ (nd(v) ∖ pa(v)) ∪ pa(v) = {v} ∪ nd(v)` — here
`pa(v) ⊆ nd(v)` is used. Second, in the moral graph of the sub-DAG induced on `{v} ∪ nd(v)` the
neighbourhood of `v` is exactly `pa(v)`: `v` has no child in the set (children are descendants),
hence also no co-parent marriage there, so every walk leaving `v` leaves through a parent. -/
theorem directedGlobalMarkov_implies_directedLocalMarkov
    -- USER-INPUT: the directed global Markov property of the law; Lauritzen Corollary 3.23, p. 47
    (h : IsDirectedGlobalMarkov D ci) :
    IsDirectedLocalMarkov D ci := by
  sorry

/-- **(DL) ⇒ (DP)** — Lauritzen p. 50: "As `pa(α) ⊆ nd(α)`, it follows from properties (C2) and
(C3) of conditional independence that the directed local Markov property (DL) implies the
pairwise (DP)."

One application of **weak union** (C3) at `A = {v}`, `B = {β}`, `E = nd(v) ∖ pa(v) ∖ {β}`,
`C = pa(v)` (the axiom's four blocks are `A`, `B`, `E`, `C`; `E` is its `D`, renamed to avoid the
DAG): the premise `ci {v} (B ∪ E) C` is (DL) since `B ∪ E = nd(v) ∖ pa(v)` (using
`β ∈ nd(v) ∖ pa(v)`), and the conclusion's conditioning set `C ∪ E` is `nd(v) ∖ {β}` (using
`pa(v) ⊆ nd(v)`). The six disjointness obligations of `IsSemigraphoid.weakUnion` are free:
`v ∉ nd(v)` gives the three involving `{v}`, `β ∉ pa(v)` and the `sdiff` give the rest.
Decomposition (C2), which the book also names, is absorbed into the same step. -/
theorem directedLocalMarkov_implies_directedPairwiseMarkov
    -- USER-INPUT: the ambient conditional-independence calculus; Lauritzen §3.1 (C1)–(C4),
    -- p. 29, abstracted per the remark after Proposition 3.4, p. 33
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the directed local Markov property of the law; Lauritzen §3.2.2 (DL), p. 50
    (h : IsDirectedLocalMarkov D ci) :
    IsDirectedPairwiseMarkov D ci := by
  sorry

/-- **(DP) ⇒ (DL) under the intersection property, at the vertices where (DP) says anything** —
Lauritzen p. 52: "If the probability distribution `P` satisfies (3.10), for example if the
density is positive, then it is not difficult to see that (DP) implies (DL)". Condition (3.10) is
`IsGraphoid.intersection`, exactly as in round 1's Theorem 3.7.

**Proof.** Fix `v` and write `N = nd(v)`, `P = pa(v)`, `R = N ∖ P`. Induct on nonempty `B ⊆ R`,
claiming `ci {v} B (N ∖ B)`; the base case `B = {β}` is (DP) verbatim, and the step from `B` to
`B ∪ {β}` is (C5) at `A = {v}`, `B`, `E = {β}`, `C = N ∖ (B ∪ {β})` (the axiom's fourth block,
renamed from `D` to avoid the DAG), whose two premises are the
inductive hypothesis (`C ∪ E = N ∖ B`) and (DP) at `β` (`C ∪ B = N ∖ {β}`). At `B = R` the
conditioning set is `N ∖ R = P`, since `P ⊆ N`. All blocks in every application are pairwise
disjoint by construction.

**Why the nonemptiness side condition.** At a vertex with `nd(v) = pa(v)` the middle block of
(DL) is empty, (DP) is vacuous there, and no semi-graphoid axiom can manufacture a first
`ci`-statement out of nothing — the same empty-block obstruction that
`Undirected/Markov.not_forall_pairwiseMarkov_implies_globalMarkov` refutes by machine. It costs
nothing at the discrete instance, where the missing statement holds by algebra; see
`directedPairwiseMarkov_implies_directedLocalMarkov_of_pos`. -/
theorem directedPairwiseMarkov_implies_directedLocalMarkov_of_nonempty
    -- USER-INPUT: the ambient calculus *with* intersection; Lauritzen §3.1 (C5), p. 30, and
    -- condition (3.10), p. 34, invoked for the directed case on p. 52
    (hci : IsGraphoid ci)
    -- USER-INPUT: the directed pairwise Markov property of the law; Lauritzen §3.2.2 (DP), p. 50
    (h : IsDirectedPairwiseMarkov D ci) :
    ∀ v : V, (D.nonDescendants v \ D.parents v).Nonempty →
      ci {v} (D.nonDescendants v \ D.parents v) (D.parents v) := by
  sorry

/-- **(DG) ⇒ (DP)** — the composite of the two implications above, recorded because it is the
directed analogue of round 1's `globalMarkov_implies_pairwiseMarkov`. Unlike that one it does
need the calculus: there is no direct separation argument, because the conditioning set of (DP)
is `nd(v) ∖ {β}` rather than a neighbourhood. -/
theorem directedGlobalMarkov_implies_directedPairwiseMarkov
    -- USER-INPUT: the ambient conditional-independence calculus; Lauritzen §3.1 (C1)–(C4), p. 29
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the directed global Markov property; Lauritzen Corollary 3.23, p. 47
    (h : IsDirectedGlobalMarkov D ci) :
    IsDirectedPairwiseMarkov D ci :=
  directedLocalMarkov_implies_directedPairwiseMarkov D hci
    (directedGlobalMarkov_implies_directedLocalMarkov D h)

end Abstract

/-! ### Marginalisation transfer

Corollary 3.23 proves a conditional independence *for the marginal on an ancestral set* and then
asserts it for the law itself. The two statements are not literally the same object, so the
passage is a lemma. It belongs with the mass algebra of `Discrete/CondIndep.lean`; it is stated
here only because that file is outside this batch's touch-set. -/

section Discrete

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

/-- **Marginalising twice rescales.** For `E ⊆ T`, the marginal on `E` of the marginal on `T` is
the marginal on `E` of `p`, multiplied by the number of configurations of the discarded
coordinates.

The factor is genuine, not a normalisation artefact: `blockMarginal T p` is constant in the
coordinates outside `T`, so summing it over `V ∖ E` counts each configuration of `V ∖ T` once
per configuration of `V ∖ T`, i.e. `#α ^ #(V ∖ T)` times. Because Lauritzen's identity (3.2) is
homogeneous of degree two on both sides, the factor cancels — which is the content of
`condIndepMass_of_condIndepMass_blockMarginal`. -/
theorem blockMarginal_blockMarginal_of_subset (p : (V → α) → ℝ≥0∞) {E T : Finset V}
    -- USER-INPUT: the inner block is contained in the outer one; without it the fibres below are
    -- not a partition and the identity is false
    (hET : E ⊆ T) (x : V → α) :
    blockMarginal E (blockMarginal T p) x
      = (Fintype.card α : ℝ≥0∞) ^ (Finset.univ \ T).card * blockMarginal E p x := by
  sorry

/-- **Conditional independence passes from a marginal to the law**, provided the three blocks are
contained in the marginalised block. This is the step Lauritzen leaves implicit in Corollary 3.23
("`A ⫫ B ∣ S`", asserted of `P` after being proved of `P_{An(A ∪ B ∪ S)}`).

Route: `blockMarginal_blockMarginal_of_subset` rescales all four marginals in the identity (3.2)
by the *same* factor `c = #α ^ #(V ∖ T)`, so both sides acquire `c²`; cancel it.

*No hypothesis on `α` is needed, although `c = 0` looks possible.* `c` vanishes only if `α` is
empty and `T ≠ Finset.univ`; but if `α` is empty and `V` is not, then `V → α` is empty and
`CondIndepMass p A B S` is vacuously true, while if `V` is empty then `T = Finset.univ = ∅` and
`c = 1`. Both branches are discharged inside the proof. -/
theorem condIndepMass_of_condIndepMass_blockMarginal {p : (V → α) → ℝ≥0∞} {A B S T : Finset V}
    -- USER-INPUT: all three blocks live inside the marginalised block; in Corollary 3.23 this is
    -- `A ∪ B ∪ S ⊆ An(A ∪ B ∪ S)`
    (hsub : A ∪ B ∪ S ⊆ T)
    -- USER-INPUT: the conditional independence established for the marginal
    (h : CondIndepMass (blockMarginal T p) A B S) :
    CondIndepMass p A B S := by
  sorry

/-! ### Corollary 3.23 — (DF) ⇒ (DG) -/

/-- **Lauritzen Corollary 3.23**, p. 47: a mass function that factorizes recursively according to
`D` obeys the **directed global Markov property**.

This is the headline of the directed lane, and it is assembled entirely from results that already
exist — the design's whole point:

1. `blockMarginal_recursivelyFactorizesOn_of_ancestralSet` (**Proposition 3.22**) — the marginal
   on `T = An(A ∪ B ∪ S)` factorizes recursively over the sub-DAG induced on `T`;
2. `recursivelyFactorizesOn_implies_factorizesOver_inducedMoralGraph` (**Lemma 3.21**) — hence
   it factorizes, in the undirected sense (F), over `(𝒢_T)^m`;
3. `factorizesOver_implies_globalMarkov` (round 1, **Proposition 3.8**) — hence it is globally
   Markov with respect to `(𝒢_T)^m`, which applied to the given separation yields
   `X_A ⫫ X_B ∣ X_S` **for the marginal**;
4. `condIndepMass_of_condIndepMass_blockMarginal` — hence for `p` itself, since
   `A ∪ B ∪ S ⊆ T`.

Steps 1 and 2 need `T` to be ancestral, which is what `DAG.ancestralClosure` delivers, and step 3
needs the three `Disjoint` hypotheses, which `IsDirectedGlobalMarkov` carries. No finiteness and
no positivity: every step is division-free.

*No decidability in the signature.* Steps 2 and 3 mention `FactorizesOver`, which carries
`[DecidableRel G.Adj]`, but neither the hypothesis nor the conclusion of this theorem does — so
the instance is supplied **classically inside the proof** (`classical`), exactly as
`Core/Separation.separates_iff_forall_path` does for `DecidableEq V`. The statement is unchanged;
any two `Decidable` instances agree by `Subsingleton.elim`. -/
theorem recursivelyFactorizes_implies_directedGlobalMarkov (D : DAG V) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    IsDirectedGlobalMarkov D (CondIndepMass p) := by
  sorry

/-- **(DF) ⇒ (DL)** — Corollary 3.23 composed with (DG) ⇒ (DL). -/
theorem recursivelyFactorizes_implies_directedLocalMarkov (D : DAG V) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    IsDirectedLocalMarkov D (CondIndepMass p) :=
  directedGlobalMarkov_implies_directedLocalMarkov D
    (recursivelyFactorizes_implies_directedGlobalMarkov D p hp)

/-- **(DF) ⇒ (DP)** — Corollary 3.23 composed with the hierarchy. The semi-graphoid input is
`isSemigraphoid_condIndepMass`, whose finiteness hypothesis is supplied by
`ne_top_of_recursivelyFactorizes`: a recursively factorizing mass has total mass `1`, hence is
bounded by `1`. -/
theorem recursivelyFactorizes_implies_directedPairwiseMarkov
    -- LEAN-ONLY: a nonempty state space, needed only to know that a recursively factorizing mass
    -- is finite; see `sum_eq_one_of_recursivelyFactorizes`
    [Nonempty α] (D : DAG V) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (DF); Lauritzen §3.2.2, p. 46
    (hp : RecursivelyFactorizes D p) :
    IsDirectedPairwiseMarkov D (CondIndepMass p) :=
  directedLocalMarkov_implies_directedPairwiseMarkov D
    (isSemigraphoid_condIndepMass (ne_top_of_recursivelyFactorizes D p hp))
    (recursivelyFactorizes_implies_directedLocalMarkov D p hp)

/-- **(DP) ⇒ (DL) for a positive discrete law** — Lauritzen p. 52, the directed reading of
condition (3.10). The two ingredients are `isGraphoid_condIndepMass_of_pos` (Lauritzen
Proposition 3.1: a strictly positive mass function satisfies (C5)) and
`directedPairwiseMarkov_implies_directedLocalMarkov_of_nonempty`.

Unlike the abstract version, this one is stated **without** a nonemptiness side condition: at a
vertex with `nd(v) = pa(v)` the required statement is `CondIndepMass p {v} ∅ (pa v)`, which is
the identity `p_{{v} ∪ pa(v)} · p_{pa(v)} = p_{{v} ∪ pa(v)} · p_{pa(v)}` — true by
`Finset.union_empty` and `Finset.empty_union`, with no hypothesis at all. That is the concrete
sense in which the empty-block gap of the abstract theory is an artefact of abstraction. -/
theorem directedPairwiseMarkov_implies_directedLocalMarkov_of_pos (D : DAG V)
    (p : (V → α) → ℝ≥0∞)
    -- LEAN-ONLY: finiteness of the mass function; the `ℝ≥0∞` counterpart of "`f` is a density",
    -- consumed by the graphoid calculus
    (hp : ∀ x, p x ≠ ∞)
    -- USER-INPUT: strict positivity; Lauritzen Proposition 3.1, p. 29, invoked for the directed
    -- case on p. 52 ("for example if the density is positive")
    (hpos : ∀ x, p x ≠ 0)
    -- USER-INPUT: the directed pairwise Markov property; Lauritzen §3.2.2 (DP), p. 50
    (h : IsDirectedPairwiseMarkov D (CondIndepMass p)) :
    IsDirectedLocalMarkov D (CondIndepMass p) := by
  sorry

/-! ### Theorem 3.27 -/

/-- **Lauritzen Theorem 3.27**, p. 51: for a discrete probability mass function the three
directed Markov properties **(DF)**, **(DG)** and **(DL)** are equivalent.

* 1 ⇒ 2 is `recursivelyFactorizes_implies_directedGlobalMarkov` (Corollary 3.23);
* 2 ⇒ 3 is `directedGlobalMarkov_implies_directedLocalMarkov` (pure graph theory);
* 3 ⇒ 1 is the book's induction on `#V`: take a terminal vertex `v₀`, let `k^{v₀}` be the
  conditional mass of `X_{v₀}` given the rest — which by (DL) depends on `x_{pa(v₀)}` only, since
  the predecessors of `v₀` in any topological order lie in `nd(v₀)` and (C2) discards
  `nd(v₀) ∖ pa(v₀)` — and apply the inductive hypothesis to the marginal on `V ∖ {v₀}`, which is
  again locally Markov. Concretely the kernels are
  `k_v = blockMarginal ({v} ∪ pa(v)) p / blockMarginal (pa(v)) p`, normalised by `hpos` and
  telescoping to `p` by `hnorm`.

*Hypotheses versus the book.* Lauritzen assumes only that `P` has a density with respect to a
product measure, which in the discrete setting is automatic. We assume in addition that `p` is
**normalised** (without which the statement is false — (DG) and (DL) are scale-invariant and
(DF) is not; see module docstring, note 5) and **strictly positive** (which replaces the book's
free choice of a conditional density on a null set; see note 4). Pointwise finiteness is *not*
assumed: it follows from `hnorm`.

*What is not in the list.* (DP) belongs in it as soon as positivity is available — Lauritzen
p. 52 — and that fourth implication is
`directedPairwiseMarkov_implies_directedLocalMarkov_of_pos`, kept separate because it is a
different citation. -/
theorem directedMarkov_tfae (D : DAG V) (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: `p` is a probability mass function; Lauritzen Theorem 3.27, p. 51 ("for a
    -- probability distribution `P` … which has density with respect to a product measure `μ`")
    (hnorm : ∑ x : V → α, p x = 1)
    -- USER-INPUT: strict positivity. **Not** a hypothesis of Theorem 3.27; it stands in for the
    -- book's free choice of a conditional density on the null set `{p_{pa(v)} = 0}` in the
    -- (DL) ⇒ (DF) step. See module docstring, note 4
    (hpos : ∀ x, p x ≠ 0) :
    [RecursivelyFactorizes D p,
      IsDirectedGlobalMarkov D (CondIndepMass p),
      IsDirectedLocalMarkov D (CondIndepMass p)].TFAE := by
  sorry

end Discrete

/-! ### Two remarks of the book that are deliberately *not* theorems here

**(i) Example 3.26** (Lauritzen p. 51) — **(DP) does not imply (DL) in general.** Take
`V = {X, Y, Z, W}` with the three arrows `W → X`, `W → Y`, `W → Z` (Fig. 3.7), binary state
spaces, and the law in which `X = Y = Z` and `W` is independent of `X`, with
`P{X = 1} = P{X = 0} = P{W = 1} = P{W = 0} = 1/2`. Then:

* (DP) **holds**. The pairs to check are the non-adjacent ones with the second vertex a
  non-descendant of the first: `(X, Y)`, `(X, Z)`, `(Y, X)`, `(Y, Z)`, `(Z, X)`, `(Z, Y)`. Each
  asks, e.g. for `(X, Y)`, that `X ⫫ Y ∣ {W, Z}` — and conditionally on `Z` both `X` and `Y` are
  degenerate, so it holds. `W` has no non-descendants, so it contributes nothing.
* (DL) **fails**, at `X`: it would say `X ⫫ (Y, Z) ∣ W`, and `X = Y`.
* Consequently, by Theorem 3.27, this law admits **no** recursive factorization according to the
  graph — which is Lauritzen's own closing remark on the example.

It is **not formalized**, and not because it is hard: writing it down requires a concrete `DAG`
term, i.e. the constructor of the structure owned by the concurrent `Directed/DAG.lean`, whose
field names are not this file's to guess. Faking it — asserting the refutation without the
witness — is forbidden. Once `Directed/DAG.lean` lands, this is a cheap, self-contained addition
in the style of round 1's `not_forall_pairwiseMarkov_implies_globalMarkov`, and it is the honest
counterexample justifying the `IsGraphoid` hypothesis of
`directedPairwiseMarkov_implies_directedLocalMarkov_of_nonempty`.

**(ii) The density-free (DL) ⟺ (DG)** (Lauritzen p. 51, closing remark, crediting Lauritzen,
Dawid, Larsen and Leimer 1990). Theorem 3.27 above obtains (DL) ⇒ (DG) by routing through (DF)
and therefore inherits `hnorm` and `hpos`; the book records that the equivalence in fact holds
for *any* probability distribution.

That remark is not stated here as a theorem, for two independent reasons. First, in the abstract
`ci` formulation it is **false as literally written**: `IsDirectedGlobalMarkov` demands `ci ∅ ∅ ∅`
and (DL) never produces a statement about empty blocks, so the everywhere-false relation is a
graphoid satisfying (DL) and failing (DG) — the exact obstruction round 1 machine-checks in
`not_forall_pairwiseMarkov_implies_globalMarkov`. Second, the repaired nonempty-block version is
a claim about probability measures whose standard proof (LDLL 1990) goes through the *ordered*
local Markov property and a well-ordering compatible with the DAG; whether it holds for an
arbitrary semi-graphoid is a separate question that this batch has not verified, and freezing an
unverified statement is worse than leaving the lane open. It is a designated follow-up. -/

end StatLean.StatisticalModels.GraphicalModels
