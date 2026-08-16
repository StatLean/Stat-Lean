import StatLean.StatisticalModels.GraphicalModels.Core.Separation
import StatLean.StatisticalModels.GraphicalModels.Core.Semigraphoid
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.TFAE

/-!
# The undirected Markov properties — pairwise, local, global

Lauritzen's three Markov properties of a probability law relative to an undirected graph `G`,
stated over an **abstract** conditional-independence relation
`ci : Finset V → Finset V → Finset V → Prop` (read `ci A B C` as `X_A ⫫ X_B ∣ X_C`):

* `IsPairwiseMarkov G ci` — (P): non-adjacent `i`, `j` are independent given everything else;
* `IsLocalMarkov G ci` — (L): a vertex is independent of the rest given its neighbourhood;
* `IsGlobalMarkov G ci` — (G): separated blocks are independent given the separator.

and the hierarchy (Lauritzen **Proposition 3.4**, p. 32): (G) ⇒ (L) ⇒ (P), plus its converse
under (C5) (Lauritzen **Theorem 3.7**, Pearl and Paz, p. 34), stated here as a designated
later lane.

* `separates_neighborFinset`, `separates_sdiff_pair` — the two purely graph-theoretic facts
  that carry (G) ⇒ (L) and (G) ⇒ (P): the neighbourhood of `v` separates `{v}` from the rest,
  and the complement of a non-adjacent pair separates the pair;
* `notMem_neighborFinset_of_not_adj`, `disjoint_singleton_neighborFinset_of_not_adj`,
  `disjoint_closedNeighborhood_sdiff`, `disjoint_pairNeighborhood_sdiff` — the disjointness
  obligations that `IsSemigraphoid`'s axioms and `IsGlobalMarkov` demand of their blocks,
  isolated as named lemmas rather than buried in a proof;
* `sdiff_closedNeighborhood_eq_union_far`, `neighborFinset_union_far_eq_sdiff_pair` — the two
  set identities that make the weak-union instantiation land on the nose;
* `globalMarkov_implies_localMarkov`, `localMarkov_implies_pairwiseMarkov`,
  `globalMarkov_implies_pairwiseMarkov` — Proposition 3.4;
* `pairwiseMarkov_implies_globalMarkov`, `markov_tfae` — Theorem 3.7 (Pearl–Paz), stated only.

**Why an abstract `ci`.** This is the book's own observation. Lauritzen remarks immediately
after Proposition 3.4 (p. 33) that the implications (G) ⇒ (L) ⇒ (P) "only depend on the
properties (C1)–(C4) of conditional independence and hence hold for any semi-graphoid", and
the remark after Theorem 3.7 says the same of that theorem for graphoids. Abstracting
therefore proves the hierarchy **once**, with the discrete-mass relation, the Gaussian
precision relation, and our general `CondIndep` each supplying an instance; see
`notes/factor_graphical/roadmap.md` §3.1.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996: the properties (P), (L), (G) are the **unnumbered** labelled
definitions on p. 32 (there is no "Definition 3.x" to cite); **Proposition 3.4** (p. 32,
with eq. (3.9)) is (G) ⇒ (L) ⇒ (P); condition **(3.10)** (p. 34) is the intersection property
(C5); **Theorem 3.7** (p. 34), credited to Pearl and Paz, is the converse under (3.10). The
justification for the abstract relation is the remark following Proposition 3.4 (p. 33)
(`Lauritzen §3.2` in tags).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Disjointness is carried by `IsGlobalMarkov`, not by its consumers.** Lauritzen states (G)
   "for any triple `(A, B, S)` of **disjoint** subsets of `V`". We put the three `Disjoint`
   hypotheses into the definition, matching the book and matching the amended
   `IsSemigraphoid`, whose axiom fields likewise range over disjoint blocks. This makes (G) a
   *weaker* assertion, hence easier for a model class to supply and harder to consume — and
   both consumers here instantiate it at genuinely disjoint blocks, so nothing is lost:
   `{v}`, `V ∖ cl(v)`, `ne(v)` are pairwise disjoint, and so are `{i}`, `{j}`, `V ∖ {i, j}`.
   (P) and (L) need no such hypothesis: their blocks are disjoint by construction.
2. **(G) ⇒ (P) is proved directly, not through (L).** Lauritzen's Proposition 3.4 routes
   (G) ⇒ (L) ⇒ (P), where the second step needs weak union. But `V ∖ {i, j}` separates `{i}`
   from `{j}` outright when `i` and `j` are non-adjacent (`separates_sdiff_pair`), so
   `globalMarkov_implies_pairwiseMarkov` needs **no** `IsSemigraphoid` hypothesis at all. We
   state it in that hypothesis-free form rather than as the composite, per the project's
   minimal-hypothesis rule; the composite route remains available via
   `localMarkov_implies_pairwiseMarkov ∘ globalMarkov_implies_localMarkov`.
3. **`ne(v)` and `cl(v)` are `Finset`s.** Lauritzen's `bd(α)` (boundary) is `G.neighborFinset
   v` and his `cl(α)` (closure) is `insert v (G.neighborFinset v)`; `V ∖ cl(α)` is
   `Finset.univ \ insert v (G.neighborFinset v)`. This needs `[Fintype V]` and
   `[DecidableRel G.Adj]`; the book works with a finite variable set throughout.
4. **The weak-union instantiation.** (L) ⇒ (P) applies (C3) at `A = {i}`, `B = {j}`,
   `C = ne(i)`, `D = V ∖ ({i, j} ∪ ne(i))`. The four blocks are pairwise disjoint — `i ≠ j`;
   `i ∉ ne(i)` because a `SimpleGraph` is loopless; `j ∉ ne(i)` is *exactly* the non-adjacency
   hypothesis of (P); and `D` excludes all three by construction — and `{j} ∪ D = V ∖ cl(i)`,
   `ne(i) ∪ D = V ∖ {i, j}`. The four obligations are the named lemmas listed above, so the
   set algebra is visible to the proof lane instead of hidden inside one large proof.

**Bibliographic comments.** The three Markov properties and their hierarchy are due to the
Markov-random-field literature of the 1970s (Hammersley–Clifford 1971 unpublished;
J. Besag, "Spatial interaction and the statistical analysis of lattice systems," *J. Roy.
Statist. Soc. Ser. B* **36** (1974), 192–236; F. Speed and H. Kiiveri). The converse under the
intersection property is J. Pearl and A. Paz, "Graphoids: a graph-based logic for reasoning
about relevance relations," in *Advances in Artificial Intelligence II*, North-Holland, 1987,
357–363 — Lauritzen's Theorem 3.7. That (P) alone does **not** imply (G) without (C5) is
Lauritzen's Example 3.10 (pp. 37–38, Moussouris), which our `Discrete/` lane is designed to
be able to express. Mathlib has no Markov-property vocabulary; the whole hierarchy is new
here, but every graph-theoretic ingredient (`neighborFinset`, `Walk`, `ComponentCompl`) is
Mathlib's.
-/

namespace StatLean.StatisticalModels.GraphicalModels

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  (ci : Finset V → Finset V → Finset V → Prop)

/-! ### The three Markov properties -/

/-- **(P) The pairwise Markov property** (Lauritzen p. 32, unnumbered): for every pair of
distinct non-adjacent vertices `i`, `j`, the relation holds for `{i}`, `{j}` conditionally on
all remaining vertices, `V ∖ {i, j}`.

*Edge behaviour.* The condition is vacuous on adjacent pairs and on `i = j`; the blocks
`{i}`, `{j}`, `V ∖ {i, j}` are pairwise disjoint whenever `i ≠ j`, so no disjointness
hypothesis is needed (contrast `IsGlobalMarkov`). Reading `ci A B C` as `X_A ⫫ X_B ∣ X_C`,
this is Lauritzen's `α ⫫ β ∣ V ∖ {α, β}`. -/
def IsPairwiseMarkov : Prop :=
  ∀ i j : V, i ≠ j → ¬ G.Adj i j → ci {i} {j} (Finset.univ \ {i, j})

/-- **(L) The local Markov property** (Lauritzen p. 32, unnumbered): every vertex `v` is
independent of the vertices outside its closure `cl(v) = {v} ∪ ne(v)`, conditionally on its
boundary `bd(v) = ne(v)`.

*Edge behaviour.* At an isolated vertex `ne(v) = ∅` this asserts unconditional independence of
`{v}` from `V ∖ {v}`; at a dominating vertex the "rest" block is empty and the condition is
whatever `ci A ∅ C` means for the instance — nothing here forces it to be trivially true. The
three blocks are pairwise disjoint by construction. -/
def IsLocalMarkov [DecidableRel G.Adj] : Prop :=
  ∀ v : V, ci {v} (Finset.univ \ insert v (G.neighborFinset v)) (G.neighborFinset v)

/-- **(G) The global Markov property** (Lauritzen p. 32, unnumbered): for every triple of
**disjoint** blocks `A`, `B`, `S` with `S` separating `A` from `B` in `G`, the relation holds
for `A`, `B` given `S`.

*Book vs Lean.* Lauritzen quantifies over disjoint triples, and so do we — the three
`Disjoint` hypotheses are part of the definition rather than of its consumers. This matches
the amended `IsSemigraphoid`, whose axiom fields also range over disjoint blocks, and keeps
(G) supplyable by model classes for which overlapping blocks would force degenerate
coordinates. *Edge behaviour.* Vacuously satisfiable content when `A` or `B` is empty is not
automatic: `Separates G S ∅ B` holds (`separates_empty_left`), so (G) demands `ci ∅ B S` of
every instance. -/
def IsGlobalMarkov : Prop :=
  ∀ A B S : Finset V, Disjoint A B → Disjoint A S → Disjoint B S →
    Separates G S A B → ci A B S

/-! ### Graph-side and set-algebra obligations

Everything in this section is graph theory or `Finset` algebra: no `ci` occurs. These are the
lemmas the hierarchy proofs consume, kept named so the obligations stay visible. -/

/-- **The graph fact behind (G) ⇒ (P)**: for distinct non-adjacent `i`, `j`, the complement
`V ∖ {i, j}` separates `{i}` from `{j}`. A walk from `i` to `j` is non-`nil`; its second
vertex differs from `i` (looplessness) and from `j` (non-adjacency), so it lies in
`V ∖ {i, j}`. Stated outside the locally-finite section: no `[DecidableRel G.Adj]` is
involved, so `globalMarkov_implies_pairwiseMarkov` needs none either. -/
theorem separates_sdiff_pair (i j : V)
    -- USER-INPUT: distinctness of the pair; Lauritzen §3.2 (P), p. 32 (at `i = j` the `nil`
    -- walk defeats separation, so the hypothesis is genuinely needed)
    (hij : i ≠ j)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    Separates G (Finset.univ \ {i, j}) {i} {j} := by
  sorry

section GraphSide

variable [DecidableRel G.Adj]

/-- A vertex not adjacent to `i` is not in `i`'s neighbourhood — the `Finset` reading of the
non-adjacency hypothesis of (P). -/
theorem notMem_neighborFinset_of_not_adj (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    j ∉ G.neighborFinset i := by
  simpa using hadj

/-- **First disjointness obligation** of the weak-union instantiation: the block `{j}` is
disjoint from the conditioning block `ne(i)`. This is *precisely* the non-adjacency
hypothesis of (P) — it is the reason (L) ⇒ (P) works only at non-adjacent pairs. -/
theorem disjoint_singleton_neighborFinset_of_not_adj (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32
    (hadj : ¬ G.Adj i j) :
    Disjoint ({j} : Finset V) (G.neighborFinset i) :=
  Finset.disjoint_singleton_left.mpr (notMem_neighborFinset_of_not_adj G i j hadj)

/-- **Second disjointness obligation**: the closure `cl(v) = {v} ∪ ne(v)` is disjoint from its
complement `V ∖ cl(v)`. Supplies the `Disjoint` arguments of `IsGlobalMarkov` at
`A = {v}`, `B = V ∖ cl(v)`, `S = ne(v)` after `Finset.disjoint_of_subset_left/right`. -/
theorem disjoint_closedNeighborhood_sdiff (v : V) :
    Disjoint (insert v (G.neighborFinset v)) (Finset.univ \ insert v (G.neighborFinset v)) :=
  Finset.disjoint_sdiff

/-- **Third disjointness obligation**: the block `{i, j} ∪ ne(i)` is disjoint from the "far"
block `D = V ∖ ({i, j} ∪ ne(i))`. Supplies, after `Finset.disjoint_of_subset_left`, all three
of `Disjoint {i} D`, `Disjoint {j} D` and `Disjoint (ne i) D` in the weak-union
instantiation. -/
theorem disjoint_pairNeighborhood_sdiff (i j : V) :
    Disjoint ({i, j} ∪ G.neighborFinset i)
      (Finset.univ \ ({i, j} ∪ G.neighborFinset i)) :=
  Finset.disjoint_sdiff

/-- **First set identity**: the "rest" block of (L) at `i` splits off `{j}`,
`V ∖ cl(i) = {j} ∪ D` with `D = V ∖ ({i, j} ∪ ne(i))`. This is the shape (C3) consumes: the
union whose second summand is moved into the conditioning set. -/
theorem sdiff_closedNeighborhood_eq_union_far (i j : V)
    -- USER-INPUT: distinctness of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `j ∉ cl(i)` on the `i` side
    (hij : i ≠ j)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `j ∉ ne(i)`
    (hadj : ¬ G.Adj i j) :
    Finset.univ \ insert i (G.neighborFinset i)
      = {j} ∪ (Finset.univ \ ({i, j} ∪ G.neighborFinset i)) := by
  sorry

/-- **Second set identity**: after weak union the conditioning set is `ne(i) ∪ D`, and that is
exactly `V ∖ {i, j}`, the conditioning set (P) asks for. Uses `i ∉ ne(i)` (a `SimpleGraph` is
loopless) and `j ∉ ne(i)` (non-adjacency). -/
theorem neighborFinset_union_far_eq_sdiff_pair (i j : V)
    -- USER-INPUT: the non-adjacency of the pair; Lauritzen §3.2 (P), p. 32 — needed so that
    -- `ne(i) ⊆ V ∖ {i, j}`
    (hadj : ¬ G.Adj i j) :
    G.neighborFinset i ∪ (Finset.univ \ ({i, j} ∪ G.neighborFinset i))
      = Finset.univ \ {i, j} := by
  sorry

/-- **The graph fact behind (G) ⇒ (L)**: the boundary `ne(v)` separates `{v}` from everything
outside the closure `cl(v)`. A walk leaving `v` and ending outside `cl(v)` is non-`nil`, so
its second vertex is a neighbour of `v` lying on it. -/
theorem separates_neighborFinset (v : V) :
    Separates G (G.neighborFinset v) {v} (Finset.univ \ insert v (G.neighborFinset v)) := by
  sorry

end GraphSide

/-! ### Proposition 3.4 — the hierarchy (G) ⇒ (L) ⇒ (P) -/

variable {ci}

/-- **(G) ⇒ (L)** (Lauritzen Proposition 3.4, p. 32). Pure graph separation: instantiate (G)
at `A = {v}`, `B = V ∖ cl(v)`, `S = ne(v)`, whose pairwise disjointness is
`disjoint_closedNeighborhood_sdiff` together with
`SimpleGraph.singleton_disjoint_neighborFinset`, and whose separation is
`separates_neighborFinset`. **No** property of `ci` is used. -/
theorem globalMarkov_implies_localMarkov [DecidableRel G.Adj]
    -- USER-INPUT: the global Markov property of the law; Lauritzen §3.2 (G), p. 32
    (h : IsGlobalMarkov G ci) :
    IsLocalMarkov G ci := by
  sorry

/-- **(L) ⇒ (P)** (Lauritzen Proposition 3.4, p. 32, eq. (3.9)). The one step that needs the
calculus: weak union (C3) applied at `A = {i}`, `B = {j}`, `C = ne(i)`,
`D = V ∖ ({i, j} ∪ ne(i))`, using `sdiff_closedNeighborhood_eq_union_far` to present the
"rest" block of (L) as `{j} ∪ D` and `neighborFinset_union_far_eq_sdiff_pair` to recognise
`ne(i) ∪ D` as `V ∖ {i, j}`. The pairwise disjointness that (C3) demands of its blocks is
supplied by `Finset.disjoint_singleton` (from `i ≠ j`),
`SimpleGraph.singleton_disjoint_neighborFinset` (looplessness),
`disjoint_singleton_neighborFinset_of_not_adj` (non-adjacency) and
`disjoint_pairNeighborhood_sdiff`. -/
theorem localMarkov_implies_pairwiseMarkov [DecidableRel G.Adj]
    -- USER-INPUT: the ambient conditional-independence calculus; Lauritzen §3.1 (C1)–(C4),
    -- p. 29, abstracted per the remark after Proposition 3.4, p. 33
    (hci : IsSemigraphoid ci)
    -- USER-INPUT: the local Markov property of the law; Lauritzen §3.2 (L), p. 32
    (h : IsLocalMarkov G ci) :
    IsPairwiseMarkov G ci := by
  sorry

/-- **(G) ⇒ (P)** (Lauritzen Proposition 3.4, p. 32). Stated **without** any property of `ci`:
`separates_sdiff_pair` gives the separation directly, so the composite route through (L) —
which would need weak union — is unnecessary. See the module docstring, note 2. -/
theorem globalMarkov_implies_pairwiseMarkov
    -- USER-INPUT: the global Markov property of the law; Lauritzen §3.2 (G), p. 32
    (h : IsGlobalMarkov G ci) :
    IsPairwiseMarkov G ci := by
  sorry

/-! ### Theorem 3.7 (Pearl–Paz) — the converse under (C5)

Designated later lane: statements only. The book's proof is a backward induction on
`#(V ∖ (A ∪ B ∪ S))` that repeatedly applies (C5) together with (C1)–(C4); it is the one
place in this file where `IsGraphoid` rather than `IsSemigraphoid` is required, and Lauritzen
remarks (p. 34) that it "applies to any graphoid". -/

/-- **(P) ⇒ (G) under the intersection property** — Lauritzen **Theorem 3.7** (p. 34),
credited to Pearl and Paz; condition (3.10) of the book is exactly `IsGraphoid.intersection`.

*Not proved here.* This is the designated later lane; see the section docstring for the proof
route. Note that the hypothesis is genuinely needed: without (C5) the implication fails, by
Lauritzen's Example 3.10 (Moussouris, pp. 37–38). -/
theorem pairwiseMarkov_implies_globalMarkov
    -- USER-INPUT: the ambient calculus *with* intersection; Lauritzen §3.1 (C5), p. 30, and
    -- condition (3.10), p. 34
    (hci : IsGraphoid ci)
    -- USER-INPUT: the pairwise Markov property of the law; Lauritzen §3.2 (P), p. 32
    (h : IsPairwiseMarkov G ci) :
    IsGlobalMarkov G ci := by
  sorry

/-- **The three Markov properties coincide over a graphoid** — Lauritzen **Theorem 3.7**
(p. 34, Pearl and Paz). Proposition 3.4 gives the forward implications for any semi-graphoid;
`pairwiseMarkov_implies_globalMarkov` closes the cycle under (C5).

*Not proved here* — it is `pairwiseMarkov_implies_globalMarkov` plus the two implications
above, so it carries no debt of its own once that lane lands. -/
theorem markov_tfae [DecidableRel G.Adj]
    -- USER-INPUT: the ambient calculus *with* intersection; Lauritzen §3.1 (C5), p. 30, and
    -- condition (3.10), p. 34
    (hci : IsGraphoid ci) :
    [IsGlobalMarkov G ci, IsLocalMarkov G ci, IsPairwiseMarkov G ci].TFAE := by
  sorry

end StatLean.StatisticalModels.GraphicalModels
