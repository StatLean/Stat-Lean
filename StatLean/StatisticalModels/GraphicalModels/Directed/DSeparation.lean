import StatLean.StatisticalModels.GraphicalModels.Core.Separation
import StatLean.StatisticalModels.GraphicalModels.Directed.DAG
import StatLean.StatisticalModels.GraphicalModels.Directed.Moralization
import StatLean.StatisticalModels.GraphicalModels.Directed.Markov
import Mathlib.Logic.Relation

/-!
# d-separation — Pearl's criterion, and its equivalence with moral-graph separation

Lauritzen's *chain* criterion for reading conditional independence off a directed acyclic
graph (p. 48, an **unnumbered** definition), together with the theorem that makes the whole
undirected layer of this area available to the directed theory: d-separation in `G` is
*exactly* separation in the moral graph of the smallest ancestral set containing the three
blocks (**Proposition 3.25**, p. 48).

* `ArrowDir`, `IsCollider` — the orientation vocabulary. `ArrowDir` records how one arrow of a
  chain sits relative to a vertex it is incident to (`into` / `outOf`); `Option ArrowDir` adds
  `none` for "there is no arrow on that side", which happens exactly at the two ends of the
  chain. `IsCollider din dout` is Lauritzen's "arrows of the chain **meet head-to-head**": both
  incident arrows point into the vertex. Endpoints are never colliders
  (`not_isCollider_none_left`, `not_isCollider_none_right`);
* `Chain` — a chain from `u` to `w`: a sequence of vertices in which consecutive vertices are
  joined by an arrow **in either direction**, the direction of each step being recorded by the
  constructor used (`fwd` / `bwd`). See *"Book vs Lean"* note 1 below for why this rather than
  a walk in the underlying undirected graph. `Chain.support`, `Chain.reverse` mirror
  `SimpleGraph.Walk`;
* `NoDescendantIn`, `BlocksAt` — the two clauses of Lauritzen's blocking rule at a single
  vertex occurrence: a **non-collider** blocks when it lies in `S`; a **collider** blocks when
  neither it nor any of its descendants lies in `S`;
* `Chain.BlockedFrom`, `Chain.Blocked`, `Chain.Active` — blocking of a whole chain, defined by
  structural recursion that carries the direction of the incoming arrow along;
* `DSeparated r S A B` — every chain from a vertex of `A` to a vertex of `B` is blocked by `S`;
* `dSeparated_symm`, `dSeparated_mono_left` / `_right`, `dSeparated_empty_left` / `_right`,
  `dSeparated_self_left` / `_right` — the API mirroring `Core.Separation`. **There is no
  monotonicity in the separator**: enlarging `S` can *unblock* a collider, and
  `not_forall_dSeparated_of_subset_sep` is the machine-checkable refutation, witnessed by the
  three-vertex collider `0 → 2 ← 1`. This is the one structural difference between
  d-separation and `Separates`;
* the graph `(G_{An(A ∪ B ∪ S)})^m` in which Proposition 3.25 reads is `Markov.ancestralMoralGraph`
  (upstream — not redefined here);
* `dSeparated_iff_separates_moralGraph_ancestralClosure` — **Proposition 3.25**, the headline:
  for disjoint `A`, `B`, `S` in a DAG, `S` d-separates `A` from `B` **iff** `S` separates `A`
  from `B` in `(G_{An(A ∪ B ∪ S)})^m`;
* `dSeparated_iff_forall_nodup` — the book's own phrasing, over chains with *distinct* vertices
  (see note 1); a corollary of Proposition 3.25 applied to both readings;
* `condIndep_of_dSeparated` — the consequence: under the **directed global Markov property**,
  d-separation implies conditional independence. Cited as **Proposition 3.25 + Corollary
  3.23**; see the reference block for why there is no single theorem number for it.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996:

* *chain*: §2.1.1, p. 6, **unnumbered** — "a chain of length `n` from `α` to `β` is a sequence
  `α = α₀, …, αₙ = β` of distinct vertices such that `αᵢ₋₁ → αᵢ` or `αᵢ → αᵢ₋₁` for all `i`";
* *blocked / active / d-separated*: §3.2.2, p. 48, **unnumbered**, credited to Pearl (1986) with
  the formal treatment in Verma and Pearl (1990) — "a chain `π` from `a` to `b` is said to be
  blocked by `S` if it contains a vertex `γ ∈ π` such that either `γ ∈ S` and arrows of `π` do
  not meet head-to-head at `γ`, or `γ ∉ S` nor has `γ` any descendants in `S`, and arrows of `π`
  do meet head-to-head at `γ`. A chain that is not blocked by `S` is said to be active. Two
  subsets `A` and `B` are now said to be d-separated by `S` if all chains from `A` to `B` are
  blocked by `S`";
* **Proposition 3.25**, p. 48 — for **disjoint** `A`, `B`, `S`, `S` d-separates `A` from `B` iff
  `S` separates `A` from `B` in `(G_{An(A∪B∪S)})^m`;
* **Corollary 3.23**, p. 47 — the conditional independence `A ⫫ B ∣ S` holds whenever `A` and
  `B` are separated by `S` in `(G_{An(A∪B∪S)})^m`; "the property in Corollary 3.23 will be
  referred to as the **directed global Markov property (DG)**".

⚠️ **There is no single numbered theorem "d-separation ⟺ directed global Markov".** The book
gives (DG) a *moral-graph* definition (Cor. 3.23) and then proves separately that d-separation
is equivalent to it (Prop. 3.25). `condIndep_of_dSeparated` is therefore tagged with **both**
numbers, and its proof is literally "Prop. 3.25, then (DG)". Citing it as one theorem would
misattribute (`Lauritzen §3.2.2` in tags).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Chains are oriented walks; the book's chains have distinct vertices.** Lauritzen's chain
   (p. 6) is a sequence of *distinct* vertices. `Chain` drops the distinctness, exactly as
   `Core.Separation.Separates` is phrased over `SimpleGraph.Walk` rather than
   `SimpleGraph.Path`: `Chain` is the type carrying the induction principle that
   `Chain.BlockedFrom` and every proof below run on, and adding a `Nodup` side condition to the
   *definition* would make the recursion carry a proof obligation it does not need. The two
   readings of d-separation agree — `dSeparated_iff_forall_nodup` — but, unlike in the
   undirected case, this is **not** a `Walk.bypass` argument: shortening a chain can turn a
   collider into a non-collider. It is instead a corollary of Proposition 3.25, which holds for
   either reading (the book's proof constructs and consumes chains whose vertex-distinctness is
   never used). This is why the equivalence is stated for a DAG with disjoint blocks and not in
   general.
2. **Orientation is data, not a proposition.** A chain could have been modelled as a walk in
   the underlying undirected graph `Relation.SymmGen r` plus a predicate reading off which of
   `r u v`, `r v u` holds at each step. We rejected that: `Relation.SymmGen r u v` is a
   *disjunction of propositions*, so "which way does this arrow point" is only recoverable by
   case analysis, and every statement about colliders would carry that case split. Recording
   the direction in the constructor (`fwd`/`bwd`) makes "arrows meet head-to-head at `γ`" a
   structural side condition of the recursion, needs no decidability of `r`, and needs no
   acyclicity — so the vocabulary is available for an arbitrary relation, and the DAG
   hypotheses appear only where they are genuinely used (Proposition 3.25 and below).
   The moral graph is *not* the underlying undirected graph anyway (it has extra marriage
   edges), so no walk type could have served both sides of Proposition 3.25.
3. **Blocking is evaluated at vertex *occurrences*.** Lauritzen writes "it contains a vertex
   `γ ∈ π`"; a chain that repeats a vertex meets it with different pairs of incident arrows
   each time, and the same vertex may be a collider at one occurrence and not at another. The
   recursion visits occurrences, which is the reading the book's proof uses.
4. **The blocking rule is stated over a bare relation, and `S`-monotonicity is refuted rather
   than proved.** `Chain`, `BlocksAt`, `Blocked` and `DSeparated` take `r : V → V → Prop`;
   a DAG-level consumer writes `DSeparated D.Adj S A B`. Nothing in these definitions uses
   acyclicity. Compared with `Separates`, exactly one API lemma is missing and cannot be added:
   `separates_of_subset_sep` has **no** d-separation analogue, because conditioning on a
   collider opens the chain through it. `not_forall_dSeparated_of_subset_sep` records this.

**Bibliographic comments.** The criterion is J. Pearl's, "Fusion, propagation, and structuring
in belief networks", *Artificial Intelligence* **29** (1986), 241–288, with the full formal
treatment in T. Verma and J. Pearl, "Causal networks: semantics and expressiveness", in
*Uncertainty in Artificial Intelligence 4*, North-Holland, 1990, 69–76; Lauritzen presents it
as "an alternative formulation of the directed global Markov property" (p. 48). Lauritzen's
remark following Proposition 3.25 (p. 50, equation **(3.22)**) records that **the criterion
cannot be improved**: D. Geiger and J. Pearl, "On the logic of causal models", in *Uncertainty
in Artificial Intelligence 4*, North-Holland, 1990, show in their Theorem 5 that for any
directed acyclic graph `G` one can choose state spaces and a probability `P` for which
`A ⫫ B ∣ S ⟺ S` d-separates `A` from `B` — so no strictly finer graphical rule reads more
conditional independences out of the graph than d-separation does. That is a statement about
the *existence of a law*, quantified over state spaces, and is recorded here as a remark only:
it is far outside this file's scope and is deliberately **not** stated in Lean. Mathlib has no
d-separation vocabulary in this pin (`Digraph` is a bare `Adj : V → V → Prop` with no path
API), so `Chain` and everything above it is new; `Relation.ReflTransGen`, `List.Nodup` and
`SimpleGraph` are Mathlib's, and `Separates` is this area's round-1 file.
-/

namespace StatLean.StatisticalModels.GraphicalModels

universe u

variable {V : Type u}

/-! ### Orientation vocabulary -/

/-- The direction of one arrow of a chain, **read from a vertex it is incident to**: `into` if
the arrow points at that vertex, `outOf` if it points away from it.

*Edge behaviour.* The two ends of a chain have an arrow on one side only; the missing side is
represented by `none : Option ArrowDir` rather than by a third constructor, so that
`IsCollider` can be stated uniformly at every vertex occurrence of a chain, endpoints
included. -/
inductive ArrowDir where
  /-- The arrow points at the vertex. -/
  | into : ArrowDir
  /-- The arrow points away from the vertex. -/
  | outOf : ArrowDir
  deriving DecidableEq

/-- **Arrows meet head-to-head** (Lauritzen p. 48): the two arrows of a chain incident to a
vertex both point *into* it. `din` is the direction of the arrow on the near side of the chain
and `dout` the direction of the arrow on the far side, each `none` when there is no such arrow.

*Edge behaviour.* At an end of the chain one of the two is `none`, so `IsCollider` is false
there (`not_isCollider_none_left`, `not_isCollider_none_right`): only *interior* vertex
occurrences can be colliders, which is what Lauritzen's phrase "arrows of `π` meet head-to-head
at `γ`" means. Symmetric in its two arguments (`isCollider_comm`), so the notion does not
depend on which end of the chain one starts from. -/
def IsCollider (din dout : Option ArrowDir) : Prop :=
  din = some ArrowDir.into ∧ dout = some ArrowDir.into

/-- An end of the chain on the near side is never a collider. -/
@[simp]
theorem not_isCollider_none_left (dout : Option ArrowDir) : ¬ IsCollider none dout := by
  simp [IsCollider]

/-- An end of the chain on the far side is never a collider. -/
@[simp]
theorem not_isCollider_none_right (din : Option ArrowDir) : ¬ IsCollider din none := by
  simp [IsCollider]

/-- Being a collider does not depend on the direction the chain is traversed in. -/
theorem isCollider_comm (din dout : Option ArrowDir) :
    IsCollider din dout ↔ IsCollider dout din :=
  and_comm

/-! ### Chains -/

/-- A **chain** from `u` to `w` for the relation `r`: a sequence of vertices in which
consecutive vertices are joined by an arrow, traversed in either direction, **together with the
direction of each step**. `fwd h c` prepends a step `u → v` (so `h : r u v`) and `bwd h c`
prepends a step `u ← v` (so `h : r v u`), in both cases continuing along `c` from `v`.

This is Lauritzen's chain (§2.1.1, p. 6) *without* the requirement that the vertices be
distinct — i.e. an oriented walk. See the module docstring, note 1, for why, and
`dSeparated_iff_forall_nodup` for the book's phrasing. Modelled on `SimpleGraph.Walk`, whose
`support` / `reverse` API is mirrored below.

*Edge behaviour.* `Chain.nil v : Chain r v v` is the chain of length `0`; it has one vertex, no
arrows, and is blocked by `S` exactly when `v ∈ S`. Nothing here assumes `r` irreflexive or
acyclic: a self-loop `r v v` yields chains, and `Chain` is well-defined for any relation. -/
inductive Chain (r : V → V → Prop) : V → V → Type u
  /-- The chain of length `0` at `v`. -/
  | nil (v : V) : Chain r v v
  /-- Prepend a step traversed **along** its arrow: `u → v`, then continue from `v`. -/
  | fwd {u v w : V} (h : r u v) (c : Chain r v w) : Chain r u w
  /-- Prepend a step traversed **against** its arrow: `u ← v`, then continue from `v`. -/
  | bwd {u v w : V} (h : r v u) (c : Chain r v w) : Chain r u w

namespace Chain

variable {r : V → V → Prop}

/-- The vertices a chain visits, in order, with multiplicity — the analogue of
`SimpleGraph.Walk.support`. -/
def support : ∀ {u w : V}, Chain r u w → List V
  | u, _, nil _ => [u]
  | u, _, fwd _ c => u :: c.support
  | u, _, bwd _ c => u :: c.support

@[simp]
theorem support_nil (v : V) : (nil v : Chain r v v).support = [v] := rfl

@[simp]
theorem support_fwd {u v w : V} (h : r u v) (c : Chain r v w) :
    (fwd h c).support = u :: c.support := rfl

@[simp]
theorem support_bwd {u v w : V} (h : r v u) (c : Chain r v w) :
    (bwd h c).support = u :: c.support := rfl

theorem start_mem_support {u w : V} (c : Chain r u w) : u ∈ c.support := by
  cases c <;> simp

theorem end_mem_support {u w : V} (c : Chain r u w) : w ∈ c.support := by
  sorry

/-- Concatenate the reverse of the first chain with the second — the engine of `Chain.reverse`,
modelled on `SimpleGraph.Walk.reverseAux`. Reversing swaps the roles of `fwd` and `bwd`, which
is the whole content of "a chain may be traversed from either end". -/
def reverseAux : ∀ {u v w : V}, Chain r u v → Chain r u w → Chain r v w
  | _, _, _, nil _, q => q
  | _, _, _, fwd h p, q => reverseAux p (bwd h q)
  | _, _, _, bwd h p, q => reverseAux p (fwd h q)

/-- A chain read from its far end. Each step keeps its arrow and changes its traversal
direction. -/
def reverse {u w : V} (c : Chain r u w) : Chain r w u := c.reverseAux (nil u)

end Chain

/-! ### Blocking -/

/-- `γ` has **no descendant in `S`**, counting `γ` itself among its own descendants.

This is the second clause of Lauritzen's blocking rule (p. 48), "`γ ∉ S` nor has `γ` any
descendants in `S`", read as the single condition `De(γ) ∩ S = ∅` with
`De(γ) = {γ} ∪ de(γ)`: Lauritzen's `de(γ)` (§2.1.1, p. 6) excludes `γ`, and the reflexivity of
`Relation.ReflTransGen` puts it back, which is exactly the conjunction the book states.

*Book vs Lean.* Stated with `Relation.ReflTransGen` on a bare relation rather than with
`Directed.DAG.descendants`, so that `BlocksAt` is available before any DAG structure is fixed;
for `r = D.Adj` the two agree by unfolding `descendants`, and no reachability fact is
re-derived here. *Edge behaviour.* Vacuously true for `S = ∅`, so over an empty separator a
chain is blocked exactly when it has a collider. -/
def NoDescendantIn (r : V → V → Prop) (S : Finset V) (γ : V) : Prop :=
  ∀ d : V, Relation.ReflTransGen r γ d → d ∉ S

/-- **Lauritzen's blocking rule at one vertex occurrence** (p. 48, unnumbered). The vertex `γ`
of a chain, met with incident arrow directions `din` (near side) and `dout` (far side), blocks
the chain relative to `S` when either

* the arrows do **not** meet head-to-head at `γ` and `γ ∈ S`, or
* they **do** meet head-to-head at `γ` and neither `γ` nor any descendant of `γ` is in `S`.

*Edge behaviour.* At an end of the chain (`din = none` or `dout = none`) the vertex is never a
collider, so the rule reduces to `γ ∈ S`; in particular a chain that starts or ends inside `S`
is blocked, which is what makes `dSeparated_self_left` / `_right` true and mirrors
`separates_self_left` / `_right`. The two clauses are mutually exclusive and exhaust the cases,
so `BlocksAt` is the negation of "`γ` leaves the chain open at this occurrence". -/
def BlocksAt (r : V → V → Prop) (S : Finset V) (din dout : Option ArrowDir) (γ : V) : Prop :=
  (¬ IsCollider din dout ∧ γ ∈ S) ∨ (IsCollider din dout ∧ NoDescendantIn r S γ)

namespace Chain

variable {r : V → V → Prop}

/-- **A chain is blocked by `S`**, given the direction `din` of the arrow entering its first
vertex from the part of the chain already traversed (`none` at the start of the whole chain).

Structural recursion on the chain: at each vertex the recursion knows the direction of the
arrow behind it (`din`, the accumulator) and reads the direction of the arrow ahead of it off
the constructor — `fwd` means the next arrow points *out of* the current vertex and *into* the
next one, `bwd` the other way round. The chain is blocked when *some* occurrence blocks
(`BlocksAt`), which is Lauritzen's "it contains a vertex `γ ∈ π` such that …".

*Edge behaviour.* On `nil` the far side is `none`, so the last vertex blocks exactly when it
lies in `S`. The accumulator is an implementation detail of the recursion; the user-facing
predicate is `Chain.Blocked`, which starts it at `none`. -/
def BlockedFrom (S : Finset V) : ∀ {u w : V}, Option ArrowDir → Chain r u w → Prop
  | γ, _, din, nil _ => BlocksAt r S din none γ
  | γ, _, din, fwd _ c =>
      BlocksAt r S din (some ArrowDir.outOf) γ ∨ BlockedFrom S (some ArrowDir.into) c
  | γ, _, din, bwd _ c =>
      BlocksAt r S din (some ArrowDir.into) γ ∨ BlockedFrom S (some ArrowDir.outOf) c

/-- **A chain is blocked by `S`** (Lauritzen p. 48): some vertex occurrence of it blocks. The
first vertex has no arrow behind it, whence the `none`. -/
def Blocked {u w : V} (c : Chain r u w) (S : Finset V) : Prop :=
  BlockedFrom S none c

/-- **A chain is active** (Lauritzen p. 48): "a chain that is not blocked by `S` is said to be
active". Definitionally the negation of `Chain.Blocked`; kept as a name because the book's
proofs, and the informal reading of d-separation, are phrased in terms of active chains. -/
def Active {u w : V} (c : Chain r u w) (S : Finset V) : Prop :=
  ¬ c.Blocked S

theorem active_iff_not_blocked {u w : V} (c : Chain r u w) (S : Finset V) :
    c.Active S ↔ ¬ c.Blocked S := Iff.rfl

/-- **Blocking does not depend on the direction of traversal.** Reversing a chain exchanges the
near and far side at every vertex occurrence, and `IsCollider` is symmetric
(`isCollider_comm`), so the set of blocking occurrences is unchanged. This is what makes
d-separation symmetric in `A` and `B`, and it is the directed counterpart of
`Walk.support_reverse` in `separates_symm`.

The intended proof generalises over the accumulator: `BlockedFrom S din (p.reverseAux q)` is
`BlockedFrom` of `p` and of `q` glued at their common endpoint, with the two accumulators
exchanged. -/
theorem blocked_reverse {u w : V} (c : Chain r u w) (S : Finset V) :
    c.reverse.Blocked S ↔ c.Blocked S := by
  sorry

/-- A chain that **starts** inside the separator is blocked: its first vertex has no arrow
behind it, hence is not a collider, hence blocks as soon as it lies in `S`. The directed
counterpart of the fact that a walk meets `S` at its own first vertex. -/
theorem blocked_of_start_mem {u w : V} (c : Chain r u w) {S : Finset V}
    -- USER-INPUT: the first vertex lies in the separator; Lauritzen p. 48 excludes this by
    -- assuming `A`, `B`, `S` disjoint, so this is a Lean-side completion of the definition
    (hu : u ∈ S) :
    c.Blocked S := by
  sorry

/-- A chain that **ends** inside the separator is blocked — the mirror image of
`blocked_of_start_mem`, via the last vertex. -/
theorem blocked_of_end_mem {u w : V} (c : Chain r u w) {S : Finset V}
    -- USER-INPUT: the last vertex lies in the separator; see `blocked_of_start_mem`
    (hw : w ∈ S) :
    c.Blocked S := by
  sorry

end Chain

/-! ### d-separation -/

/-- `S` **d-separates** `A` from `B` for the relation `r` (Lauritzen p. 48, unnumbered): every
chain from a vertex of `A` to a vertex of `B` is blocked by `S`.

*Book vs Lean.* Stated for a bare relation `r : V → V → Prop`; a consumer holding a
`D : DAG V` writes `DSeparated D.Adj S A B`. Nothing in the definition uses acyclicity — it is
needed only from `dSeparated_iff_separates_moralGraph_ancestralClosure` onwards — and stating
it here would make every basic lemma below carry a hypothesis it does not use. The argument
order `S A B` matches `Core.Separation.Separates`.

*Edge behaviour.* Vacuously true when `A = ∅` or `B = ∅` (`dSeparated_empty_left`,
`dSeparated_empty_right`), and automatically true when `A ⊆ S` or `B ⊆ S`
(`dSeparated_self_left`, `dSeparated_self_right`) since an endpoint of a chain is never a
collider. No disjointness of `A`, `B`, `S` is assumed, exactly as in `Separates`; Lauritzen's
disjointness is carried by the consumers that need it (Proposition 3.25 below). Unlike
`Separates`, this is **not** monotone in `S`: see `not_forall_dSeparated_of_subset_sep`. -/
def DSeparated (r : V → V → Prop) (S A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ c : Chain r a b, c.Blocked S

variable {r : V → V → Prop} {S A A' B B' : Finset V}

/-- **Symmetry.** d-separation is symmetric in the two separated blocks: reverse the chain
(`Chain.reverse`, `Chain.blocked_reverse`). -/
theorem dSeparated_symm
    -- USER-INPUT: the d-separation to be flipped; Lauritzen p. 48 (the book's definition is
    -- visibly symmetric, being phrased on chains, which have no preferred direction)
    (h : DSeparated r S A B) :
    DSeparated r S B A :=
  fun a ha b hb c => (Chain.blocked_reverse c S).mp (h b hb a ha c.reverse)

/-- **Symmetry, as an equivalence.** -/
theorem dSeparated_comm : DSeparated r S A B ↔ DSeparated r S B A :=
  ⟨dSeparated_symm, dSeparated_symm⟩

/-- **Monotone in the first block**: shrinking `A` preserves d-separation. -/
theorem dSeparated_mono_left
    -- USER-INPUT: the smaller first block; free choice of the caller (Lauritzen p. 48 blocks
    -- *all* chains from `A` to `B`, so a sub-block inherits it)
    (hA : A' ⊆ A)
    -- USER-INPUT: the d-separation to be weakened; Lauritzen p. 48
    (h : DSeparated r S A B) :
    DSeparated r S A' B :=
  fun a ha b hb c => h a (hA ha) b hb c

/-- **Monotone in the second block**: shrinking `B` preserves d-separation. -/
theorem dSeparated_mono_right
    -- USER-INPUT: the smaller second block; free choice of the caller (Lauritzen p. 48)
    (hB : B' ⊆ B)
    -- USER-INPUT: the d-separation to be weakened; Lauritzen p. 48
    (h : DSeparated r S A B) :
    DSeparated r S A B' :=
  fun a ha b hb c => h a ha b (hB hb) c

/-- **Degenerate case**: nothing to d-separate on the left. -/
theorem dSeparated_empty_left : DSeparated r S ∅ B :=
  fun a ha _ _ _ => absurd ha (Finset.notMem_empty a)

/-- **Degenerate case**: nothing to d-separate on the right. -/
theorem dSeparated_empty_right : DSeparated r S A ∅ :=
  fun _ _ b hb _ => absurd hb (Finset.notMem_empty b)

/-- **Degenerate case**: a block contained in the separator is d-separated from everything —
the first vertex of a chain is never a collider, so it blocks as soon as it lies in `S`. This
is the reason the book's disjointness assumption is not needed in the definition. -/
theorem dSeparated_self_left
    -- USER-INPUT: the first block sits inside the separator; the book excludes this case by
    -- assuming `A`, `B`, `S` disjoint, so this is a Lean-side completion of the definition
    (hAS : A ⊆ S) :
    DSeparated r S A B :=
  fun a ha _ _ c => c.blocked_of_start_mem (hAS ha)

/-- **Degenerate case**: dual of `dSeparated_self_left`, via the last vertex of the chain. -/
theorem dSeparated_self_right
    -- USER-INPUT: the second block sits inside the separator; see `dSeparated_self_left`
    (hBS : B ⊆ S) :
    DSeparated r S A B :=
  fun _ _ b hb c => c.blocked_of_end_mem (hBS hb)

/-- **Adjacent vertices are never d-separated.** The one-arrow chain `a → b` has two vertices,
both ends, hence both non-colliders; if neither lies in `S` the chain is active. The directed
counterpart of the fact that an edge defeats every separator disjoint from its endpoints. -/
theorem not_dSeparated_of_rel {a b : V}
    -- USER-INPUT: the arrow; Lauritzen §2.1.1, p. 5
    (hab : r a b)
    -- USER-INPUT: the tail is outside the separator; Lauritzen p. 48 assumes `A`, `S` disjoint
    (haS : a ∉ S)
    -- USER-INPUT: the head is outside the separator; Lauritzen p. 48 assumes `B`, `S` disjoint
    (hbS : b ∉ S) :
    ¬ DSeparated r S {a} {b} := by
  sorry

/-! ### The separator is not monotone — refutation

`Core.Separation.separates_of_subset_sep` says that growing the separator preserves undirected
separation. **The d-separation analogue is false**, and this section refutes it rather than
leaving a plausible-looking lemma unstated. The obstruction is the second clause of the
blocking rule: a collider blocks only while neither it nor any of its descendants lies in `S`,
so putting the collider *into* `S` opens the chain. This is the whole point of Pearl's
criterion — "explaining away" — and it is why `IsDirectedGlobalMarkov` cannot be obtained from
the undirected global Markov property of any single fixed graph. -/

/-- The three-vertex collider `0 → 2 ← 1` on `Fin 3`, as a bare relation. It is acyclic (every
arrow ends at `2`, which has no outgoing arrow) and loopless, so it is the adjacency relation of
a genuine directed acyclic graph; it is used only to refute monotonicity of d-separation in the
separator. -/
def colliderRel : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ∨ a = 1) ∧ b = 2

/-- Over the empty separator the collider blocks: every chain from `0` to `1` must leave `0`
along `0 → 2` and arrive at `1` against `1 → 2`, so it meets `2` head-to-head, and with `S = ∅`
the descendant condition is vacuous. -/
theorem dSeparated_collider_empty : DSeparated colliderRel ∅ {0} {1} := by
  sorry

/-- Conditioning **on** the collider opens the chain `0 → 2 ← 1`: at `2` the arrows meet
head-to-head and `2` is one of its own descendants, so `2` does not block; the two ends `0` and
`1` are not colliders and are not in `{2}`, so they do not block either. -/
theorem not_dSeparated_collider_singleton : ¬ DSeparated colliderRel {2} {0} {1} := by
  sorry

/-- **d-separation is not monotone in the separator.** The undirected `separates_of_subset_sep`
has no analogue here: `∅ ⊆ {2}` d-separates `{0}` from `{1}` in `0 → 2 ← 1` while `{2}` does
not. -/
theorem not_forall_dSeparated_of_subset_sep :
    ¬ ∀ (W : Type) (r : W → W → Prop) (S S' A B : Finset W), S ⊆ S' →
        DSeparated r S A B → DSeparated r S' A B := fun h =>
  not_dSeparated_collider_singleton
    (h (Fin 3) colliderRel ∅ {2} {0} {1} (Finset.empty_subset _) dSeparated_collider_empty)

/-! ### Proposition 3.25 — d-separation is moral-graph separation

⚠️ *Names imported from the concurrent directed files.* This section is stated against
`DAG` / `DAG.Adj` / `DAG.induce` (`Directed/DAG.lean`), `moralGraph` (`Directed/Moralization.lean`)
and `IsDirectedGlobalMarkov` (`Directed/Markov.lean`). Everything above this line is
independent of those files. -/

section Prop325

variable [Fintype V] [DecidableEq V]

/-- The undirected graph `(G_{An(A ∪ B ∪ S)})^m` of Lauritzen's Proposition 3.25 (p. 48):
**moralize the sub-DAG induced on the smallest ancestral set containing `A ∪ B ∪ S`.**

Named because the object occurs in the statement of Proposition 3.25, of Corollary 3.23 (the
directed global Markov property), and of every consumer of either; the two operations it
composes are both supplied by `Directed/DAG.lean` and `Directed/Moralization.lean` and are
**not** re-derived here.

*Edge behaviour.* `ancestralClosure` of the empty set is empty and moralization of the empty
sub-DAG is the empty graph, so at `A = B = S = ∅` this is `⊥` and `Separates ⊥ ∅ ∅ ∅` holds
vacuously — matching `dSeparated_empty_left`. The vertex type is all of `V`: the induced
sub-DAG keeps `V` as its vertex type and merely deletes arrows leaving the ancestral set, so
`Separates` and `DSeparated` speak about the same blocks without any subtype transport. -/
*Deduplicated.* This object is **not** defined here. `Directed/Markov.lean` already provides
`ancestralMoralGraph D T = inducedMoralGraph D (D.ancestralClosure T)`, which at
`T := A ∪ B ∪ S` is exactly the graph Proposition 3.25 reads in, and which in turn composes
`Directed/Factorization.lean`'s `inducedMoralGraph`. Both files are upstream of this one, so
the statements below consume `ancestralMoralGraph D (A ∪ B ∪ S)` directly rather than
introducing a third spelling of the same composite. -/

/-- **Lauritzen Proposition 3.25** (p. 48) — *the headline of this file*. For **disjoint**
blocks `A`, `B`, `S` of a directed acyclic graph `D`, the separator `S` d-separates `A` from `B`
**iff** `S` separates `A` from `B` in `(G_{An(A∪B∪S)})^m`.

This is the bridge that lets the entire round-1 undirected layer (`Core.Separation` and its
`Undirected.Markov` consumers) serve the directed theory: the left-hand side is Pearl's local,
chain-by-chain criterion, the right-hand side is a single application of `Separates` to one
explicitly constructed undirected graph.

**Proof (the book's, p. 48–49).** Both directions are contrapositives.

* *Not d-separated ⇒ not separated in the moral graph.* Take an active chain `π` from `A` to
  `B`. Every vertex of `π` lies in `An(A ∪ B ∪ S)`: at a head-to-head vertex `γ` activity forces
  `γ ∈ S` or `γ` to have a descendant in `S`, so `γ ∈ An(S)`; and any other vertex leads, along
  the arrows of `π`, either to a head-to-head vertex or all the way to an endpoint in `A ∪ B`.
  Each head-to-head meeting marries its two neighbours on `π` in the moral graph, so deleting
  the head-to-head vertices from `π` leaves a walk in `(G_{An(A∪B∪S)})^m` from `A` to `B`; its
  vertices are the non-head-to-head vertices of `π`, none of which lies in `S`, since `π` is
  active. (When the two neighbours of a head-to-head vertex coincide, no marriage edge is
  needed and the walk simply stays put — this is where allowing repeated vertices in `Chain`
  costs nothing.)
* *Not separated in the moral graph ⇒ not d-separated.* A walk in `(G_{An(A∪B∪S)})^m`
  circumventing `S` has pieces that are arrows of `D` and pieces that are marriages. Each
  marriage comes from a head-to-head meeting at some `γ`. If `γ ∈ S`, or `γ` has a descendant
  in `S`, the meeting does not block. If not, then `γ` must have a descendant in `A ∪ B` —
  *because the ancestral set was the smallest one* — and rerouting along that line of descent
  produces a chain with one head-to-head meeting fewer. Iterating terminates in an active chain
  from `A` to `B`.

Note where acyclicity is used: in "the ancestral set was smallest", i.e. in the fact that a
vertex of `An(A ∪ B ∪ S)` which is not an ancestor of `S` must be an ancestor of `A ∪ B`. -/
theorem dSeparated_iff_separates_moralGraph_ancestralClosure (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    -- ("let `A`, `B` and `S` be disjoint subsets")
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S) :
    DSeparated D.Adj S A B ↔ Separates (ancestralMoralGraph D (A ∪ B ∪ S)) S A B := by
  sorry

/-- **The book's phrasing of d-separation**, over chains whose vertices are *distinct*.
Lauritzen's chains (§2.1.1, p. 6) are vertex-distinct sequences; `Chain` drops that requirement
(module docstring, note 1). The two readings of d-separation agree.

*This is not the undirected argument.* `separates_iff_forall_path` follows from
`SimpleGraph.Walk.bypass`, which shortens a walk to a path with smaller support; the same move
is **unavailable** here, because deleting a repeated section of a chain can turn a collider into
a non-collider and so turn a blocked chain into an active one. The equivalence is instead a
corollary of Proposition 3.25 applied twice: the book proves that *its* (vertex-distinct)
d-separation is equivalent to separation in `(G_{An(A∪B∪S)})^m`, and
`dSeparated_iff_separates_moralGraph_ancestralClosure` proves the same for the walk reading, so
the two agree. That is why this statement — unlike every other basic lemma in this file —
carries the DAG and the disjointness hypotheses. -/
theorem dSeparated_iff_forall_nodup (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S) :
    DSeparated D.Adj S A B ↔
      ∀ a ∈ A, ∀ b ∈ B, ∀ c : Chain D.Adj a b, c.support.Nodup → c.Blocked S := by
  sorry

/-- **d-separation implies conditional independence** — Lauritzen **Proposition 3.25** (p. 48)
composed with **Corollary 3.23** (p. 47).

⚠️ *Two citations, deliberately.* The book **defines** the directed global Markov property (DG)
by the moral-graph criterion of Corollary 3.23 and proves *separately*, in Proposition 3.25,
that d-separation is the same relation. There is no single numbered result in Lauritzen saying
"d-separation ⟹ conditional independence", and citing one number for this theorem would
misattribute it. The Lean proof is the composition: rewrite along
`dSeparated_iff_separates_moralGraph_ancestralClosure`, then apply the hypothesis.

Stated against the **abstract** relation `ci : Finset V → Finset V → Finset V → Prop` (read
`ci A B S` as `X_A ⫫ X_B ∣ X_S`), as everything in `Undirected.Markov` is, so that every model
class — the discrete mass relation, the Gaussian precision relation, the general `CondIndep` —
gets the criterion once (Lauritzen's own remark after Proposition 3.4, p. 33, that these
arguments depend only on the calculus). -/
theorem condIndep_of_dSeparated (D : DAG V) [DecidableRel D.Adj] [DecidableRel (Relation.TransGen D.Adj)] (ci : Finset V → Finset V → Finset V → Prop)
    -- USER-INPUT: the directed global Markov property of the law; Lauritzen Corollary 3.23,
    -- p. 47, which is where (DG) is defined
    (hDG : IsDirectedGlobalMarkov D ci) (A B S : Finset V)
    -- USER-INPUT: the two separated blocks are disjoint; Lauritzen Proposition 3.25, p. 48
    (hAB : Disjoint A B)
    -- USER-INPUT: the first block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hAS : Disjoint A S)
    -- USER-INPUT: the second block avoids the separator; Lauritzen Proposition 3.25, p. 48
    (hBS : Disjoint B S)
    -- USER-INPUT: the graphical criterion, read off the DAG; Lauritzen p. 48
    (hd : DSeparated D.Adj S A B) :
    ci A B S := by
  sorry

end Prop325

end StatLean.StatisticalModels.GraphicalModels
