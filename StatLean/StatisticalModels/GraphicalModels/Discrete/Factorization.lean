import StatLean.StatisticalModels.GraphicalModels.Discrete.CondIndep
import StatLean.StatisticalModels.GraphicalModels.Undirected.Markov
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Factorization over the cliques of a graph — property (F)

Lauritzen's fourth Markov-type property: a mass function **factorizes** over an undirected
graph `G` when it is a product of non-negative factors, one for each complete vertex set, each
depending on the configuration only through its own coordinates. Together with
`Discrete/CondIndep.lean` (which supplies the graphoid calculus) this closes the discrete
chain (F) ⇒ (G) ⇒ (L) ⇒ (P) of Lauritzen's Proposition 3.8, and sets up the round-2 headline,
Hammersley–Clifford.

* `completeSubsets G` — the `Finset` of complete vertex sets, assembled from Mathlib's
  `SimpleGraph.IsClique`;
* `IsCliquePotential G ψ` — a family of **clique potentials**: `ψ c` depends only on `x_c`;
* `FactorizesOver G p` — property **(F)**, Lauritzen eqs. **(3.11)/(3.12)**, pp. 34–35;
* `isClique_subset_or_of_separates` — the one graph-theoretic fact behind (F) ⇒ (G): a complete
  set cannot straddle a separator;
* `exists_factorization_of_separates` — the product splits across a separator into a factor on
  `A ∪ S` and a factor on `B ∪ S`;
* **`factorizesOver_implies_globalMarkov`** — Lauritzen **Proposition 3.8**, p. 35, (F) ⇒ (G),
  stated against the abstract `IsGlobalMarkov` of `Undirected/Markov.lean` instantiated at
  `CondIndepMass`;
* `factorizesOver_implies_localMarkov` / `factorizesOver_implies_pairwiseMarkov` — the rest of
  Proposition 3.8, by composition with the hierarchy;
* **`hammersleyClifford`** — Lauritzen **Theorem 3.9**, p. 36: for a *strictly positive* mass
  function, (P) ⟺ (F). **Stated, not proved** — the designated round-2 headline.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996**: property (F) is the unnumbered definition on pp. 34–35 with
equations **(3.11)** (product over complete subsets) and **(3.12)** (product over cliques);
**Proposition 3.8** (p. 35) is (F) ⇒ (G) ⇒ (L) ⇒ (P); **Theorem 3.9** (p. 36) is the
Hammersley–Clifford theorem, that a positive and continuous density satisfies (P) iff it
factorizes; **Example 3.10** (pp. 37–38) is Moussouris's counterexample. Lauritzen remarks on
p. 28 that on a discrete space every function is continuous (`Lauritzen §3.2`).

**Proof formalization notes.** *Book vs Lean, four deliberate differences.*

1. **Complete subsets, not maximal cliques.** Lauritzen's (3.11) is a product over complete
   subsets and his (3.12) is the same product regrouped over the *maximal* complete subsets,
   which he calls cliques; the two properties are equivalent, since a potential attached to a
   complete set can be absorbed into any maximal complete set containing it. Mathlib's
   `SimpleGraph.IsClique` means *complete*, not maximal, so `FactorizesOver` is (3.11)
   verbatim. Mathlib's `SimpleGraph.cliqueFinset n` is the finset of complete sets of a **given
   size** `n` and is therefore not the index family we need; `completeSubsets` filters
   `Finset.univ : Finset (Finset V)` by `IsClique` instead. No notion of clique is redefined.
2. **The potentials are functions of the whole configuration.** As in `Discrete/CondIndep.lean`,
   `ψ c : (V → α) → ℝ≥0∞` with the constraint `DependsOn (ψ c) ↑c` (Mathlib's `DependsOn`),
   rather than a function on the subtype `↥c → α`. The two readings are interchangeable by
   `dependsOn_iff_exists_comp`; keeping a single type is what makes the product
   `∏ c ∈ completeSubsets G, ψ c x` a plain `Finset.prod` in `ℝ≥0∞`.
3. **No normalisation, no finiteness in (F) ⇒ (G).** Lauritzen's `f` is a density; ours is a
   bare `ℝ≥0∞`-valued mass. `factorizesOver_implies_globalMarkov` needs neither: the route
   splits a product and then applies `condIndepMass_of_exists_factorization`, which is the
   division-free half of the criterion (3.6). Finiteness reappears only in
   `hammersleyClifford`, whose reverse implication runs through the graphoid calculus.
4. **The extension step in (F) ⇒ (G) is explicit.** The product only splits when the three
   blocks *cover* `V`. For a general separated triple `(A, B, S)` one first enlarges `A` to the
   union of the connected components of `G ∖ S` meeting `A`, sets `B'` to the rest, splits
   there, and then shrinks back with (C2). The enlargement is Mathlib's `ComponentCompl` (see
   `separates_iff_componentComplMk_ne` in `Core/Separation.lean`); the shrinking is
   `CondIndepMass.decomposition`, which needs neither finiteness nor positivity.

**Moussouris's example — why Theorem 3.9 needs positivity** (Lauritzen **Example 3.10**,
pp. 37–38). On the four-cycle `1 − 2 − 3 − 4 − 1` with binary states there is a mass function
that is globally Markov, hence pairwise Markov, but does **not** factorize: its support is a
set of eight configurations chosen so that every attempt to write `p` as a product over the
four edges forces a potential to vanish somewhere it must not. The example is *not* formalized
here, and deliberately so — it is a counterexample, not a reusable theorem, and stating it
would require pinning a concrete `V = Fin 4`, `α = Fin 2` model. Its role in this file is
documentary: it is the reason `hammersleyClifford` carries `hpos`, and the reason
`Undirected/Markov.pairwiseMarkov_implies_globalMarkov` carries `IsGraphoid` rather than
`IsSemigraphoid`.

**Reuse (binding).** `SimpleGraph.IsClique` and its `Decidable` instance
(`Combinatorics/SimpleGraph/Clique.lean:73`), `SimpleGraph.IsClique.subset`, `Separates` and
its API from `Core/Separation.lean`, `SimpleGraph.Walk`/`Walk.support` for the straddling
argument, `DependsOn` and `DependsOn.mono` from Mathlib, `Finset.prod_filter_mul_prod_filter_not`
and `Finset.prod_congr` for the product split, and from `Discrete/CondIndep.lean` the whole
mass API — `blockMarginal_univ`, `condIndepMass_of_exists_factorization`,
`CondIndepMass.decomposition`, `CondIndepMass.symm`, `isSemigraphoid_condIndepMass`,
`isGraphoid_condIndepMass_of_pos`. The Markov hierarchy itself
(`globalMarkov_implies_localMarkov`, `globalMarkov_implies_pairwiseMarkov`) is
`Undirected/Markov.lean` and is composed with, never re-proved.

**Bibliographic comments.** The equivalence of the Markov property and factorization for
strictly positive distributions is the Hammersley–Clifford theorem: J. M. Hammersley and
P. E. Clifford, "Markov fields on finite graphs and lattices," 1971, unpublished; the first
published proofs are J. Besag, "Spatial interaction and the statistical analysis of lattice
systems," *J. Roy. Statist. Soc. Ser. B* **36** (1974), 192–236, and G. R. Grimmett, "A theorem
about random fields," *Bull. London Math. Soc.* **5** (1973), 81–84. The necessity of
positivity is J. Moussouris, "Gibbs and Markov random systems with constraints," *J. Statist.
Phys.* **10** (1974), 11–33 — Lauritzen's Example 3.10.
-/

open SimpleGraph
open scoped ENNReal

namespace StatLean.StatisticalModels.GraphicalModels

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

/-! ### Complete subsets and clique potentials -/

/-- The **complete vertex sets** of `G` — Lauritzen's index family for eq. (3.11), p. 34.

Assembled from Mathlib's `SimpleGraph.IsClique` (which means *complete*, not maximal) by
filtering `Finset.univ : Finset (Finset V)`. Mathlib's `SimpleGraph.cliqueFinset n` is the
family of complete sets of a **fixed size** `n`, so it is not usable here.

Edge behaviour: `∅` and every singleton are complete (`SimpleGraph.IsClique.of_subsingleton`),
so `completeSubsets G` always contains `∅` and all `{v}`; for the complete graph it is all of
`Finset.univ`, and for the empty graph it is `{∅} ∪ {{v} | v}`. -/
def completeSubsets (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter fun c : Finset V => G.IsClique (c : Set V)

@[simp]
theorem mem_completeSubsets {G : SimpleGraph V} [DecidableRel G.Adj] {c : Finset V} :
    c ∈ completeSubsets G ↔ G.IsClique (c : Set V) := by
  simp [completeSubsets]

/-- A family of **clique potentials** for `G` (Lauritzen eq. (3.11), p. 34): for every complete
set `c`, the factor `ψ c` depends on the configuration only through the coordinates in `c`.

Edge behaviour: nothing is required of `ψ c` for a non-complete `c` — those factors never enter
the product in `FactorizesOver`. The potentials are `ℝ≥0∞`-valued and are *not* required to be
finite, positive, or normalised; Lauritzen's are non-negative measurable functions. -/
def IsCliquePotential (G : SimpleGraph V) (ψ : Finset V → (V → α) → ℝ≥0∞) : Prop :=
  ∀ c : Finset V, G.IsClique (c : Set V) → DependsOn (ψ c) (c : Set V)

/-- **Property (F): `p` factorizes over `G`** — Lauritzen eqs. **(3.11)/(3.12)**, pp. 34–35:
`p(x) = ∏_{c complete} ψ_c(x_c)` for some family of clique potentials.

*Book vs Lean.* This is (3.11), the product over **complete** subsets. Lauritzen's (3.12) is
the same property with the product taken over the maximal complete subsets ("cliques"); the two
are equivalent, since each potential may be absorbed into a maximal complete set containing its
index, and we state (3.11) because Mathlib's `IsClique` is completeness rather than maximality.

Edge behaviour: the empty set and all singletons are complete, so `FactorizesOver G p` always
permits a global constant and an arbitrary product of one-vertex factors; in particular every
`p` of the form `∏ v, f v (x v)` factorizes over the **empty** graph, and every `p` whatsoever
factorizes over the **complete** graph (take `ψ Finset.univ := p` and all other factors `1`),
which is the degenerate case in which (F) says nothing. -/
def FactorizesOver (G : SimpleGraph V) [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞) : Prop :=
  ∃ ψ : Finset V → (V → α) → ℝ≥0∞, IsCliquePotential G ψ ∧
    ∀ x, p x = ∏ c ∈ completeSubsets G, ψ c x

/-! ### (F) ⇒ (G) — Lauritzen Proposition 3.8 -/

variable (G : SimpleGraph V)

/-- **A complete set cannot straddle a separator.** If `S` separates `A` from `B` and the three
blocks cover `V`, then every complete set lies entirely inside `A ∪ S` or entirely inside
`B ∪ S`.

This is the only graph theory in the file. Route: if a complete `c` met both `A ∖ S` and
`B ∖ S` at two distinct vertices they would be adjacent, and the one-edge walk between them has
support contained in `{a, b}`, which is disjoint from `S` — contradicting `hsep`; if it met
them at the *same* vertex, the `nil` walk at that vertex gives the same contradiction. The
cover hypothesis is what turns "`c` misses `A ∖ S`" into "`c ⊆ B ∪ S`". -/
theorem isClique_subset_or_of_separates {A B S c : Finset V}
    -- USER-INPUT: the separation hypothesis of (G); Lauritzen §3.2, p. 32
    (hsep : Separates G S A B)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.2
    (hAS : Disjoint A S) (hBS : Disjoint B S)
    -- LEAN-ONLY: the two sides together with the separator must exhaust the vertex set, else a
    -- complete set may live entirely outside all three blocks; the enlargement step of
    -- `factorizesOver_implies_globalMarkov` is what supplies this
    (hcover : A ∪ B ∪ S = Finset.univ)
    -- USER-INPUT: completeness of the set being placed; Lauritzen eq. (3.11), p. 34
    (hc : G.IsClique (c : Set V)) :
    c ⊆ A ∪ S ∨ c ⊆ B ∪ S := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Finset.not_subset] at h1 h2
  obtain ⟨u, huc, huAS⟩ := h1
  obtain ⟨v, hvc, hvBS⟩ := h2
  simp only [Finset.mem_union, not_or] at huAS hvBS
  -- the cover hypothesis places `u` in `B` and `v` in `A`
  have huB : u ∈ B := by
    have : u ∈ A ∪ B ∪ S := hcover ▸ Finset.mem_univ u
    simp only [Finset.mem_union] at this; tauto
  have hvA : v ∈ A := by
    have : v ∈ A ∪ B ∪ S := hcover ▸ Finset.mem_univ v
    simp only [Finset.mem_union] at this; tauto
  rcases eq_or_ne v u with rfl | hne
  · -- the same vertex lies in `A` and in `B`: the `nil` walk already defeats separation
    obtain ⟨s, hsS, hsw⟩ := hsep _ hvA _ huB SimpleGraph.Walk.nil
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hsw
    exact hvBS.2 (hsw ▸ hsS)
  · -- distinct vertices of a complete set are adjacent: the one-edge walk misses `S`
    have hadj : G.Adj v u := hc (by simpa using hvc) (by simpa using huc) hne
    obtain ⟨s, hsS, hsw⟩ := hsep v hvA u huB (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hsw
    rcases hsw with rfl | rfl
    · exact hvBS.2 hsS
    · exact huAS.2 hsS

/-- **The product splits across a separator.** For a factorizing `p` and a separated triple
covering `V`, the product over complete sets breaks into the complete sets inside `A ∪ S` and
those inside `B ∪ S`, giving Lauritzen's criterion **(3.6)** at the blocks `A`, `B`, `S`.

Route: `isClique_subset_or_of_separates` shows the predicate "`c ⊆ A ∪ S`" partitions
`completeSubsets G` into a part on which it holds and a part contained in `B ∪ S`; take
`h := ∏` over the first part and `k := ∏` over the second
(`Finset.prod_filter_mul_prod_filter_not`), whose dependence on the respective blocks is
`IsCliquePotential` plus `DependsOn.mono`. -/
theorem exists_factorization_of_separates [DecidableRel G.Adj] {p : (V → α) → ℝ≥0∞}
    {A B S : Finset V}
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p)
    -- USER-INPUT: the separation hypothesis of (G); Lauritzen §3.2, p. 32
    (hsep : Separates G S A B)
    -- USER-INPUT: the book's disjointness convention on the triple; Lauritzen §3.2
    (hAS : Disjoint A S) (hBS : Disjoint B S)
    -- LEAN-ONLY: the covering hypothesis; see `isClique_subset_or_of_separates`
    (hcover : A ∪ B ∪ S = Finset.univ) :
    ∃ h k : (V → α) → ℝ≥0∞, DependsOn h ((A ∪ S : Finset V) : Set V) ∧
      DependsOn k ((B ∪ S : Finset V) : Set V) ∧ ∀ x, p x = h x * k x := by
  classical
  obtain ⟨ψ, hψ, hprod⟩ := hfac
  refine ⟨fun x => ∏ c ∈ (completeSubsets G).filter (fun c => c ⊆ A ∪ S), ψ c x,
    fun x => ∏ c ∈ (completeSubsets G).filter (fun c => ¬ (c ⊆ A ∪ S)), ψ c x, ?_, ?_, ?_⟩
  · intro y z hyz
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_filter] at hc
    exact DependsOn.mono (Finset.coe_subset.mpr hc.2)
      (hψ c (mem_completeSubsets.mp hc.1)) hyz
  · intro y z hyz
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_filter] at hc
    have hcl := mem_completeSubsets.mp hc.1
    -- a complete set that is not inside `A ∪ S` must be inside `B ∪ S`
    have hsub : c ⊆ B ∪ S :=
      (isClique_subset_or_of_separates G hsep hAS hBS hcover hcl).resolve_left hc.2
    exact DependsOn.mono (Finset.coe_subset.mpr hsub) (hψ c hcl) hyz
  · intro x
    rw [hprod x]
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

/-- **Lauritzen Proposition 3.8**, p. 35: **(F) ⇒ (G)**. A mass function that factorizes over
`G` is globally Markov with respect to `G`.

Stated against the abstract `IsGlobalMarkov` of `Undirected/Markov.lean` instantiated at the
discrete relation `CondIndepMass p`, so that the rest of the hierarchy — (G) ⇒ (L) ⇒ (P),
Lauritzen Proposition 3.4 — is obtained by composition rather than re-proof.

*No finiteness or positivity hypothesis.* Both halves of the route are division-free: the
product split (`exists_factorization_of_separates`) and the `mpr` half of the criterion (3.6)
(`condIndepMass_of_exists_factorization`), and the final shrinking step
(`CondIndepMass.decomposition`) is a pure sum rearrangement.

Route, given a disjoint separated triple `(A, B, S)`: enlarge `A` to `A'`, the union of `A`
with all connected components of `G` minus `S` that meet `A`, and set `B' := V ∖ (A' ∪ S)`.
Then `A ⊆ A'`, `B ⊆ B'`, the triple `(A', B', S)` is disjoint, covers `V`, and `S` still
separates `A'` from `B'` (`separates_iff_componentComplMk_ne`). Split the product there, feed
it to `condIndepMass_of_exists_factorization` after rewriting `p` as
`blockMarginal (A' ∪ B' ∪ S) p` via `blockMarginal_univ`, and shrink `A' ↝ A`, `B' ↝ B` with
`CondIndepMass.decomposition` (using `CondIndepMass.symm` on the left-hand block). -/
theorem factorizesOver_implies_globalMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsGlobalMarkov G (CondIndepMass p) := by
  classical
  intro A B S hAB hAS hBS hsep
  -- **The enlargement.** `A'` is everything reachable from `A` by a walk that never meets `S`
  -- (Lauritzen's "components of `G ∖ S` meeting `A`", spelled with walks rather than
  -- `ComponentCompl`, so that the argument is self-contained); `B'` is all the rest.
  obtain ⟨A', hA'⟩ : ∃ T : Finset V, T = Finset.univ.filter
      (fun v => v ∉ S ∧ ∃ a ∈ A, ∃ w : G.Walk a v, ∀ s ∈ S, s ∉ w.support) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ T : Finset V, T = Finset.univ \ (A' ∪ S) := ⟨_, rfl⟩
  have hmemA' : ∀ v, v ∈ A' ↔
      (v ∉ S ∧ ∃ a ∈ A, ∃ w : G.Walk a v, ∀ s ∈ S, s ∉ w.support) := by
    intro v; rw [hA']; simp
  have hmemB' : ∀ v, v ∈ B' ↔ (v ∉ A' ∧ v ∉ S) := by
    intro v; rw [hB']; simp
  -- the enlarged triple is disjoint, covers `V`, and still contains the original blocks
  have hA'S : Disjoint A' S := Finset.disjoint_left.mpr fun v hv => ((hmemA' v).mp hv).1
  have hB'S : Disjoint B' S := Finset.disjoint_left.mpr fun v hv => ((hmemB' v).mp hv).2
  have hA'B' : Disjoint A' B' := Finset.disjoint_right.mpr fun v hv => ((hmemB' v).mp hv).1
  have hcover : A' ∪ B' ∪ S = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvS : v ∈ S
    · exact Or.inr hvS
    by_cases hvA' : v ∈ A'
    · exact Or.inl (Or.inl hvA')
    · exact Or.inl (Or.inr ((hmemB' v).mpr ⟨hvA', hvS⟩))
  have hAA' : A ⊆ A' := by
    intro a ha
    refine (hmemA' a).mpr ⟨Finset.disjoint_left.mp hAS ha, a, ha, SimpleGraph.Walk.nil, ?_⟩
    intro s hs hsw
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hsw
    exact Finset.disjoint_left.mp hAS ha (hsw ▸ hs)
  have hBB' : B ⊆ B' := by
    intro b hb
    refine (hmemB' b).mpr ⟨?_, Finset.disjoint_left.mp hBS hb⟩
    intro hbA'
    obtain ⟨-, a, haA, w, hw⟩ := (hmemA' b).mp hbA'
    obtain ⟨s, hsS, hsw⟩ := hsep a haA b hb w
    exact hw s hsS hsw
  -- `S` still separates the enlarged blocks: appending an `S`-avoiding walk to an
  -- `S`-avoiding walk out of `A` would put its endpoint into `A'`.
  have hsep' : Separates G S A' B' := by
    intro a' ha' b' hb' w
    by_contra hno
    simp only [not_exists, not_and] at hno
    obtain ⟨-, a, haA, w₀, hw₀⟩ := (hmemA' a').mp ha'
    refine ((hmemB' b').mp hb').1
      ((hmemA' b').mpr ⟨((hmemB' b').mp hb').2, a, haA, w₀.append w, ?_⟩)
    intro s hs hmem
    rw [SimpleGraph.Walk.mem_support_append_iff] at hmem
    exact hmem.elim (hw₀ s hs) (hno s hs)
  -- **The split.** The product breaks across the separator, and (3.6) turns it into (3.2).
  obtain ⟨h, k, hh, hk, hpk⟩ :=
    exists_factorization_of_separates G hfac hsep' hA'S hB'S hcover
  have hci : CondIndepMass p A' B' S :=
    condIndepMass_of_exists_factorization hA'B' hA'S hB'S hh hk (fun x => by
      rw [hcover, blockMarginal_univ]; exact hpk x)
  -- **The shrinking**, by (C2) on each side in turn.
  have hci2 : CondIndepMass p A' B S := by
    refine CondIndepMass.decomposition (D := B' \ B) (hA'B'.mono_right Finset.sdiff_subset) ?_
    rwa [Finset.union_sdiff_of_subset hBB']
  have hci3 : CondIndepMass p B A' S := hci2.symm
  refine (CondIndepMass.decomposition (A := B) (B := A) (D := A' \ A)
    ((hA'B'.mono_right hBB').symm.mono_right Finset.sdiff_subset) ?_).symm
  rwa [Finset.union_sdiff_of_subset hAA']

/-- **(F) ⇒ (L)** — the second link of Lauritzen Proposition 3.8, p. 35, by composition with
`globalMarkov_implies_localMarkov`. -/
theorem factorizesOver_implies_localMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsLocalMarkov G (CondIndepMass p) :=
  globalMarkov_implies_localMarkov G (factorizesOver_implies_globalMarkov G p hfac)

/-- **(F) ⇒ (P)** — the last link of Lauritzen Proposition 3.8, p. 35. Composition with
`globalMarkov_implies_pairwiseMarkov`, which needs no property of the relation at all (the
complement of a non-adjacent pair separates it outright). -/
theorem factorizesOver_implies_pairwiseMarkov [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- USER-INPUT: property (F); Lauritzen eqs. (3.11)/(3.12), pp. 34–35
    (hfac : FactorizesOver G p) :
    IsPairwiseMarkov G (CondIndepMass p) :=
  globalMarkov_implies_pairwiseMarkov G (factorizesOver_implies_globalMarkov G p hfac)

/-! ### Theorem 3.9 — Hammersley–Clifford (designated round-2 headline)

Statement only. The forward implication is Proposition 3.8 above composed with the hierarchy;
the reverse is the substantive half, and the standard proof is a Möbius inversion of
`log p` over the subset lattice (Besag 1974; Grimmett 1973): define the interaction terms
`φ_a(x) := ∑_{b ⊆ a} (−1)^{|a ∖ b|} log p(x_b, x*_{V ∖ b})` at a fixed reference configuration
`x*`, show by the pairwise Markov property that `φ_a ≡ 0` for every non-complete `a`, and read
off the factorization. Positivity is used twice: to take logarithms at all, and to run the
cancellation in the vanishing argument. -/

/-- **The Hammersley–Clifford theorem** — Lauritzen **Theorem 3.9**, p. 36. For a *strictly
positive* mass function on a finite configuration space, the pairwise Markov property (P) and
the factorization property (F) are equivalent.

*Book vs Lean.* Lauritzen's hypotheses are that the density be **positive and continuous** with
respect to a product measure. Here the dominating product measure is counting measure on
`V → α`, and continuity is vacuous: Lauritzen himself notes on p. 28 that on a discrete space
every function is continuous. Positivity is `hpos`, and finiteness (`hp`) is the `ℝ≥0∞`-side
counterpart of "`f` is a density", needed so that the graphoid calculus
(`isGraphoid_condIndepMass_of_pos`) applies.

*Positivity is not removable.* Without it, (P) — indeed even (G) — fails to imply (F):
Lauritzen's **Example 3.10** (Moussouris, pp. 37–38); see the module docstring.

**Not proved here.** This is the designated round-2 headline; see the section docstring for the
Möbius-inversion route. The `mp` direction is already available as
`factorizesOver_implies_pairwiseMarkov` and carries no debt. -/
theorem hammersleyClifford [DecidableRel G.Adj] (p : (V → α) → ℝ≥0∞)
    -- LEAN-ONLY: finiteness of the mass function — the `ℝ≥0∞` counterpart of "`f` is a
    -- density"; needed for the graphoid calculus in the reverse direction
    (hp : ∀ x, p x ≠ ∞)
    -- USER-INPUT: strict positivity of the mass function; Lauritzen Theorem 3.9, p. 36. The
    -- theorem is false without it (Example 3.10, Moussouris, pp. 37–38)
    (hpos : ∀ x, p x ≠ 0) :
    FactorizesOver G p ↔ IsPairwiseMarkov G (CondIndepMass p) := by
  sorry

end StatLean.StatisticalModels.GraphicalModels
