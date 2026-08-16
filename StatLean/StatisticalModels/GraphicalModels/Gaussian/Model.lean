import StatLean.StatisticalModels.GraphicalModels.Gaussian.Regression
import StatLean.StatisticalModels.GraphicalModels.Gaussian.PartialCorrelation
import StatLean.StatisticalModels.Constraint.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

/-!
# Covariance selection models — the Gaussian graphical model

Lauritzen §5.2, p. 131: "the Gaussian graphical model or covariance selection model for `Y` with
graph `G` is given by assuming that `Y` follows a multivariate normal distribution which obeys
the undirected pairwise Markov property with respect to `G`. Since the density is positive and
continuous, this implies the global and local Markov properties and the density factorizes. It
follows from Proposition 5.2 that this is equivalent to assuming the quadratic interactions
`k_{γμ}` to be equal to zero for all pairs `γ, μ` which are not adjacent in `G`."

And its compact form, p. 132: let `S⁺(G)` be the set of positive definite symmetric matrices `A`
with `a_{γμ} = 0` whenever `γ ≠ μ` are non-adjacent; then the model is
`Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ⁻¹ ∈ S⁺(G)`.

* `concentrationSet G` — Lauritzen's `S⁺(G)`;
* `gaussianGraphicalModel G` — the **family of laws** `{N(m, Σ) : Σ⁻¹ ∈ S⁺(G)}`, transcribed
  verbatim from the p. 132 compact form; viewed as the fiber map of a
  `StatisticalModels.Constraint` model indexed by `Θ := SimpleGraph ι`;
* `fibersNonempty_gaussianGraphicalModel`, `fibersProbability_gaussianGraphicalModel`,
  `gaussianGraphicalModel_mono` — the constraint-model hygiene;
* `gaussianGraphicalModelExact` + `separatesTarget_gaussianGraphicalModelExact` — the *saturated*
  fibers, for which the graph **is** identified (`SeparatesTarget`); see the note below on why
  the book's own model does not separate its graph;
* **`condIndepCoords_of_mem_gaussianGraphicalModel` (HEADLINE)** — a law in the model satisfies
  the undirected **pairwise** Markov property with respect to `G`;
* `mem_gaussianGraphicalModel_iff_pairwise` — and conversely, so that Lauritzen's *definition*
  (pairwise Markov) and the p. 132 *parametrisation* (zeros of `K`) are one and the same model;
* `condIndepCoords_local_of_mem_gaussianGraphicalModel` — the **local** Markov property
  `Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`;
* `condIndepCoords_intersection_of_disjoint` — Lauritzen **Proposition 3.1 at the Gaussian**:
  the density is positive and continuous, hence conditional independence satisfies (C5)
  *intersection*, which is what upgrades pairwise to local and global;
* `condIndepCoords_of_separates` (later lane) — the **global** Markov property.

## Note: `SeparatesTarget` and why the book's model does not identify its graph

`gaussianGraphicalModel` is monotone in `G` (a zero constraint is a *restriction*), so
`gaussianGraphicalModel G ⊆ gaussianGraphicalModel H` whenever `G ≤ H`, and in particular every
model is contained in the saturated one. Hence `SeparatesTarget gaussianGraphicalModel id` is
**false** for `|Γ| ≥ 2` and is deliberately not stated. What *is* true — and is the
identifiability content of covariance selection — is that the *exact* zero pattern determines the
graph: `SeparatesTarget gaussianGraphicalModelExact id`. This is the honest reading of "the
conditional independence graph of a regular Gaussian is identified from its law".

## Note: `Core.Semigraphoid`'s `IsGraphoid` is **not** claimed here

`Core.Semigraphoid` states (C1)–(C5) for *arbitrary* triples of `Finset V`, with no disjointness
side condition, and flags that "it is the *instances* that carry the cost". The Gaussian cannot
pay it: taking `B = D` and `C = ∅`, the intersection field reads
`ci A B B → ci A B B → ci A B ∅`, whose premises hold trivially (conditioning on `X_B` makes
`X_B` degenerate) while the conclusion is unconditional independence of `X_A` and `X_B` — false
for any regular Gaussian with a nonzero covariance entry. So
`IsGraphoid (CondIndepCoords (multivariateGaussian m S) gaussianCoords)` is **refuted**, not
merely unproved, and this file states Lauritzen's (C5) in the book's own form — for *pairwise
disjoint* blocks — as `condIndepCoords_intersection_of_disjoint`. Whoever wires the Markov
hierarchy should consume that, or restrict `IsGraphoid`'s fields to disjoint blocks.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §5.2 "Covariance selection models", pp. 131–132
(the definition, the equivalence with zero concentration entries via Proposition 5.2, and the
compact description `Σ⁻¹ ∈ S⁺(G)`); Proposition 3.1, p. 29 (a strictly positive continuous joint
density satisfies (C5)); §3.2.1, p. 32 (the pairwise (P), local (L) and global (G) Markov
properties) and Proposition 3.4 / Theorem 3.7, pp. 33–35 (the hierarchy, and its collapse for a
positive density) (`Lauritzen §5.2`, `Lauritzen §3.1`, `Lauritzen §3.2.1`).

**Proof formalization notes.**

*Book vs Lean, symmetry.* Lauritzen's `S(G)` requires the matrices to be symmetric and `S⁺(G)`
additionally positive definite. Over `ℝ`, `Matrix.PosDef` already carries
`Matrix.IsHermitian`, which is symmetry (`Matrix.conjTranspose_eq_transpose_of_trivial`), so
`concentrationSet` states positive definiteness plus the zero pattern and the symmetry is
inherited — not dropped.

*Book vs Lean, the graph.* `SimpleGraph ι` is irreflexive and symmetric, matching Lauritzen's
undirected `G = (Γ, E)`; the zero constraint is quantified over `γ ≠ μ` so the diagonal — where
`k_{γγ} > 0` always — is untouched, exactly as in the book ("for all pairs `γ, μ` which are not
adjacent").

*Book vs Lean, `IsPairwiseMarkov`.* The area's named Markov-property predicates are not yet
available in this branch, so the pairwise and local properties are stated **unfolded**, in the
`CondIndepCoords` vocabulary of `Core.Coordinates`. They are definitionally the (P) and (L) of
Lauritzen §3.2.1 and should be restated as `IsPairwiseMarkov` / `IsLocalMarkov` when those land;
the same applies to `condIndepCoords_of_separates`, whose separation hypothesis is spelled out
inline (every walk from `A` to `B` meets `C`) rather than referring to a `Separates` predicate
this branch cannot see.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| pairwise Markov, both directions | `condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` — Prop. 5.2 (`Gaussian.Precision`) |
| `Σ` regular from `Σ⁻¹` regular | `Matrix.posDef_inv_iff` (`LinearAlgebra/Matrix/PosDef.lean:499`) |
| a Gaussian law determines its covariance (for `mem_..._iff` and `SeparatesTarget`) | `covMatrix_multivariateGaussian` (`ForMathlib.CovarianceMatrix`) + `meanVec_multivariateGaussian` |
| `N(m, S)` is a probability measure | `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure` (instance; `Gaussian/Basic.lean:50`) |
| the feasibility witness `Σ = 1` | `Matrix.PosDef.one`, `Matrix.inv_one`, `Matrix.one_apply_ne` |
| graph extensionality for `SeparatesTarget` | `SimpleGraph.ext` on `Adj` (the diagonal is covered by `SimpleGraph.irrefl`) |
| (C5) from a positive density | Lauritzen Proposition 3.1, p. 29; for the Gaussian the density is `ProbabilityTheory.multivariateGaussian` against Lebesgue measure — the pin has no Lebesgue-density lemma for it, so the intended route is the block-splitting one: reduce to `multivariateGaussian_fromBlocks_prod` (G2.9) on the reindexed sum space, where the two premises force the two off-diagonal covariance blocks to vanish simultaneously |
| pairwise ⇒ local ⇒ global | the abstract combinators of `Core.Semigraphoid` (`union_iff`, `weakUnion_sdiff`, `decomposition_subset`) fed by `condIndepCoords_intersection_of_disjoint` |

**Bibliographic comments.** Covariance selection is A. P. Dempster's, "Covariance selection,"
*Biometrics* **28** (1972), 157–175 — the name, the model class `S⁺(G)` and the maximum
likelihood theory. The Markov-property hierarchy for undirected graphs and its collapse under a
positive density is J. N. Darroch, S. L. Lauritzen and T. P. Speed, "Markov fields and log-linear
interaction models for contingency tables," *Ann. Statist.* **8** (1980), 522–539, and
J. M. Hammersley and P. Clifford's unpublished 1971 manuscript; the graphoid axiomatics is
J. Pearl's, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section ConcentrationSet

/-- **Lauritzen's `S⁺(G)`** (§5.2, p. 132): the positive definite matrices whose off-diagonal
entries vanish at every non-edge of `G`.

The book asks for `S(G)` to consist of *symmetric* matrices and takes `S⁺(G)` to be its positive
definite elements; over `ℝ`, `Matrix.PosDef` already includes `Matrix.IsHermitian`, which is
symmetry, so nothing is dropped. The constraint is quantified over `γ ≠ μ`, leaving the diagonal
free — as in the book.

Edge behaviour: for the complete graph this is all of the positive definite cone (the saturated
model); for the empty graph it is the diagonal positive definite matrices. -/
def concentrationSet (G : SimpleGraph ι) : Set (Matrix ι ι ℝ) :=
  {A | A.PosDef ∧ ∀ i j, i ≠ j → ¬ G.Adj i j → A i j = 0}

/-- Adding edges enlarges `S⁺(G)`: fewer zero constraints. -/
theorem concentrationSet_mono {G H : SimpleGraph ι}
    -- USER-INPUT: `G` is a subgraph of `H`; Lauritzen §5.2, p. 132
    (hGH : G ≤ H) :
    concentrationSet G ⊆ concentrationSet H := by
  sorry

/-- A regular concentration matrix comes from a regular covariance matrix. -/
theorem posDef_of_precisionMatrix_posDef {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: `Matrix.inv` is junk-valued at singular matrices, so this is the statement that
    -- the junk value `0` is not positive definite; `Matrix.posDef_inv_iff`
    (h : (precisionMatrix S).PosDef) :
    S.PosDef := by
  sorry

end ConcentrationSet

section Model

/-- **The Gaussian graphical model / covariance selection model** with graph `G` (Lauritzen §5.2,
pp. 131–132), in the book's own compact form: `Y ∼ N_{|Γ|}(ξ, Σ)` with `Σ⁻¹ ∈ S⁺(G)`.

This is the fiber of a `StatisticalModels.Constraint` model with parameter space
`Θ := SimpleGraph ι` and sample space `𝓧 := EuclideanSpace ℝ ι`: it is a *set* of laws, one
constraint per graph, not a single law per parameter.

Edge behaviour: the membership condition is stated on `precisionMatrix S`, which forces `S` to be
regular (`posDef_of_precisionMatrix_posDef`), so the junk regimes of both `Matrix.inv` and
`multivariateGaussian` (a Dirac mass off the positive semidefinite cone) are excluded — a Dirac
law is never a member. -/
def gaussianGraphicalModel (G : SimpleGraph ι) : Set (Measure (EuclideanSpace ℝ ι)) :=
  {P | ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ),
        precisionMatrix S ∈ concentrationSet G ∧ P = multivariateGaussian m S}

/-- Unfolded membership: a law is in the model iff it is a regular Gaussian whose concentration
matrix has the prescribed zeros. -/
theorem mem_gaussianGraphicalModel_iff {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)} :
    P ∈ gaussianGraphicalModel G
      ↔ ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ), S.PosDef ∧
          (∀ i j, i ≠ j → ¬ G.Adj i j → precisionMatrix S i j = 0) ∧
          P = multivariateGaussian m S := by
  sorry

/-- Membership for an explicitly given regular Gaussian. -/
theorem multivariateGaussian_mem_gaussianGraphicalModel_iff {G : SimpleGraph ι}
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) :
    multivariateGaussian m S ∈ gaussianGraphicalModel G
      ↔ ∀ i j, i ≠ j → ¬ G.Adj i j → precisionMatrix S i j = 0 := by
  sorry

/-- Adding edges enlarges the model — a covariance selection model is a *restriction*. This
monotonicity is why the book's model does not identify its own graph; see the module docstring. -/
theorem gaussianGraphicalModel_mono {G H : SimpleGraph ι}
    -- USER-INPUT: `G` is a subgraph of `H`; Lauritzen §5.2, p. 132
    (hGH : G ≤ H) :
    gaussianGraphicalModel G ⊆ gaussianGraphicalModel H := by
  sorry

/-- Feasibility of the constraint model: every graph admits a compatible law (take `Σ = I`, whose
concentration matrix `I` satisfies every zero constraint). -/
theorem fibersNonempty_gaussianGraphicalModel :
    FibersNonempty (gaussianGraphicalModel (ι := ι)) := by
  sorry

/-- Every compatible law is a probability measure. -/
theorem fibersProbability_gaussianGraphicalModel :
    FibersProbability (gaussianGraphicalModel (ι := ι)) := by
  sorry

/-- The **saturated** fibers: the laws whose concentration zero pattern is *exactly* the
non-edge set of `G`. Lauritzen's model asks for `⊆`; this asks for `=`.

Edge behaviour: the fibers are pairwise disjoint and each is nonempty, so this is the constraint
model whose parameter — the graph — is identified (`separatesTarget_gaussianGraphicalModelExact`).
It is *not* the book's model class: it is not closed under limits and is not a natural object for
maximum likelihood, which is exactly why Lauritzen states the model with `⊆`. -/
def gaussianGraphicalModelExact (G : SimpleGraph ι) : Set (Measure (EuclideanSpace ℝ ι)) :=
  {P | ∃ (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ), S.PosDef ∧
        (∀ i j, i ≠ j → (precisionMatrix S i j = 0 ↔ ¬ G.Adj i j)) ∧
        P = multivariateGaussian m S}

theorem gaussianGraphicalModelExact_subset (G : SimpleGraph ι) :
    gaussianGraphicalModelExact G ⊆ gaussianGraphicalModel G := by
  sorry

/-- **The conditional independence graph is identified.** Two graphs whose saturated fibers share
a law are equal: by Proposition 5.2 the law's concentration zero pattern is its set of
conditional independences, and the saturated fiber pins the graph to be exactly that pattern.

Stated with the `Constraint` carrier of `StatisticalModels.Constraint.Defs`, with `Θ` the graphs
and the target `ψ = id`. Compare `gaussianGraphicalModel_mono`: the *book's* model is monotone
and hence does **not** separate its graph. -/
theorem separatesTarget_gaussianGraphicalModelExact :
    SeparatesTarget (gaussianGraphicalModelExact (ι := ι)) id := by
  sorry

end Model

section MarkovProperties

/-- **HEADLINE — the pairwise Markov property** (Lauritzen §5.2, p. 131: the covariance selection
model "is given by assuming that `Y` follows a multivariate normal distribution which obeys the
undirected pairwise Markov property with respect to `G`"; §3.2.1, p. 32, property (P)).

Every law of the model satisfies `Y_γ ⫫ Y_μ ∣ Y_{Γ∖{γ,μ}}` for every pair of distinct
non-adjacent vertices. Immediate from Proposition 5.2 — this is the sense in which the zero
pattern of `K` *is* the graph.

The conclusion is the (P) of Lauritzen §3.2.1 written out in the `CondIndepCoords` vocabulary;
see the module docstring for why the area's `IsPairwiseMarkov` predicate is not used. -/
theorem condIndepCoords_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) {i j : ι}
    -- USER-INPUT: distinct vertices; Lauritzen §3.2.1, p. 32, property (P)
    (hij : i ≠ j)
    -- USER-INPUT: a non-edge of `G`; Lauritzen §3.2.1, p. 32, property (P)
    (hadj : ¬ G.Adj i j) :
    CondIndepCoords P gaussianCoords {i} {j} ({i, j} : Finset ι)ᶜ := by
  sorry

/-- **The definition and the parametrisation agree** (Lauritzen §5.2, p. 131: "It follows from
Proposition 5.2 that this is equivalent to assuming the quadratic interactions `k_{γμ}` to be
equal to zero for all pairs `γ, μ` which are not adjacent in `G`").

A regular Gaussian belongs to the covariance selection model of `G` **iff** it is pairwise Markov
with respect to `G`. The `←` direction is the one that needs Proposition 5.2 in its nontrivial
direction. -/
theorem multivariateGaussian_mem_gaussianGraphicalModel_iff_pairwise {G : SimpleGraph ι}
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) :
    multivariateGaussian m S ∈ gaussianGraphicalModel G
      ↔ ∀ i j, i ≠ j → ¬ G.Adj i j →
          CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j}
            ({i, j} : Finset ι)ᶜ := by
  sorry

/-- **Lauritzen Proposition 3.1 at the Gaussian** (p. 29): a strictly positive continuous joint
density satisfies (C5), *intersection*. A regular multivariate normal has such a density
(Lauritzen §5.2, p. 131: "Since the density is positive and continuous, this implies the global
and local Markov properties"), so its conditional independence relation satisfies

`X_A ⫫ X_B ∣ (X_C, X_D)` and `X_A ⫫ X_D ∣ (X_C, X_B)` ⟹ `X_A ⫫ (X_B, X_D) ∣ X_C`

for **pairwise disjoint** blocks. The disjointness is Lauritzen's own standing hypothesis on
(C1)–(C5) and is *not* removable: see the module docstring for the `B = D`, `C = ∅` refutation of
the unrestricted form. This is the missing ingredient that turns pairwise Markov into local and
global Markov. -/
theorem condIndepCoords_intersection_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular — this is what makes the density positive and continuous;
    -- Lauritzen Prop. 3.1, p. 29 and §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of (C5); Lauritzen §3.1, p. 30
    (h₁ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D))
    -- USER-INPUT: second premise of (C5); Lauritzen §3.1, p. 30
    (h₂ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A D (C ∪ B)) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C := by
  sorry

/-- **The local Markov property** (Lauritzen §3.2.1, p. 32, property (L)):
`Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`, where `bd(γ)` is the neighbourhood of `γ` and
`cl(γ) = {γ} ∪ bd(γ)` its closure.

Lauritzen obtains (L) from (P) for a positive density (§5.2, p. 131); the intended route is
pairwise Markov plus `condIndepCoords_intersection_of_disjoint`, assembled by the abstract
combinators of `Core.Semigraphoid`. -/
theorem condIndepCoords_local_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    -- LEAN-ONLY: needed to form `G.neighborFinset`, the `Finset` version of `bd(γ)`
    [DecidableRel G.Adj] {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) (i : ι) :
    CondIndepCoords P gaussianCoords {i}
      (Finset.univ \ insert i (G.neighborFinset i)) (G.neighborFinset i) := by
  sorry

/-- **The global Markov property** (Lauritzen §3.2.1, p. 32, property (G); §5.2, p. 131: "Since
the density is positive and continuous, this implies the global and local Markov properties"):
if every path in `G` from `A` to `B` meets `C`, then `Y_A ⫫ Y_B ∣ Y_C`.

Separation is spelled out inline — every walk from a vertex of `A` to a vertex of `B` visits a
vertex of `C` — rather than through the area's `Separates` predicate, which this branch cannot
see; it should be restated in those terms when the graph lane lands. Later lane: the intended
route is pairwise Markov plus `condIndepCoords_intersection_of_disjoint` through the abstract
`Core.Semigraphoid` combinators (Lauritzen Theorem 3.7), not a fresh Gaussian computation. -/
theorem condIndepCoords_of_separates {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) {A B C : Finset ι}
    -- USER-INPUT: the three blocks are disjoint, as in Lauritzen §3.2.1, p. 32
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    -- USER-INPUT: `C` separates `A` from `B` in `G` — every walk between the two blocks meets
    -- the separator; Lauritzen §3.2.1, p. 32, property (G)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∀ w : G.Walk a b, ∃ c ∈ C, c ∈ w.support) :
    CondIndepCoords P gaussianCoords A B C := by
  sorry

end MarkovProperties

end StatLean.StatisticalModels.GraphicalModels
