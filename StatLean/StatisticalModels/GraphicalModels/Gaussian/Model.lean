import StatLean.StatisticalModels.GraphicalModels.Gaussian.Regression
import StatLean.StatisticalModels.GraphicalModels.Gaussian.PartialCorrelation
import StatLean.StatisticalModels.GraphicalModels.Undirected.Markov
import StatLean.StatisticalModels.Constraint.Defs

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
* **`isPairwiseMarkov_of_mem_gaussianGraphicalModel` (HEADLINE)** — a law in the model satisfies
  `Undirected.Markov.IsPairwiseMarkov G` for the relation `CondIndepCoords P gaussianCoords`;
* `multivariateGaussian_mem_gaussianGraphicalModel_iff_pairwise` — and conversely, so that
  Lauritzen's *definition* (pairwise Markov) and the p. 132 *parametrisation* (zeros of `K`) are
  one and the same model;
* **`isGraphoid_condIndepCoords_multivariateGaussian`** — Lauritzen **Proposition 3.1 at the
  Gaussian**: the density is positive and continuous, so the conditional-independence relation of
  a regular normal is a **graphoid**, i.e. an instance of `Core.Semigraphoid.IsGraphoid`. This is
  the Gaussian's contribution to the abstraction, and it is what turns pairwise into local and
  global through `Undirected.Markov`;
* `condIndepCoords_weakUnion_of_disjoint`, `condIndepCoords_contraction_of_disjoint`,
  `condIndepCoords_intersection_of_disjoint` — the three named sub-lemmas that instance needs
  ((C3), (C4), (C5)); symmetry and decomposition come free from `Core.Coordinates`;
* `isGlobalMarkov_of_mem_gaussianGraphicalModel` (later lane) — `IsGlobalMarkov`, i.e. (G),
  obtained from the graphoid instance through Theorem 3.7;
* `isLocalMarkov_of_mem_gaussianGraphicalModel` — `IsLocalMarkov`, i.e. (L)
  `Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`, obtained from (G) by pure graph separation. It is stated
  *after* (G) because that is the direction of the dependency: `IsGlobalMarkov ⇒ IsLocalMarkov`
  is `Undirected.Markov`'s `globalMarkov_implies_localMarkov`, so nothing here re-walks the
  hierarchy.

## Note: `SeparatesTarget` and why the book's model does not identify its graph

`gaussianGraphicalModel` is monotone in `G` (a zero constraint is a *restriction*), so
`gaussianGraphicalModel G ⊆ gaussianGraphicalModel H` whenever `G ≤ H`, and in particular every
model is contained in the saturated one. Hence `SeparatesTarget gaussianGraphicalModel id` is
**false** for `|Γ| ≥ 2` and is deliberately not stated. What *is* true — and is the
identifiability content of covariance selection — is that the *exact* zero pattern determines the
graph: `SeparatesTarget gaussianGraphicalModelExact id`. This is the honest reading of "the
conditional independence graph of a regular Gaussian is identified from its law".

## Note: why `IsGraphoid`'s disjointness hypotheses are constitutive, not bureaucracy

`Core.Semigraphoid`'s axiom fields each carry pairwise disjointness of the blocks occurring in
them, matching Lauritzen, who states (C1)–(C5) for *disjoint* subsets. That is not a stylistic
choice, and the Gaussian is the witness: **without** the disjointness the structure is
unsatisfiable here. Take `B = D` and `C = ∅` in the intersection field; the disjointness-free
version would read `ci A B B → ci A B B → ci A B ∅`, whose premises hold trivially (conditioning
on `X_B` makes `X_B` degenerate) while the conclusion asserts *unconditional* independence of
`X_A` and `X_B` — false for any regular Gaussian with a nonzero covariance entry. The amended
field blocks this: `Disjoint B D` at `B = D` forces `B = D = ∅`, and `ci A ∅ ∅` is harmless. So
`isGraphoid_condIndepCoords_multivariateGaussian` below is stateable exactly because the
disjointness is part of the axioms — the counterexample is the reason it must stay there.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**: §5.2 "Covariance selection models", pp. 131–132
(the definition, the equivalence with zero concentration entries via Proposition 5.2, and the
compact description `Σ⁻¹ ∈ S⁺(G)`); Proposition 3.1, p. 29 (a strictly positive continuous joint
density satisfies (C5)); §3.2, p. 32 — the pairwise (P), local (L) and global (G) Markov
properties, all three **unnumbered** definitions; and Proposition 3.4 / Theorem 3.7, pp. 33–35
(the hierarchy, and its collapse for a positive density) (`Lauritzen §5.2`, `Lauritzen §3.1`,
`Lauritzen §3.2`). Page numbers and item kinds follow `notes/factor_graphical/books.md`.

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

*No re-statement of the Markov vocabulary.* The three Markov properties are `Undirected.Markov`'s
`IsPairwiseMarkov` / `IsLocalMarkov` / `IsGlobalMarkov`, instantiated at the abstract relation
`ci := CondIndepCoords P gaussianCoords`; separation is `Core.Separation.Separates`, consumed
*inside* `IsGlobalMarkov` and never re-spelled here. Nothing in this file redefines a Markov
property, a separation predicate, or a graphoid axiom. The three `Disjoint` hypotheses that
`IsGlobalMarkov` carries are part of its definition, so its Gaussian instance takes no
`Disjoint` arguments of its own.

*Landing on the nose.* `IsPairwiseMarkov` conditions on `Finset.univ \ {i, j}`, so
`Gaussian.Precision`'s Proposition 5.2 is stated with that same expression rather than
`({i, j} : Finset ι)ᶜ`; the instantiation is then syntactic, with no `Finset.compl_eq_univ_sdiff`
rewriting in between.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| pairwise Markov, both directions | `condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` — Prop. 5.2 (`Gaussian.Precision`) |
| `Σ` regular from `Σ⁻¹` regular | `Matrix.posDef_inv_iff` (`LinearAlgebra/Matrix/PosDef.lean:499`) |
| a Gaussian law determines its covariance (for `mem_..._iff` and `SeparatesTarget`) | `covMatrix_multivariateGaussian` (`ForMathlib.CovarianceMatrix`) + `meanVec_multivariateGaussian` |
| `N(m, S)` is a probability measure | `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure` (instance; `Gaussian/Basic.lean:50`) |
| the feasibility witness `Σ = 1` | `Matrix.PosDef.one`, `Matrix.inv_one`, `Matrix.one_apply_ne` |
| graph extensionality for `SeparatesTarget` | `SimpleGraph.ext` on `Adj` (the diagonal is covered by `SimpleGraph.irrefl`) |
| (C1) symmetry, (C2) decomposition of the Gaussian relation | `CondIndepCoords.symm`, `CondIndepCoords.decomposition` (`Core.Coordinates`) — already available, do **not** re-prove |
| (C3), (C4), (C5) for the Gaussian relation | the three named sub-lemmas of this file; (C5) is Lauritzen Proposition 3.1, p. 29. The pin has no Lebesgue-density lemma for `multivariateGaussian`, so the intended route is block-splitting rather than the book's density argument: reduce to `multivariateGaussian_fromBlocks_prod` (G2.9) on the reindexed sum space, where the premises force the relevant off-diagonal covariance blocks to vanish simultaneously |
| (G) ⇒ (L), (L) ⇒ (P), (G) ⇒ (P) | `Undirected.Markov.globalMarkov_implies_localMarkov`, `localMarkov_implies_pairwiseMarkov`, `globalMarkov_implies_pairwiseMarkov` — Lauritzen Proposition 3.4; **never** re-derive the hierarchy per model class |
| (P) ⇒ (G) | `Undirected.Markov.pairwiseMarkov_implies_globalMarkov` (Theorem 3.7, Pearl–Paz) fed by `isGraphoid_condIndepCoords_multivariateGaussian` — this is the whole content of "since the density is positive and continuous, this implies the global and local Markov properties" |

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
    SeparatesTarget (gaussianGraphicalModelExact (ι := ι))
      (id : SimpleGraph ι → SimpleGraph ι) := by
  sorry

end Model

section MarkovProperties

/-- **HEADLINE — the pairwise Markov property** (Lauritzen §5.2, p. 131: the covariance selection
model "is given by assuming that `Y` follows a multivariate normal distribution which obeys the
undirected pairwise Markov property with respect to `G`"; §3.2, p. 32, property (P)).

Stated as an instance of `Undirected.Markov.IsPairwiseMarkov` at the abstract relation
`ci := CondIndepCoords P gaussianCoords`. Immediate from Proposition 5.2 — this is the sense in
which the zero pattern of `K` *is* the graph. `IsPairwiseMarkov` already quantifies over distinct
non-adjacent pairs and conditions on `Finset.univ \ {i, j}`, which is exactly the shape
`condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` produces. -/
theorem isPairwiseMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsPairwiseMarkov G (CondIndepCoords P gaussianCoords) := by
  sorry

/-- **The definition and the parametrisation agree** (Lauritzen §5.2, p. 131: "It follows from
Proposition 5.2 that this is equivalent to assuming the quadratic interactions `k_{γμ}` to be
equal to zero for all pairs `γ, μ` which are not adjacent in `G`").

A regular Gaussian belongs to the covariance selection model of `G` **iff** it is pairwise Markov
with respect to `G`. The `←` direction is the one that needs Proposition 5.2 in its nontrivial
direction. Together with `isPairwiseMarkov_of_mem_gaussianGraphicalModel` this says the model
class is *defined* by (P), which is how Lauritzen introduces it. -/
theorem multivariateGaussian_mem_gaussianGraphicalModel_iff_pairwise {G : SimpleGraph ι}
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) :
    multivariateGaussian m S ∈ gaussianGraphicalModel G
      ↔ IsPairwiseMarkov G (CondIndepCoords (multivariateGaussian m S) gaussianCoords) := by
  sorry

/-! ### Lauritzen Proposition 3.1 at the Gaussian — the graphoid instance

The Gaussian's contribution to the `Core.Semigraphoid` abstraction. (C1) and (C2) are already
available as `CondIndepCoords.symm` and `CondIndepCoords.decomposition`; the three sub-lemmas
below are the genuine debts, kept named rather than buried inside the instance so that the gap
structure stays visible. All three carry the book's pairwise disjointness of the blocks. -/

/-- **(C3), weak union, for the Gaussian** (Lauritzen §3.1, p. 29): `X_A ⫫ (X_B, X_D) ∣ X_C`
implies `X_A ⫫ X_B ∣ (X_C, X_D)`.

`Core.CondIndep` deliberately proves only (C1)–(C2) in full generality — weak union needs
essential uniqueness of disintegrations — so the Gaussian supplies this itself, by block
splitting rather than through the general calculus. -/
theorem condIndepCoords_weakUnion_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: the independence to be weakened; Lauritzen §3.1 (C3), p. 29
    (h : CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D) := by
  sorry

/-- **(C4), contraction, for the Gaussian** (Lauritzen §3.1, p. 29): `X_A ⫫ X_B ∣ (X_C, X_D)`
together with `X_A ⫫ X_D ∣ X_C` implies `X_A ⫫ (X_B, X_D) ∣ X_C`. -/
theorem condIndepCoords_contraction_of_disjoint
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular; Lauritzen §5.2, p. 131
    (hS : S.PosDef) {A B C D : Finset ι}
    -- USER-INPUT: Lauritzen states (C1)–(C5) for disjoint subsets; §3.1, p. 29
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    -- USER-INPUT: first premise of (C4); Lauritzen §3.1, p. 29
    (h₁ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A B (C ∪ D))
    -- USER-INPUT: second premise of (C4); Lauritzen §3.1, p. 29
    (h₂ : CondIndepCoords (multivariateGaussian m S) gaussianCoords A D C) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords A (B ∪ D) C := by
  sorry

/-- **(C5), intersection, for the Gaussian — Lauritzen Proposition 3.1** (p. 29): a strictly
positive continuous joint density satisfies intersection. A regular multivariate normal has such
a density (Lauritzen §5.2, p. 131: "Since the density is positive and continuous, this implies
the global and local Markov properties"), so

`X_A ⫫ X_B ∣ (X_C, X_D)` and `X_A ⫫ X_D ∣ (X_C, X_B)` ⟹ `X_A ⫫ (X_B, X_D) ∣ X_C`

for **pairwise disjoint** blocks. Two hypotheses do real work and neither is removable. The
disjointness is Lauritzen's own standing convention — see the module docstring for the
`B = D`, `C = ∅` counterexample that makes it constitutive. Regularity is what supplies the
positive density: (C5) fails outright for a degenerate law, by Lauritzen's `X = Y = Z`
counterexample on p. 30. -/
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

/-- **The conditional-independence relation of a regular Gaussian is a graphoid** — the Gaussian
instance of `Core.Semigraphoid.IsGraphoid`, i.e. Lauritzen **Proposition 3.1** (p. 29) applied to
the normal density, which §5.2 (p. 131) invokes when it says "since the density is positive and
continuous, this implies the global and local Markov properties".

This is the single object `Undirected.Markov` needs from the Gaussian side: with it,
`pairwiseMarkov_implies_globalMarkov` (Theorem 3.7, Pearl–Paz) and `markov_tfae` apply verbatim,
and no Markov implication has to be re-proved for this model class.

Assembly (no new mathematics): `symm := CondIndepCoords.symm`,
`decomposition := CondIndepCoords.decomposition` at `B ⊆ B ∪ D`, and the three named sub-lemmas
above for `weakUnion`, `contraction` and `intersection`. -/
theorem isGraphoid_condIndepCoords_multivariateGaussian
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    -- USER-INPUT: `Σ` regular — positivity and continuity of the density; Lauritzen Prop. 3.1,
    -- p. 29, and §5.2, p. 131
    (hS : S.PosDef) :
    IsGraphoid (CondIndepCoords (multivariateGaussian m S) gaussianCoords) := by
  sorry

/-- **The global Markov property** (Lauritzen §3.2, p. 32, property (G); §5.2, p. 131: "Since the
density is positive and continuous, this implies the global and local Markov properties"), as an
instance of `Undirected.Markov.IsGlobalMarkov`. Separation is `Core.Separation.Separates` and the
three disjointness conditions are part of that definition; nothing is restated here.

Later lane, and it carries **no debt of its own**: destructure `hP` into a regular
`multivariateGaussian m S`, then apply
`pairwiseMarkov_implies_globalMarkov G (isGraphoid_condIndepCoords_multivariateGaussian m hS)`
to `isPairwiseMarkov_of_mem_gaussianGraphicalModel hP`. The real content sits in Theorem 3.7 (in
`Undirected.Markov`) and in the graphoid instance above — which is exactly Lauritzen's own
argument, and not a fresh Gaussian computation. -/
theorem isGlobalMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsGlobalMarkov G (CondIndepCoords P gaussianCoords) := by
  sorry

/-- **The local Markov property** (Lauritzen §3.2, p. 32, property (L)):
`Y_γ ⫫ Y_{Γ∖cl(γ)} ∣ Y_{bd(γ)}`, as an instance of `Undirected.Markov.IsLocalMarkov`.

Carries **no debt of its own**: it is `globalMarkov_implies_localMarkov` applied to
`isGlobalMarkov_of_mem_gaussianGraphicalModel`, a step that is pure graph separation and uses no
property of `ci` at all. -/
theorem isLocalMarkov_of_mem_gaussianGraphicalModel {G : SimpleGraph ι}
    -- LEAN-ONLY: `IsLocalMarkov` is stated through `G.neighborFinset`, which needs the
    -- neighbourhoods to be `Finset`s
    [DecidableRel G.Adj] {P : Measure (EuclideanSpace ℝ ι)}
    -- USER-INPUT: a law of the covariance selection model; Lauritzen §5.2, p. 131
    (hP : P ∈ gaussianGraphicalModel G) :
    IsLocalMarkov G (CondIndepCoords P gaussianCoords) := by
  sorry

end MarkovProperties

end StatLean.StatisticalModels.GraphicalModels
