/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan, David Jacho-Chávez
-/
import Mathlib.Probability.Independence.Basic

/-!
# Dependency graphs

Let $(X_i)_{i \in \iota}$ be a finite family of real random variables on a probability space.
A **dependency graph** for the family is a reflexive, symmetric relation $G$ on $\iota$ such
that, whenever two index sets $A, B \subseteq \iota$ are joined by no edge of $G$, the tuples
$(X_a)_{a \in A}$ and $(X_b)_{b \in B}$ are independent. This file introduces the structure
`DepGraph` recording such a relation together with the measurability of each $X_i$, and the
closed neighbourhood $N(i) = \{j : G\,i\,j\}$ (`DepGraph.nbhd`).

Janson's maximal degree $M$ of the graph is the largest number of neighbours of a vertex other
than itself; since `DepGraph.nbhd` is the closed neighbourhood, it is bounded through
`#((D.nbhd i).erase i) ≤ M`.

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312:
the Definition on p. 306, used in the hypotheses of Theorem 2.

**Provenance.** The structure `DepGraph` and the lemmas `DepGraph.mem_nbhd_iff` and
`DepGraph.self_mem_nbhd` are adapted from the file
`Causalean/Mathlib/Probability/SteinMethod/DepGraphCLT.lean` of CausalSmith, the Causalean
library of Jiyuan Tan (https://github.com/Jiyuan-Tan/CausalSmith), Copyright (c) 2026 Jiyuan
Tan, licensed under the Apache License, Version 2.0. Changes: the namespace, the docstrings,
and the omission of every other declaration of the original file.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

/-- A **dependency graph** for a family `X : ι → Ω → ℝ` of real random variables under the
measure `μ`: an adjacency relation `G` on the index set that is reflexive and symmetric, such
that each `X i` is measurable and any two index sets joined by no edge of `G` carry independent
variable tuples. -/
structure DepGraph (X : ι → Ω → ℝ) (μ : Measure Ω) where
  /-- The dependency relation. -/
  G : ι → ι → Prop
  /-- Decidability of adjacency (for the neighbourhood `Finset`). -/
  decG : DecidableRel G
  /-- Each index depends on itself. -/
  refl : ∀ i, G i i
  /-- Symmetry of the dependency relation. -/
  symm : ∀ i j, G i j → G j i
  /-- Each variable in the family is measurable. -/
  meas : ∀ i, Measurable (X i)
  /-- Non-adjacent index sets carry independent variable tuples. -/
  indep : ∀ A B : Finset ι, (∀ a ∈ A, ∀ b ∈ B, ¬ G a b) →
    IndepFun (fun ω => fun k : A => X k ω) (fun ω => fun k : B => X k ω) μ

namespace DepGraph

variable {X : ι → Ω → ℝ} {μ : Measure Ω} (D : DepGraph X μ)

/-- The **closed dependency neighbourhood** `N i = {j | G i j}` of an index `i`: the finite set
of all indices adjacent to `i`, including `i` itself. -/
noncomputable def nbhd (i : ι) : Finset ι := by
  letI := D.decG; exact Finset.univ.filter (fun j => D.G i j)

/-- Membership in the neighbourhood is exactly adjacency. -/
theorem mem_nbhd_iff {i j : ι} : j ∈ D.nbhd i ↔ D.G i j := by
  simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Each index lies in its own neighbourhood. -/
theorem self_mem_nbhd (i : ι) : i ∈ D.nbhd i := D.mem_nbhd_iff.mpr (D.refl i)

end DepGraph

end StatLean.AsymptoticStatistics
