import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.Compact

/-!
# Weak compactness of the class of `[0,1]`-valued functions — ForMathlib brick

Over a **finite** measure `μ`, the set of (a.e.) `[0,1]`-valued elements of `L²(μ)` is convex,
norm-bounded and norm-closed, hence **weakly compact**; intersecting it with finitely many
linear (moment) constraints `⟪gᵢ, f⟫ = cᵢ` keeps it compact, and a linear functional therefore
attains its maximum on the constrained class. That existence statement is the analytic engine
behind every "there exists an optimal test subject to `m` side conditions" argument.

This file provides:

* `testClassL2 μ` — the `[0,1]`-valued elements of `L²(μ)`;
* `constrainedTestClassL2 μ g c` — the same, cut by the constraints `⟪gᵢ, f⟫ = cᵢ`;
* `toWeakDualL2 μ` — the Fréchet–Riesz embedding `f ↦ ⟪f, ·⟫` of `L²(μ)` into
  `WeakDual ℝ (L²(μ))`, in which the weak topology of `L²` is the ambient weak-* topology;
* compactness of the images of the two classes, and `exists_max_inner_of_constraints`.

**Packaging note.** Mathlib has the Banach–Alaoglu theorem for the weak-* topology on a dual
space (`WeakDual.isCompact_closedBall`), but no separate carrier for "the weak topology on a
Hilbert space". We therefore transport the class along the Fréchet–Riesz isometry
`InnerProductSpace.toDual` and state compactness of the *image* in `WeakDual ℝ (L²(μ))`. Since
`InnerProductSpace.toDual` and `StrongDual.toWeakDual` are both bijections, this loses nothing:
the image determines the class, and `exists_max_inner_of_constraints` — the statement the
consumers actually use — is phrased back in `L²` with no weak-dual vocabulary at all.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.6 (A Generalization of the Fundamental Lemma), supporting material for
Theorem 3.6.1: weak compactness of the class of `[0,1]`-valued test functions. (`TSH4 §3.6 Thm
3.6.1`.)

**Proof formalization notes.**
* Intended route for `isCompact_toWeakDualL2_image_testClass`: (i) `μ` finite gives
  `‖f‖₂ ≤ √(μ univ)` for every `f` in the class, so the image sits inside a closed ball, which
  is weak-* compact by `WeakDual.isCompact_closedBall` (`ProperSpace ℝ`); (ii) the image is
  weak-* closed, because `toWeakDualL2` is *surjective* (Fréchet–Riesz) and the class is cut
  out by the weak-* closed conditions `0 ≤ L h` and `L h ≤ ⟪1, h⟫` ranging over the nonnegative
  `h ∈ L²(μ)` — each an intersection of preimages of closed half-lines under the continuous
  evaluations `L ↦ L h` (note `1 ∈ L²(μ)` because `μ` is finite); (iii) conclude with
  `IsCompact.of_isClosed_subset`. This avoids needing Mazur's theorem ("convex + norm-closed
  ⇒ weakly closed") explicitly.
* The constrained class adds `⋂ i, {L | L (g i) = c i}`, closed for the same reason; the index
  type is arbitrary (no finiteness needed for compactness — finiteness enters only when the
  constraints are produced by a finite family of moment conditions).
* `exists_max_inner_of_constraints` then applies `IsCompact.exists_isMaxOn` to the continuous
  evaluation at `h` and transports the maximizer back along the injective `toWeakDualL2`.
* Everything is stated for the real field; `⟪·,·⟫_ℝ` is the `InnerProductSpace`-scoped
  notation, and on real `L²` it reduces to `∫ f·g dμ` (see `toWeakDualL2_apply_eq_integral`;
  recall that `RCLike.inner_apply` produces the factors in the opposite order).

**Bibliographic comments.** Weak-* compactness of the closed unit ball of a dual space is the
Banach–Alaoglu theorem (S. Banach, *Théorie des opérations linéaires*, Warszawa, 1932, for the
separable case; L. Alaoglu, "Weak topologies of normed linear spaces," *Ann. of Math.* **41**
(1940), 252–267, in general). The self-duality of Hilbert space used to transport it is the
Fréchet–Riesz representation theorem (F. Riesz, *C. R. Acad. Sci. Paris* **144** (1907),
1409–1411; M. Fréchet, *ibid.*, 1414–1416). Its use to produce optimal tests under finitely
many side conditions is the generalized-fundamental-lemma argument of J. Neyman and
E. S. Pearson ("On the problem of the most efficient tests of statistical hypotheses,"
*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **`L²` test class**: the (a.e.) `[0,1]`-valued elements of `L²(μ)`. These are exactly
the critical functions of the testing theory, viewed in `L²`. -/
def testClassL2 (μ : Measure 𝓧) : Set (Lp ℝ 2 μ) :=
  {f | (0 : 𝓧 → ℝ) ≤ᵐ[μ] ⇑f ∧ ⇑f ≤ᵐ[μ] (1 : 𝓧 → ℝ)}

/-- The **constrained `L²` test class**: `[0,1]`-valued elements of `L²(μ)` satisfying the
linear (moment) side conditions `⟪gᵢ, f⟫ = cᵢ`. The index type is arbitrary. -/
def constrainedTestClassL2 (μ : Measure 𝓧) {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) :
    Set (Lp ℝ 2 μ) :=
  testClassL2 μ ∩ {f | ∀ i, ⟪g i, f⟫_ℝ = c i}

/-- The **Fréchet–Riesz embedding** of `L²(μ)` into its weak dual, `f ↦ ⟪f, ·⟫`. The weak
topology of `L²(μ)` is the topology induced from `WeakDual ℝ (L²(μ))` along this map. -/
noncomputable def toWeakDualL2 (μ : Measure 𝓧) (f : Lp ℝ 2 μ) : WeakDual ℝ (Lp ℝ 2 μ) :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) f)

/-- The embedding evaluates as the inner product. -/
theorem toWeakDualL2_apply (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    toWeakDualL2 μ f g = ⟪f, g⟫_ℝ := by
  sorry

/-- On real `L²` the embedding evaluates as an integral: the moment functionals
`f ↦ ∫ f·g dμ` are exactly the evaluations of the weak dual. -/
theorem toWeakDualL2_apply_eq_integral (μ : Measure 𝓧) (f g : Lp ℝ 2 μ) :
    toWeakDualL2 μ f g = ∫ x, f x * g x ∂μ := by
  sorry

/-- **Weak continuity of the moment functionals**: `f ↦ ⟪g, f⟫` is continuous for the weak
topology, in the weak-dual packaging. -/
theorem continuous_eval_weakDual (μ : Measure 𝓧) (g : Lp ℝ 2 μ) :
    Continuous fun L : WeakDual ℝ (Lp ℝ 2 μ) => L g := by
  sorry

/-- **Moment-constraint slices are closed**: a level set of a moment functional is weakly
closed. -/
theorem isClosed_setOf_eval_eq (μ : Measure 𝓧) (g : Lp ℝ 2 μ) (c : ℝ) :
    IsClosed {L : WeakDual ℝ (Lp ℝ 2 μ) | L g = c} := by
  sorry

/-- **Weak compactness of the test class** over a finite measure. -/
theorem isCompact_toWeakDualL2_image_testClass (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] :
    IsCompact (toWeakDualL2 μ '' testClassL2 μ) := by
  sorry

/-- **Weak compactness of the constrained test class** over a finite measure: the moment
constraints cut a closed subset out of a compact set. -/
theorem isCompact_toWeakDualL2_image_constrained (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) :
    IsCompact (toWeakDualL2 μ '' constrainedTestClassL2 μ g c) := by
  sorry

/-- **Existence of an optimal constrained test**: a linear functional attains its maximum over
the (nonempty) class of `[0,1]`-valued `L²` functions meeting the moment constraints.

Stated entirely inside `L²`: the weak-dual packaging is an implementation detail of the
proof. -/
theorem exists_max_inner_of_constraints (μ : Measure 𝓧)
    -- USER-INPUT: the dominating measure is finite; without it the class is unbounded in `L²`
    [IsFiniteMeasure μ] {ι : Type*} (g : ι → Lp ℝ 2 μ) (c : ι → ℝ) (h : Lp ℝ 2 μ)
    -- USER-INPUT: the constraints are attainable; Neyman–Pearson (1933)
    (hne : (constrainedTestClassL2 μ g c).Nonempty) :
    ∃ f ∈ constrainedTestClassL2 μ g c,
      ∀ f' ∈ constrainedTestClassL2 μ g c, ⟪h, f'⟫_ℝ ≤ ⟪h, f⟫_ℝ := by
  sorry

end StatLean.HypothesisTesting
