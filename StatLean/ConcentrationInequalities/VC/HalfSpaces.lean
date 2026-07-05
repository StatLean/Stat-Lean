import StatLean.ConcentrationInequalities.VC.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Radon

/-!
# VC dimension of half-spaces in ℝᵐ

The class of closed half-spaces
$\{x \in \mathbb{R}^m : \langle a, x\rangle \le b\}$ has VC dimension exactly
$$ \mathrm{vc}(\text{half-spaces in } \mathbb{R}^m) \;=\; m + 1, $$
and in particular half-planes in $\mathbb{R}^2$ have VC dimension $3$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.1, Example 8.3.5 (= Exercise 8.17;
half-spaces) and Example 8.3.3 (half-planes, the `m = 2` instance).

**Proof formalization notes.** Lower bound: the `(m+1)`-point set
`{0, e₀, …, e_{m−1}}` is shattered by the explicit witnesses
`a = ∑ᵢ (if eᵢ ∈ T then −1 else 1) • EuclideanSpace.single i 1` and
`b = if 0 ∈ T then 0 else −1/2` (inner products computed by
`EuclideanSpace.inner_single_left`; the design's witness was verified on
paper). Upper bound: any `(m+2)`-point set is affinely dependent
(`finrank_vectorSpan_le_iff_not_affineIndependent` + `Submodule.finrank_le`),
so `Convex.radon_partition` yields a point in the convex hulls of both cells
of a partition; a half-space realizing the corresponding labeling would put
that point in the disjoint convex sets `{⟨a,·⟩ ≤ b}` and `{b < ⟨a,·⟩}`
(`convex_halfSpace_le` / `convex_halfSpace_gt` + `convexHull_min`) —
contradiction. `Shatters.mono_right` extends "no `(m+2)`-set is shattered"
to `vcDim ≤ m + 1`. Example 8.3.3 is *derived* as the `m = 2`
instantiation, not re-proved. Constants: exact equality, no slack.
Named-sorry fallback of this work item: `not_shatters_halfSpaceClass` (the
Radon upper bound); the explicit lower-bound witness and the `vcDim`
assembly must close.

**Bibliographic comments.** The half-space computation is the classical
example of Vapnik–Chervonenkis theory (*Theory Probab. Appl.* 16 (1971),
264–280); the Radon-partition route to the upper bound follows J. Radon,
"Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten," *Math.
Ann.* 83 (1921), 113–115, as in HDP Exercise 8.17 and its solution sketch.
-/

namespace StatLean.ConcentrationInequalities

/-- The class of closed half-spaces `{x : ⟨a, x⟩ ≤ b}` in `ℝᵐ`
(HDP §8.3.1, Example 8.3.5). Edge behavior: `a = 0` is allowed, so `∅`
(`b < 0`) and `univ` (`b ≥ 0`) are members. -/
def halfSpaceClass (m : ℕ) : Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {S | ∃ (a : EuclideanSpace ℝ (Fin m)) (b : ℝ),
    S = {x : EuclideanSpace ℝ (Fin m) | inner ℝ a x ≤ b}}

open Classical in
/-- The `(m+1)`-point set `{0, e₀, …, e_{m−1}}` is shattered by half-spaces
(HDP §8.3.1, Example 8.3.5, lower bound; witness
`a i = if eᵢ ∈ T then −1 else 1`, `b = if 0 ∈ T then 0 else −1/2`). -/
theorem shatters_halfSpaceClass_simplex (m : ℕ) :
    Shatters (halfSpaceClass m)
      (insert (0 : EuclideanSpace ℝ (Fin m))
        (Finset.univ.image fun i : Fin m =>
          EuclideanSpace.single i (1 : ℝ))) := by
  sorry

/-- No `(m+2)`-point set is shattered by half-spaces in `ℝᵐ` (HDP §8.3.1,
Example 8.3.5, upper bound via Radon's partition: `(m+2)` points are
affinely dependent, and a point common to the two convex hulls cannot be
separated from itself). -/
theorem not_shatters_halfSpaceClass {m : ℕ}
    {Λ : Finset (EuclideanSpace ℝ (Fin m))}
    -- USER-INPUT: cardinality m + 2 (one above the claimed VC dimension);
    -- HDP §8.3.1, Example 8.3.5.
    (hcard : Λ.card = m + 2) :
    ¬ Shatters (halfSpaceClass m) Λ := by
  sorry

/-- **Half-spaces in ℝᵐ have VC dimension m + 1** (HDP §8.3.1,
Example 8.3.5 = Exercise 8.17). -/
theorem vcDim_halfSpaceClass (m : ℕ) :
    vcDim (halfSpaceClass m) = m + 1 := by
  sorry

/-- **Half-planes in ℝ² have VC dimension 3** (HDP §8.3.1, Example 8.3.3) —
derived as the `m = 2` instance of `vcDim_halfSpaceClass`, not
re-proved. -/
theorem vcDim_halfSpaceClass_two : vcDim (halfSpaceClass 2) = 3 := by
  sorry

end StatLean.ConcentrationInequalities
