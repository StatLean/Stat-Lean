import StatLean.ConcentrationInequalities.VC.Defs

/-!
# Worked VC dimension computations: intervals and a three-point class

Two exact VC dimension computations:
$$ \mathrm{vc}\bigl(\{[a,b] : a \le b\}\bigr) = 2
   \qquad\text{on } \Omega = \mathbb{R}, $$
and, on the three-point set $\Omega = \{0,1,2\}$, the four-member class
encoded by the Boolean strings $\{001, 010, 100, 111\}$ also has VC
dimension $2$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.1, Example 8.3.2 (intervals) and
Example 8.3.4 (the three-point class).

**Proof formalization notes.** Lower bounds are explicit shattering
witnesses, fully precomputed: for intervals shatter `{0, 1}` with the four
intervals `[2,3]` (∅), `[0,0]`, `[1,1]`, `[0,1]`; for the three-point class
shatter `{0, 2}` (the strings `001/100/111` and `010` realize all four
labelings). Upper bounds are case analyses: for intervals, any three-point
set ordered `a < b < c` cannot realize the `101` labeling (an interval
containing `a` and `c` contains the middle point `b`) — extraction via
`Finset.card_eq_three`; for the three-point class, the only 3-set `{0,1,2}`
is not shattered (`{0,1}` is not a trace). `decide` is unavailable for
`Set`-membership propositions, so the case analyses are by hand. Constants:
exact equalities, no slack. Named-sorry fallback of this work item:
`vcDim_intervalClass` (the harder computation; `vcDim_threePointClass` on
`Fin 3` must close).

**Bibliographic comments.** Both examples are HDP's warm-up computations for
Definition 8.3.1; the interval class goes back to the original
Vapnik–Chervonenkis paper (*Theory Probab. Appl.* 16 (1971), 264–280) as the
canonical example of a class with a two-point cap on shattering.
-/

namespace StatLean.ConcentrationInequalities

/-- The class of closed bounded intervals `[a, b]`, `a ≤ b`, on ℝ
(HDP §8.3.1, Example 8.3.2). Edge behavior: singletons `[a, a]` are members;
the empty set is *not* a member (the `a ≤ b` convention), so realizing the
empty labeling uses an interval disjoint from the given points. -/
def intervalClass : Set (Set ℝ) := {S | ∃ a b : ℝ, a ≤ b ∧ S = Set.Icc a b}

/-- The pair `{0, 1}` is shattered by intervals (HDP §8.3.1, Example 8.3.2,
lower bound; four explicit interval witnesses). -/
theorem shatters_intervalClass_pair :
    Shatters intervalClass ({0, 1} : Finset ℝ) := by
  sorry

/-- No three-point subset of ℝ is shattered by intervals (HDP §8.3.1,
Example 8.3.2, upper bound: the `101` labeling of the ordered triple fails
since an interval containing the endpoints contains the middle point). -/
theorem not_shatters_intervalClass_of_card_three {Λ : Finset ℝ}
    -- LEAN-ONLY: cardinality-three extraction via `Finset.card_eq_three`;
    -- encoding of "any three points", no scope change.
    (h : Λ.card = 3) :
    ¬ Shatters intervalClass Λ := by
  sorry

/-- **Intervals have VC dimension 2** (HDP §8.3.1, Example 8.3.2). -/
theorem vcDim_intervalClass : vcDim intervalClass = 2 := by
  sorry

/-- The four-member class on `Fin 3` encoded by the Boolean strings
`001, 010, 100, 111` (HDP §8.3.1, Example 8.3.4; string position `i` is
membership of `i`, so `001 = {2}`, `010 = {1}`, `100 = {0}`,
`111 = univ`). -/
def threePointClass : Set (Set (Fin 3)) :=
  {({2} : Set (Fin 3)), {1}, {0}, Set.univ}

/-- **The three-point class has VC dimension 2** (HDP §8.3.1, Example 8.3.4:
`{0, 2}` is shattered — witnesses `010`/`001`/`100`/`111` — while the only
three-point set `{0, 1, 2}` is not, e.g. the labeling `{0, 2}` itself is not
a trace). -/
theorem vcDim_threePointClass : vcDim threePointClass = 2 := by
  sorry

end StatLean.ConcentrationInequalities
