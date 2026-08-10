import StatLean.ComputationalStatistics.Core.Defs
import StatLean.Bayesian.ForMathlib.MultinomialDist
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Category counts of i.i.d. categorical draws are multinomial

The bridge between sampling (i.i.d. index draws) and counting (the multinomial
law): if `A₁, …, Aₙ` are i.i.d. `categorical q` on `Fin m`, then the count
vector `V_j = #{i | Aᵢ = j}` has the multinomial distribution `ℳ_m(n; q)`.

* `categoricalCounts` — the count statistic of an index sample;
* `map_categoricalCounts_pi` — the bridge
  `(categorical q)^n ∘ counts⁻¹ = multinomialKernel m n q`, where
  `multinomialKernel` is the existing
  `StatLean.Bayesian.ForMathlib.MultinomialDist` construction (reused, not
  reproved).

This is the missing link (noted absent in the 2026-08-10 survey) between
`StatLean.Bayesian.multinomialKernel` and any i.i.d.-sampling representation;
the Efron bootstrap-counts representation in
`Resampling/BootstrapMoments.lean` is the `q = (1/n, …, 1/n)` case.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 p. 84 (the resampling vector `nP*` "has an
n-variate multinomial distribution with parameters `n` and `(1/n, …, 1/n)`"),
§2.5 (random sampling from data).  (`ECS ch. 4, §2.5`.)

**Proof formalization notes.**

* Both sides are measures on the countable discrete space `Fin m → ℕ`, so
  equality reduces to singletons; the left singleton mass is a sum over the
  fiber `{a | counts a = v}`, of constant value `∏ⱼ qⱼ^{vⱼ}`, and the fiber
  has cardinality `Nat.multinomial univ v` — a finite combinatorial count.
* The simplex hypotheses are genuinely needed: `multinomialWeight` hard-codes
  the off-simplex junk value `0`, while the pushforward is a nonzero measure
  for any nonnegative `q`.
* `categoricalCounts` deliberately coexists with the random-variable-level
  `StatLean.HypothesisTesting.multinomialCount` (Pearson χ² lane, concept
  layer, not importable here); this one is a pure data-level statistic.

**Bibliographic comments.** The multinomial law of category counts is
classical (de Moivre); the resampling-vector formulation is Efron, "Bootstrap
methods: another look at the jackknife," *Ann. Statist.* **7** (1979), 1–26, §2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {m n : ℕ}

/-- The **category counts** of an index sample `a : Fin n → Fin m`:
`categoricalCounts a j = #{i | a i = j}`.  The bootstrap resampling-count
vector of ECS ch. 4 (there `n·P*`). -/
def categoricalCounts (a : Fin n → Fin m) : Fin m → ℕ :=
  fun j => (Finset.univ.filter fun i => a i = j).card

/-- The counts of any index sample sum to the sample size. -/
theorem sum_categoricalCounts (a : Fin n → Fin m) :
    ∑ j, categoricalCounts a j = n := by
  simp only [categoricalCounts]
  rw [← Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ)
    fun i _ => Finset.mem_univ (a i)]
  simp

/-- The count statistic is measurable (both spaces are discrete). -/
theorem measurable_categoricalCounts :
    Measurable (categoricalCounts (m := m) (n := n)) :=
  .of_discrete

/-- Indicator form of the count statistic: `#{i | aᵢ = j} = Σᵢ 1{aᵢ = j}`. -/
private theorem categoricalCounts_eq_sum_ite (a : Fin n → Fin m) (j : Fin m) :
    categoricalCounts a j = ∑ i, if a i = j then 1 else 0 :=
  Finset.card_filter _ _

/-- **Counts of i.i.d. categorical draws are multinomial** (ECS ch. 4, p. 84):
the pushforward of `(categorical q)^{⊗n}` under the count statistic is the
multinomial law `ℳ_m(n; q)` of `StatLean.Bayesian.multinomialKernel`. -/
theorem map_categoricalCounts_pi {q : Fin m → ℝ}
    -- USER-INPUT: nonnegative probability vector; ECS §2.5
    (hq0 : ∀ i, 0 ≤ q i)
    -- USER-INPUT: probabilities sum to one; ECS §2.5
    (hq1 : ∑ i, q i = 1) :
    (Measure.pi fun _ : Fin n => categorical q).map categoricalCounts
      = StatLean.Bayesian.multinomialKernel m n q := by
  sorry

end StatLean.ComputationalStatistics
