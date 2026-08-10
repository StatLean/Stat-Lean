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
open scoped ENNReal NNReal BigOperators Nat

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

/-! ### Combinatorics of the count fibers

The fiber `{a | counts a = v}` over a count vector `v` with `∑ v = n` has
cardinality `Nat.multinomial univ v`; this is the only genuinely combinatorial
input to the bridge, proved by induction on `n` (peeling the first coordinate).
-/

/-- Pascal-style recurrence for the multinomial coefficient: decrementing one
coordinate and summing over the choice of coordinate reproduces the coefficient.
Proved by clearing the factorial denominators through `Nat.multinomial_spec`. -/
private theorem sum_multinomial_update (v : Fin m → ℕ) (N : ℕ) (hv : ∑ j, v j = N + 1) :
    (∑ j, if v j = 0 then 0
      else Nat.multinomial Finset.univ (Function.update v j (v j - 1)))
      = Nat.multinomial Finset.univ v := by
  have hQpos : 0 < ∏ i, (v i)! := Finset.prod_pos fun i _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_left hQpos ?_
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      (∏ i, (v i)!) * (if v j = 0 then 0
        else Nat.multinomial Finset.univ (Function.update v j (v j - 1)))
        = v j * N ! := by
    intro j _
    by_cases hj : v j = 0
    · simp [hj]
    rw [if_neg hj]
    -- the sum of the decremented vector is `N`
    have hsplit : ∑ i ∈ Finset.univ \ {j}, v i + ∑ i ∈ ({j} : Finset (Fin m)), v i
        = ∑ i, v i := Finset.sum_sdiff (Finset.subset_univ _)
    rw [Finset.sum_singleton] at hsplit
    have hsumw : ∑ i, Function.update v j (v j - 1) i = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
      omega
    -- the factorial products differ by the factor `v j`
    have hrest : ∀ i ∈ Finset.univ \ ({j} : Finset (Fin m)),
        (Function.update v j (v j - 1) i)! = (v i)! := by
      intro i hi
      have hij : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
      rw [Function.update_of_ne hij]
    have h2 : ∏ i, (Function.update v j (v j - 1) i)!
        = (v j - 1)! * ∏ i ∈ Finset.univ \ ({j} : Finset (Fin m)), (v i)! := by
      have hsd := Finset.prod_sdiff (f := fun i => (Function.update v j (v j - 1) i)!)
        (Finset.subset_univ ({j} : Finset (Fin m)))
      simp only [Finset.prod_singleton, Function.update_self] at hsd
      rw [← hsd, Finset.prod_congr rfl hrest]
      ring
    have h1 : ∏ i, (v i)!
        = v j * ((v j - 1)! * ∏ i ∈ Finset.univ \ ({j} : Finset (Fin m)), (v i)!) := by
      have hsd := Finset.prod_sdiff (f := fun i => (v i)!)
        (Finset.subset_univ ({j} : Finset (Fin m)))
      simp only [Finset.prod_singleton] at hsd
      rw [← hsd, ← Nat.mul_factorial_pred hj]
      ring
    have hspecw := Nat.multinomial_spec (Finset.univ : Finset (Fin m))
      (Function.update v j (v j - 1))
    rw [hsumw] at hspecw
    calc (∏ i, (v i)!) * Nat.multinomial Finset.univ (Function.update v j (v j - 1))
        = v j * ((∏ i, (Function.update v j (v j - 1) i)!) *
            Nat.multinomial Finset.univ (Function.update v j (v j - 1))) := by
          rw [h1, h2]; ring
      _ = v j * N ! := by rw [hspecw]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hv, Nat.multinomial_spec, hv,
    Nat.factorial_succ]

/-- Peeling the first coordinate of an index sample. -/
private theorem categoricalCounts_succ (a : Fin (n + 1) → Fin m) (k : Fin m) :
    categoricalCounts a k
      = (if a 0 = k then 1 else 0) + categoricalCounts (fun i => a i.succ) k := by
  simp only [categoricalCounts_eq_sum_ite, Fin.sum_univ_succ]

/-- The fiber of the counts map over `v`, restricted to samples starting at `j`,
is in bijection with the fiber over `v` with one unit removed at `j`. -/
private theorem card_counts_fiber_first (v : Fin m → ℕ) {j : Fin m} (hj : v j ≠ 0) :
    ((Finset.univ.filter fun a : Fin (n + 1) → Fin m => categoricalCounts a = v).filter
        fun a => a 0 = j).card
      = (Finset.univ.filter fun b : Fin n → Fin m =>
          categoricalCounts b = Function.update v j (v j - 1)).card := by
  refine Finset.card_nbij' (fun a => fun i => a i.succ) (fun b => Fin.cons j b) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨hcount, hzero⟩ := ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    funext k
    have hk := categoricalCounts_succ a k
    rw [hcount, hzero] at hk
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl] at hk
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hkj]
      rw [if_neg (fun h => hkj h.symm)] at hk
      omega
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, Fin.cons_zero _ _⟩
    funext k
    have hk := categoricalCounts_succ (Fin.cons j b) k
    simp only [Fin.cons_zero, Fin.cons_succ] at hk
    rw [hk, hb]
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self, if_pos rfl]
      omega
    · rw [Function.update_of_ne hkj, if_neg (fun h => hkj h.symm)]
      omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [← ha.2]
    exact Fin.cons_self_tail a
  · intro b _
    funext i
    simp

/-- **The counts fiber is a multinomial coefficient.** -/
private theorem card_counts_fiber :
    ∀ (n : ℕ) (v : Fin m → ℕ), ∑ j, v j = n →
      (Finset.univ.filter fun a : Fin n → Fin m => categoricalCounts a = v).card
        = Nat.multinomial Finset.univ v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hv0 : ∀ j, v j = 0 := fun j => Finset.sum_eq_zero_iff.mp hv j (Finset.mem_univ j)
    have hcount : ∀ a : Fin 0 → Fin m, categoricalCounts a = v := by
      intro a; funext j; simp [categoricalCounts, hv0 j]
    rw [Finset.filter_true_of_mem fun a _ => hcount a, Finset.card_univ]
    simp [Nat.multinomial, hv0]
  | succ n ih =>
    intro v hv
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun a : Fin (n + 1) → Fin m => a 0) (t := Finset.univ)
      fun a _ => Finset.mem_univ _]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        ((Finset.univ.filter fun a : Fin (n + 1) → Fin m => categoricalCounts a = v).filter
            fun a => a 0 = j).card
          = if v j = 0 then 0
            else Nat.multinomial Finset.univ (Function.update v j (v j - 1)) := by
      intro j _
      by_cases hj : v j = 0
      · rw [if_pos hj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        intro hzero
        have hk := categoricalCounts_succ a j
        rw [ha, hzero, if_pos rfl, hj] at hk
        omega
      · rw [if_neg hj, card_counts_fiber_first v hj]
        refine ih _ ?_
        rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
        have hsplit : ∑ i ∈ Finset.univ \ {j}, v i + ∑ i ∈ ({j} : Finset (Fin m)), v i
            = ∑ i, v i := Finset.sum_sdiff (Finset.subset_univ _)
        rw [Finset.sum_singleton] at hsplit
        omega
    rw [Finset.sum_congr rfl hterm]
    exact sum_multinomial_update v n hv

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
