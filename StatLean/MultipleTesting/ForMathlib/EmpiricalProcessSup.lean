import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import StatLean.MultipleTesting.PValues.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import Mathlib.Probability.Independence.Basic

/-!
# One-sided Kolmogorov–Smirnov statistic and Massart's inequality — ForMathlib brick

The one-sided KS statistic `KS⁺ = sup_t (F̂ₙ(t) − t)` and its tail bound (Candès, Lecture 3,
§3.3.1, Theorem 2 — Massart's inequality). For `n` p-values `p : Fin n → Ω → ℝ`, the empirical
process `F̂ₙ(t) − t` is right-continuous and decreasing between jumps, so its supremum over `[0,1]`
is attained at the jumps, i.e. `KS⁺ = maxᵢ ( (i+1)/n − p₍ᵢ₊₁₎ )` (a finite max over the order
statistics `p₍₁₎ ≤ … ≤ p₍ₙ₎`). We take that finite max as the definition.

* `ksPlus p ω` — `⨆ᵢ ((i+1)/n − orderStat (p·ω) i)`, the one-sided KS statistic;
* `ksPlus_tail_union` — the **union-bound** tail `μ{KS⁺ ≥ u} ≤ n·e^{−2nu²}` (a *real* theorem:
  order-stat reduction `{(k/n)−p₍ₖ₎ ≥ u} = {countLE(k/n−u) ≥ k}` + Hoeffding at each `k`);
* `massart_inequality` — the **sharp** Massart bound `μ{KS⁺ ≥ u} ≤ 2·e^{−2nu²}` for
  `u ≥ √(log 2/(2n))`; the sharp constant needs the empirical-process reflection argument
  (Massart 1990) and is left as a documented named `sorry`.

Under the global null the p-values are independent with super-uniform marginals; that suffices for
the upper tail of `F̂ₙ(t) − t`. Theorem-agnostic; consumed by the goodness-of-fit assembly.

Reference: Candès, Lecture 3, §3.3.1, Theorem 2, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The **one-sided Kolmogorov–Smirnov statistic** `KS⁺ = maxᵢ ((i+1)/n − p₍ᵢ₊₁₎)`, the supremum
of the empirical process `F̂ₙ(t) − t` (attained at the order statistics). -/
noncomputable def ksPlus (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ i : Fin n, (((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i)

/-- **Order statistic ↔ threshold count.** The `i`-th order statistic of `p(·, ω)` is `≤ s` iff at
least `i + 1` of the `pⱼ(ω)` are `≤ s`, i.e. `(i : ℕ) < countLE p s ω`. This is the discrete
reduction underlying the KS tail: the empirical-process event `{(k/n) − p₍ₖ₎ ≥ u}` becomes the
count event `{countLE (k/n − u) ≥ k}`. Proved from Mathlib's
`Tuple.lt_card_le_iff_apply_le_of_monotone` (applied to the monotone sorted tuple `orderStat`) plus
the reindexing identity `#{i | orderStat v i ≤ s} = #{j | v j ≤ s}`. -/
private theorem orderStat_le_iff_countLE (p : Fin n → Ω → ℝ) (ω : Ω) (i : Fin n) (s : ℝ) :
    orderStat (fun j => p j ω) i ≤ s ↔ (i : ℕ) < countLE p s ω := by
  have hcard :
      (Finset.univ.filter (fun i' => orderStat (fun j => p j ω) i' ≤ s)).card
        = (Finset.univ.filter (fun j => p j ω ≤ s)).card := by
    simp only [Finset.card_filter, orderStat]
    exact Equiv.sum_comp (Tuple.sort (fun j => p j ω))
      (fun j => if p j ω ≤ s then (1 : ℕ) else 0)
  rw [← Tuple.lt_card_le_iff_apply_le_of_monotone (orderStat_monotone (fun j => p j ω))]
  simp only [countLE]
  rw [hcard]

/-- **Per-threshold Hoeffding bound for the count.** For independent super-uniform null p-values
and `1 ≤ k ≤ n`, `μ{ countLE (k/n − u) ≥ k } ≤ e^{−2nu²}`. Proof: the count is a sum of independent
`[0,1]`-indicators with mean `≤ k/n − u`, so the centered sum exceeds `nu` on this event; the
sub-Gaussian (proxy `1/4`) sum-tail bound gives `e^{−(nu)²/(2·n/4)} = e^{−2nu²}`. For `k/n − u < 0`
the event is null (a.s. no `pⱼ ≤ k/n − u` by super-uniformity at `0`). -/
private theorem countLE_tail_le (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1.
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1.
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1.
    (hnull : ∀ j, SuperUniform (p j) μ)
    {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    μ {ω | k ≤ countLE p ((k : ℝ) / (n : ℝ) - u) ω}
      ≤ ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * u ^ 2)) := by
  set s : ℝ := (k : ℝ) / (n : ℝ) - u with hs_def
  have hn1 : 1 ≤ n := le_trans hk1 hkn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rcases lt_or_ge s 0 with hs0 | hs0
  · -- Edge case `s < 0`: the event is null since a.s. no `pⱼ ≤ s`.
    have hnull0 : ∀ j, μ {ω | p j ω ≤ s} = 0 := by
      intro j
      have h1 : μ {ω | p j ω ≤ s} ≤ μ {ω | p j ω ≤ 0} :=
        measure_mono (fun ω hω => le_trans hω (le_of_lt hs0))
      have h2 : μ {ω | p j ω ≤ 0} ≤ ENNReal.ofReal 0 := hnull j 0 le_rfl
      simp only [ENNReal.ofReal_zero] at h2
      exact le_antisymm (le_trans h1 h2) (zero_le _)
    have hsub : {ω | k ≤ countLE p s ω} ⊆ ⋃ j, {ω | p j ω ≤ s} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      have hpos : 0 < countLE p s ω := by omega
      rw [countLE] at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hj
      exact Set.mem_iUnion.mpr ⟨j, hj.2⟩
    calc μ {ω | k ≤ countLE p s ω}
        ≤ μ (⋃ j, {ω | p j ω ≤ s}) := measure_mono hsub
      _ ≤ ∑ j, μ {ω | p j ω ≤ s} := measure_iUnion_fintype_le _ _
      _ = 0 := by simp [hnull0]
      _ ≤ _ := zero_le _
  · -- Main case `s ≥ 0`: Hoeffding on the centered indicators.
    set c : ℝ≥0 := (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 with hc
    have hcR : (c : ℝ) = 1 / 4 := by
      rw [hc]; push_cast; rw [sub_zero, norm_one]; norm_num
    set E : Fin n → ℝ := fun i => ∫ ω, (if p i ω ≤ s then (1 : ℝ) else 0) ∂μ with hEdef
    set X : Fin n → Ω → ℝ := fun i ω => (if p i ω ≤ s then (1 : ℝ) else 0) - E i with hXdef
    -- Measurability of the (uncentered) indicator branch.
    have hg : ∀ i, Measurable (fun y : ℝ => (if y ≤ s then (1 : ℝ) else 0) - E i) := fun i =>
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).sub_const _
    -- Independence of the centered indicators.
    have hXindep : iIndepFun X μ := by
      have h := hindep.comp
        (fun (i : Fin n) (y : ℝ) => (if y ≤ s then (1 : ℝ) else 0) - E i) hg
      exact h
    -- Each centered indicator is sub-Gaussian with proxy `c = 1/4`.
    have hXsubG : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasSubgaussianMGF (X i) c μ := by
      intro i _
      have hb : ∀ᵐ ω ∂μ, (if p i ω ≤ s then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
        filter_upwards with ω
        by_cases h : p i ω ≤ s <;> simp [h, Set.mem_Icc]
      have hsg := StatLean.ConcentrationInequalities.isSubGaussian_of_mem_Icc (μ := μ)
        (X := fun ω => if p i ω ≤ s then (1 : ℝ) else 0) (a := 0) (b := 1)
        (Measurable.ite (measurableSet_le (hmeas i) measurable_const)
          measurable_const measurable_const).aemeasurable hb
      exact hsg
    -- Each indicator has mean `≤ s` (super-uniformity), so `∑ E ≤ k − nu`.
    have hEi : ∀ i, E i ≤ s := by
      intro i
      have hA : MeasurableSet {ω | p i ω ≤ s} := measurableSet_le (hmeas i) measurable_const
      have hind : E i = (μ {ω | p i ω ≤ s}).toReal := by
        simp only [hEdef]
        rw [show (fun ω => if p i ω ≤ s then (1 : ℝ) else 0)
              = Set.indicator {ω | p i ω ≤ s} (fun _ => (1 : ℝ)) from ?_]
        · rw [MeasureTheory.integral_indicator hA, MeasureTheory.setIntegral_const,
            smul_eq_mul, mul_one, measureReal_def]
        · funext ω; rw [Set.indicator_apply]; simp [Set.mem_setOf_eq]
      rw [hind]
      exact ENNReal.toReal_le_of_le_ofReal hs0 (hnull i s hs0)
    have hEbound : ∑ i : Fin n, E i ≤ (k : ℝ) - (n : ℝ) * u := by
      calc ∑ i : Fin n, E i
          ≤ ∑ _i : Fin n, s := Finset.sum_le_sum (fun i _ => hEi i)
        _ = (n : ℝ) * s := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (k : ℝ) - (n : ℝ) * u := by rw [hs_def]; field_simp
    -- The count event sits inside the centered-sum tail event.
    have hsubset : {ω | k ≤ countLE p s ω} ⊆ {ω | (n : ℝ) * u ≤ ∑ i : Fin n, X i ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hsumX : ∑ i : Fin n, X i ω = (countLE p s ω : ℝ) - ∑ i : Fin n, E i := by
        simp only [hXdef]
        rw [Finset.sum_sub_distrib]
        congr 1
        simp only [countLE]
        rw [Finset.card_filter]
        push_cast
        rfl
      rw [hsumX]
      have hkR : (k : ℝ) ≤ (countLE p s ω : ℝ) := by exact_mod_cast hω
      linarith [hEbound]
    -- The sub-Gaussian sum-tail bound at threshold `ε = nu`.
    have hε : (0 : ℝ) ≤ (n : ℝ) * u := by positivity
    have hsum := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := X) (c := fun _ => c) hXindep hXsubG hε
    have hden : ((∑ _i ∈ (Finset.univ : Finset (Fin n)), c : ℝ≥0) : ℝ) = (n : ℝ) / 4 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast [hcR]; ring
    calc μ {ω | k ≤ countLE p s ω}
        ≤ μ {ω | (n : ℝ) * u ≤ ∑ i : Fin n, X i ω} := measure_mono hsubset
      _ = ENNReal.ofReal (μ.real {ω | (n : ℝ) * u ≤ ∑ i : Fin n, X i ω}) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      _ ≤ ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * u ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            refine le_trans hsum (le_of_eq ?_)
            congr 1
            rw [hden]
            field_simp
            ring

/-- **Union-bound KS tail** (the *real*, achievable form). For independent super-uniform null
p-values, `μ{ KS⁺ ≥ u } ≤ n · e^{−2nu²}` (`u ≥ 0`). Proof: `KS⁺ ≥ u ⟺ ∃ k, (k/n) − p₍ₖ₎ ≥ u`, and
`{(k/n) − p₍ₖ₎ ≥ u} = {countLE (k/n − u) ≥ k}`, each bounded by `e^{−2nu²}` (Hoeffding on the
bounded indicators with mean `≤ k/n − u`); union over the `n` order statistics.

The hypothesis `1 ≤ n` is genuinely required: at `n = 0` the empirical sup is `⨆∅ = 0`, so for
`u = 0` the event is all of `Ω` (measure `1`) while the right-hand side is `n · … = 0`. The book
statement is implicitly about `n ≥ 1` samples. -/
theorem ksPlus_tail_union (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    -- USER-INPUT: at least one sample; Candès L3 §3.3.1 (the empirical CDF F̂ₙ needs n ≥ 1, and the
    --             bound is false at n = 0, u = 0 where the event is all of Ω).
    (hn : 1 ≤ n)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ ksPlus p ω} ≤ ENNReal.ofReal ((n : ℝ) * Real.exp (-2 * n * u ^ 2)) := by
  -- Step 1: the sup event lies in the union of the per-order-statistic events.
  haveI hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsubU : {ω | u ≤ ksPlus p ω}
      ⊆ ⋃ i : Fin n, {ω | u ≤ ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    have hmem := Set.Nonempty.csSup_mem
      (Set.range_nonempty
        (fun i : Fin n => ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i))
      (Set.finite_range _)
    obtain ⟨i, hi⟩ := hmem
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_setOf_eq]
    have hksup : ksPlus p ω
        = sSup (Set.range
            (fun i : Fin n => ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i)) := rfl
    rw [hksup] at hω
    exact le_trans hω (le_of_eq hi.symm)
  -- Step 2: each per-order-statistic event has measure `≤ e^{−2nu²}`.
  have hidx : ∀ i : Fin n,
      μ {ω | u ≤ ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i}
        ≤ ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * u ^ 2)) := by
    intro i
    have hk1 : 1 ≤ (i : ℕ) + 1 := by omega
    have hkn : (i : ℕ) + 1 ≤ n := i.isLt
    have hbase := countLE_tail_le μ p hmeas hindep hnull hu hk1 hkn
    have hset : {ω | u ≤ ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i}
        = {ω | (i : ℕ) + 1 ≤ countLE p (((i : ℕ) + 1 : ℕ) / (n : ℝ) - u) ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have hcast : (((i : ℕ) + 1 : ℕ) : ℝ) = ((i : ℕ) + 1 : ℝ) := by push_cast; ring
      rw [hcast]
      constructor
      · intro h
        have h2 : orderStat (fun j => p j ω) i ≤ ((i : ℕ) + 1 : ℝ) / n - u := by linarith
        rw [orderStat_le_iff_countLE] at h2
        omega
      · intro h
        have h2 : (i : ℕ) < countLE p (((i : ℕ) + 1 : ℝ) / n - u) ω := by omega
        rw [← orderStat_le_iff_countLE] at h2
        linarith
    rw [hset]; exact hbase
  -- Step 3: union bound + collapse the constant sum to `n · e^{−2nu²}`.
  calc μ {ω | u ≤ ksPlus p ω}
      ≤ μ (⋃ i : Fin n, {ω | u ≤ ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i}) :=
        measure_mono hsubU
    _ ≤ ∑ i : Fin n, μ {ω | u ≤ ((i : ℕ) + 1 : ℝ) / n - orderStat (fun j => p j ω) i} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * u ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hidx i)
    _ = ENNReal.ofReal ((n : ℝ) * Real.exp (-2 * n * u ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

/-- **Massart's inequality** (Candès, Lecture 3, §3.3.1, Theorem 2 — Massart 1990): the *sharp*
one-sided KS tail `μ{ KS⁺ ≥ u } ≤ 2·e^{−2nu²}` for `u ≥ √(log 2/(2n))`. The sharp constant `2`
(vs. the `n` of `ksPlus_tail_union`) requires the empirical-process reflection argument and is a
documented named debt. -/
theorem massart_inequality (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin n → Ω → ℝ)
    -- USER-INPUT: each p-value is measurable; Candès L3 §3.3.1
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: the p-values are jointly independent; Candès L3 §3.3.1
    (hindep : iIndepFun p μ)
    -- USER-INPUT: every null p-value is super-uniform; Candès L3 §3.3.1
    (hnull : ∀ j, SuperUniform (p j) μ)
    {u : ℝ} (hu : Real.sqrt (Real.log 2 / (2 * n)) ≤ u) :
    μ {ω | u ≤ ksPlus p ω} ≤ ENNReal.ofReal (2 * Real.exp (-2 * n * u ^ 2)) := by
  -- sharp DKW constant — Massart 1990 reflection argument, not in Mathlib
  sorry

end StatLean.MultipleTesting
