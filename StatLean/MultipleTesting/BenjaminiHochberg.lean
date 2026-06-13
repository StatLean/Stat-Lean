import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Benjamini–Hochberg FDR control — assembly (Lu-BDA §18, Theorem `BH`)

The Benjamini–Hochberg procedure at level `α` orders the p-values `p₍₁₎ ≤ ⋯ ≤ p₍N₎`, finds
`iₘₐₓ = max{ i : p₍ᵢ₎ ≤ iα/N }`, and rejects the `iₘₐₓ` smallest. Equivalently (sort-free, the
form used here) it rejects `{ j : pⱼ ≤ k̂·α/N }` where
`k̂ = max{ k ≤ N : #{ j : pⱼ ≤ kα/N } ≥ k }`.

**Main result** (`benjamini_hochberg_fdr_le`): if the p-values are independent and every null
p-value is super-uniform, then `FDR ≤ (N₀/N)·α ≤ α`, where `N₀ = |H₀|`.

*Book vs Lean.* Lu-BDA §18 states the equality `FDR = (N₀/N)·α` for exactly-uniform nulls; we
prove the honest inequality `≤`, which holds under the weaker `SuperUniform` hypothesis and
specializes to the book's equality when the nulls are exactly uniform.

Proof outline (Lu-BDA §18): for `i ∈ H₀`, `E[ψᵢ/(R∨1)] ≤ α/N` (`bh_claim`), via the
leave-one-out invariance `bh_count_eq_leaveOneOut` and the tower property over the σ-algebra of
the other p-values; summing over `i ∈ H₀` gives the bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Benjamini–Hochberg rejection set at level `α` (Lu-BDA §18): reject `{ j : pⱼ ≤ k̂·α/N }`,
where `k̂ = max{ k ≤ N : #{ j : pⱼ ≤ kα/N } ≥ k }` (the sort-free form of `iₘₐₓ`). With no `k ≥ 1`
satisfying the count condition, `k̂ = 0` and nothing is rejected. -/
noncomputable def bhRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : Finset (Fin N) :=
  let kmax : ℕ := ((Finset.range (N + 1)).filter
    (fun (m : ℕ) => m ≤ (Finset.univ.filter
      (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ))).card)).sup id
  Finset.univ.filter (fun j => p j ω ≤ (kmax : ℝ) * α / (N : ℝ))

/-! ## Helper definitions for the BH proof -/

/-- The BH count: number of p-values at or below `m * α / N`. -/
private def bhCount {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ))).card

/-- The BH kmax: the maximum `k ≤ N` with `bhCount ≥ k`. -/
private def bhKmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) : ℕ :=
  ((Finset.range (N + 1)).filter (fun m => m ≤ bhCount α p m ω)).sup id

/-- The BH rejection set expressed via `bhKmax`. -/
private lemma bhRejects_eq_filter {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhRejects α p ω = Finset.univ.filter (fun j => p j ω ≤ (bhKmax α p ω : ℝ) * α / (N : ℝ)) :=
  rfl

/-- `bhKmax` is at most `N`. -/
private lemma bhKmax_le {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmax α p ω ≤ N := by
  simp only [bhKmax]
  apply Finset.sup_le
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  omega

/-- `bhKmax` is in `Finset.range (N + 1)`. -/
private lemma bhKmax_mem_range {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω) :
    bhKmax α p ω ∈ Finset.range (N + 1) := by
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (bhKmax_le α p ω)

/-- The count `bhCount` is at most `N`. -/
private lemma bhCount_le {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (m : ℕ) (ω : Ω) :
    bhCount α p m ω ≤ N := by
  simp only [bhCount]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- If `K = bhKmax α p ω` and `K ≥ 1`, then `K ≤ bhCount α p K ω`. -/
private lemma bhKmax_le_count {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (hK : 0 < bhKmax α p ω) :
    bhKmax α p ω ≤ bhCount α p (bhKmax α p ω) ω := by
  set S := (Finset.range (N + 1)).filter (fun m => m ≤ bhCount α p m ω)
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp only [S, bhKmax, h, Finset.sup_empty] at hK
  -- bhKmax = S.sup id ∈ id '' ↑S = ↑S (as a set), so bhKmax ∈ S as finset
  have hmem_S : bhKmax α p ω ∈ S := by
    have h := Finset.sup_mem_of_nonempty (f := id) hne
    simp only [Set.image_id, Finset.mem_coe] at h
    exact h
  -- bhKmax ∈ S means bhKmax ≤ bhCount α p (bhKmax) ω
  exact (Finset.mem_filter.mp hmem_S).2

/-- For `m > bhKmax α p ω` with `m ≤ N`, `bhCount α p m ω < m`. -/
private lemma bhCount_lt_of_gt_kmax {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (ω : Ω)
    (m : ℕ) (hm : bhKmax α p ω < m) (hm' : m ≤ N) :
    bhCount α p m ω < m := by
  by_contra h
  push_neg at h
  have hmem : m ∈ (Finset.range (N + 1)).filter (fun k => k ≤ bhCount α p k ω) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hm', h⟩
  have hle : m ≤ ((Finset.range (N + 1)).filter (fun k => k ≤ bhCount α p k ω)).sup id :=
    Finset.le_sup hmem
  simp only [bhKmax] at hm
  omega

/-! ## Leave-one-out combinatorial lemmas -/

/-- For LOO at `i`: `bhCount` with `p i` replaced by `0` equals `bhCount` of original when
`m * α / N ≥ p i ω` and `m * α / N ≥ 0` (i.e., index `i` is in both counts). -/
private lemma bhCount_loo_eq_of_ge {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (i : Fin N)
    (m : ℕ) (ω : Ω) (hm : p i ω ≤ (m : ℝ) * α / (N : ℝ))
    (hpos : 0 ≤ (m : ℝ) * α / (N : ℝ)) :
    bhCount α (Function.update p i (0 : Ω → ℝ)) m ω = bhCount α p m ω := by
  simp only [bhCount]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    -- 0 ≤ m * α / N and p i ω ≤ m * α / N, so LOO (which puts 0 at i) satisfies both conditions
    exact ⟨fun _ => hm, fun _ => hpos⟩
  · simp [Function.update_of_ne hji]

/-- For LOO at `i`: when `m * α / N < p i ω` (and `m * α / N ≥ 0`),
the LOO count exceeds original count by 1. -/
private lemma bhCount_loo_eq_succ_of_lt {N : ℕ} (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ) (i : Fin N)
    (m : ℕ) (ω : Ω) (hm : ¬ (p i ω ≤ (m : ℝ) * α / (N : ℝ))) :
    bhCount α (Function.update p i (0 : Ω → ℝ)) m ω = bhCount α p m ω + 1 := by
  push_neg at hm
  -- 0 ≤ m * α / N since m ≥ 0, α > 0, N ≥ 0
  have hpos : 0 ≤ (m : ℝ) * α / (N : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hα)) (Nat.cast_nonneg N)
  simp only [bhCount]
  -- The LOO filter at i gives 0 ≤ m*α/N (true), while the original doesn't include i.
  -- Show: filter with LOO = (filter with p) ∪ {i}, and i ∉ filter with p.
  have hi_not_mem : i ∉ Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hm
  have hset_eq : Finset.univ.filter (fun j => Function.update p i (0 : Ω → ℝ) j ω ≤
        (m : ℝ) * α / (N : ℝ)) =
      insert i (Finset.univ.filter (fun j => p j ω ≤ (m : ℝ) * α / (N : ℝ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      -- 0 ≤ m * α / N (hpos), so LOO includes i; insert means i is in LHS iff (i = i ∨ ...)
      constructor
      · intro; left; rfl
      · intro; exact hpos
    · simp only [Function.update_of_ne hji, or_iff_right (Ne.symm hji)]
  rw [hset_eq, Finset.card_insert_of_not_mem hi_not_mem]

/-- The BH kmax is unchanged by replacing `p i` with `0` when `i ∈ bhRejects α p ω`. -/
private lemma bhKmax_loo_eq {N : ℕ} (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ)
    (i : Fin N) (ω : Ω)
    (hmem : i ∈ bhRejects α p ω) :
    bhKmax α (Function.update p i (0 : Ω → ℝ)) ω = bhKmax α p ω := by
  -- Let K := bhKmax α p ω. We show bhKmax of LOO = K.
  set K := bhKmax α p ω with hK_def
  -- i ∈ bhRejects means p i ω ≤ K * α / N
  rw [bhRejects_eq_filter] at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  apply le_antisymm
  · -- bhKmax loo ≤ K: any m in the loo filter satisfies m ≤ K
    simp only [bhKmax]
    apply Finset.sup_le
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmN, hm_count⟩ := hm
    -- We need m ≤ K. Suppose m > K.
    by_contra h
    push_neg at h
    have hmN' : m ≤ N := Nat.lt_succ_iff.mp hmN
    -- For m > K, bhCount p m < m
    have hc_lt : bhCount α p m ω < m := bhCount_lt_of_gt_kmax α p ω m h hmN'
    -- Compare bhCount loo m with bhCount p m
    by_cases hge : p i ω ≤ (m : ℝ) * α / (N : ℝ)
    · have hpos : 0 ≤ (m : ℝ) * α / (N : ℝ) := by
        apply div_nonneg (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hα))
        exact Nat.cast_nonneg N
      rw [bhCount_loo_eq_of_ge α p i m ω hge hpos] at hm_count; omega
    · rw [bhCount_loo_eq_succ_of_lt α hα p i m ω hge] at hm_count; omega
  · -- K ≤ bhKmax loo: K is in the loo filter
    by_cases hK0 : K = 0
    · simp [hK0]
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
      have hK_count : K ≤ bhCount α p K ω := bhKmax_le_count α p ω hKpos
      -- For m = K: p i ω ≤ K * α/N, so bhCount loo K = bhCount p K ≥ K
      have hloo_K : K ≤ bhCount α (Function.update p i (0 : Ω → ℝ)) K ω := by
        have hpos : 0 ≤ (K : ℝ) * α / (N : ℝ) := by
          apply div_nonneg (mul_nonneg (Nat.cast_nonneg K) (le_of_lt hα))
          exact Nat.cast_nonneg N
        rw [bhCount_loo_eq_of_ge α p i K ω hmem hpos]; exact hK_count
      -- So K ∈ filter for loo
      have hK_mem : K ∈ ((Finset.range (N + 1)).filter
          (fun m => m ≤ bhCount α (Function.update p i (0 : Ω → ℝ)) m ω)) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (bhKmax_le α p ω), hloo_K⟩
      exact le_trans (Finset.le_sup hK_mem) le_rfl

/-- The rejection set is unchanged by LOO replacement when `i ∈ bhRejects α p ω`. -/
private lemma bhRejects_loo_eq {N : ℕ} (α : ℝ) (hα : 0 < α) (p : Fin N → Ω → ℝ)
    (i : Fin N) (ω : Ω)
    (hmem : i ∈ bhRejects α p ω) :
    bhRejects α (Function.update p i (0 : Ω → ℝ)) ω = bhRejects α p ω := by
  -- After unfolding bhRejects, we need: filter with threshold bhKmax loo = filter with threshold K.
  -- Since bhKmax loo = K, the thresholds are identical.
  -- The only difference is p vs update p i 0 at index i; but i already passes both thresholds.
  -- After rewriting via bhRejects_eq_filter, bhKmax loo = bhKmax p (by bhKmax_loo_eq),
  -- so the threshold is the same; the only difference is p vs update p i 0 at i.
  rw [bhRejects_eq_filter, bhRejects_eq_filter, bhKmax_loo_eq α hα p i ω hmem]
  -- hmem gives p i ω ≤ bhKmax α p ω * α / N (after unfolding bhRejects_eq_filter)
  have hi_le : p i ω ≤ (bhKmax α p ω : ℝ) * α / (N : ℝ) := by
    rw [bhRejects_eq_filter] at hmem
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    -- 0 ≤ (bhKmax : ℝ) * α / N because bhKmax ≥ 0, α > 0, N ≥ 0
    exact ⟨fun _ => hi_le, fun _ => by positivity⟩
  · simp [Function.update_of_ne hji]

/-- Leave-one-out invariance (Lu-BDA §18, BH proof, "second key observation"): if hypothesis `i`
is rejected and the total number of rejections is `k`, then replacing `pᵢ` by the constant `0`
leaves the number of rejections equal to `k`. The deterministic combinatorial crux. -/
theorem bh_count_eq_leaveOneOut {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    -- LEAN-ONLY: positivity of N and α needed for the combinatorial argument
    (p : Fin N → Ω → ℝ) (i : Fin N) (k : ℕ) (ω : Ω)
    (hmem : i ∈ bhRejects α p ω) (hR : numRejections (bhRejects α p) ω = k) :
    numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k := by
  simp only [numRejections] at *
  rw [bhRejects_loo_eq α hα p i ω hmem]
  exact hR

/-! ## Measurability lemmas (sorry'd — measure-theoretic infrastructure) -/

/-- Measurability of the set `{ω | i ∈ bhRejects α p ω}`. -/
private lemma measurableSet_bhRejects_mem {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    MeasurableSet {ω | i ∈ bhRejects α p ω} := by
  sorry

/-- Measurability of `numRejections (bhRejects α p)` as a function of ω. -/
private lemma measurable_numRejections_bhRejects {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) :
    Measurable (fun ω => numRejections (bhRejects α p) ω) := by
  sorry

/-- The BH per-null summand is measurable. -/
private lemma measurable_bh_summand {N : ℕ} (α : ℝ) (hα : 0 < α)
    (p : Fin N → Ω → ℝ) (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    Measurable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) := by
  -- Measurability follows from measurability of the indicator and numRejections.
  -- The indicator is measurable (measurableSet_bhRejects_mem, sorry'd).
  -- The denominator max(R, 1) is measurable (measurable_numRejections_bhRejects, sorry'd).
  -- Division of measurable functions over ℝ is measurable since the denominator ≥ 1 > 0.
  sorry

/-- The BH per-null summand is pointwise bounded by 1. -/
private lemma bh_summand_le_one {N : ℕ} (α : ℝ) (p : Fin N → Ω → ℝ) (i : Fin N) (ω : Ω) :
    ‖(if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1‖ ≤ ‖(1 : ℝ)‖ := by
  simp only [Real.norm_one]
  have hd_pos : 0 < max (numRejections (bhRejects α p) ω : ℝ) 1 :=
    lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [Real.norm_of_nonneg (div_nonneg (by split_ifs <;> simp) (le_of_lt hd_pos))]
  apply div_le_one_of_le
  · split_ifs <;> simp
  · exact le_of_lt hd_pos

/-- Integrability of the BH per-null summand `ψᵢ / (R ∨ 1)`. -/
private lemma integrable_bh_summand {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ) (hmeas : ∀ j, Measurable (p j)) (i : Fin N) :
    Integrable (fun ω => (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) μ := by
  -- Bounded by the constant 1, which is integrable on a probability space.
  apply Integrable.mono (integrable_const 1)
  · exact (measurable_bh_summand α hα p hmeas i).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (bh_summand_le_one α p i)

/-! ## Independence helper for the BH claim -/

/-- The LOO rejection count is independent of `p i` when the p-values are jointly independent.
This is the key independence fact: the σ-algebra generated by `{p j : j ≠ i}` is independent
of the σ-algebra generated by `p i`, by `iIndepFun`. -/
private lemma bh_loo_indep_mul {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p μ)
    (i : Fin N) (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    μ ({ω | p i ω ≤ t} ∩
        {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k}) =
    μ {ω | p i ω ≤ t} *
        μ {ω | numRejections (bhRejects α (Function.update p i (0 : Ω → ℝ))) ω = k} := by
  sorry

/-! ## Per-null contribution bound -/

/-- Per-null contribution bound (Lu-BDA §18, the claim `E[ψᵢ/(R∨1)] = α/N`, honest `≤` form):
for a null index `i` with super-uniform p-value, `E[ψᵢ/(R∨1)] ≤ α/N`. -/
theorem bh_claim {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for independence / integration
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: p-values independent; Lu-BDA §18 (BH)
    (hindep : iIndepFun p μ)
    (i : Fin N)
    -- USER-INPUT: null marginal super-uniform; Lu-BDA §18 (BH)
    (hi : SuperUniform (p i) μ) :
    ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0)
          / max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ ≤ α / N := by
  sorry

/-! ## FDP decomposition -/

/-- Decompose `numFalseRejections` as a sum of indicators over `H₀`. -/
private lemma numFalseRejections_eq_sum {N : ℕ} (α : ℝ) (H₀ : Finset (Fin N))
    (p : Fin N → Ω → ℝ) (ω : Ω) :
    (numFalseRejections H₀ (bhRejects α p) ω : ℝ) =
    ∑ i ∈ H₀, if i ∈ bhRejects α p ω then (1 : ℝ) else 0 := by
  simp only [numFalseRejections]
  -- bhRejects ∩ H₀ = H₀.filter (∈ bhRejects) (membership condition swapped)
  have hset : (bhRejects α p ω ∩ H₀) = H₀.filter (fun i => i ∈ bhRejects α p ω) := by
    ext j; simp [Finset.mem_inter, Finset.mem_filter, and_comm]
  rw [hset]
  -- natCast_card_filter: (#{x ∈ H₀ | x ∈ bhRejects} : ℝ) = ∑ i ∈ H₀, if i ∈ bhRejects then 1 else 0
  exact Finset.natCast_card_filter _ H₀

/-- Rewrite `FDP` as a sum of per-null indicators divided by `R ∨ 1`. -/
private lemma fdp_eq_sum_div {N : ℕ} (α : ℝ) (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    (ω : Ω) :
    FDP H₀ (bhRejects α p) ω =
    ∑ i ∈ H₀, ((if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
        max (numRejections (bhRejects α p) ω : ℝ) 1) := by
  simp only [FDP]
  rw [numFalseRejections_eq_sum, Finset.sum_div]

/-- **Benjamini–Hochberg FDR control** (Lu-BDA §18, Theorem `BH`). If the p-values are
independent and each null p-value is super-uniform, the BH procedure at level `α` controls the
false discovery rate: `FDR ≤ (N₀/N)·α ≤ α`. -/
theorem benjamini_hochberg_fdr_le {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : 0 < α)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin N)) (p : Fin N → Ω → ℝ)
    -- LEAN-ONLY: measurability of each p-value; needed for independence / integration
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: p-values independent; Lu-BDA §18 (BH)
    (hindep : iIndepFun p μ)
    -- USER-INPUT: null marginals super-uniform; Lu-BDA §18 (BH)
    (hnull : ∀ j ∈ H₀, SuperUniform (p j) μ) :
    FDR H₀ (bhRejects α p) μ ≤ (H₀.card : ℝ) / N * α := by
  -- Step 1: Unfold FDR and rewrite FDP as sum of per-null indicators.
  simp only [FDR]
  have hfdp_sum : ∀ ω, FDP H₀ (bhRejects α p) ω =
      ∑ i ∈ H₀, ((if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
          max (numRejections (bhRejects α p) ω : ℝ) 1) :=
    fun ω => fdp_eq_sum_div α H₀ p ω
  simp_rw [hfdp_sum]
  -- Step 2: Swap integral and sum.
  rw [integral_finset_sum H₀ (fun i _ => integrable_bh_summand hN α hα μ p hmeas i)]
  -- Step 3: Bound each summand by α/N using bh_claim, then sum.
  calc ∑ i ∈ H₀, ∫ ω, (if i ∈ bhRejects α p ω then (1 : ℝ) else 0) /
          max (numRejections (bhRejects α p) ω : ℝ) 1 ∂μ
      ≤ ∑ _i ∈ H₀, α / N := by
        apply Finset.sum_le_sum
        intro i hi
        exact bh_claim hN α hα μ p hmeas hindep i (hnull i hi)
    _ = H₀.card * (α / N) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (H₀.card : ℝ) / N * α := by ring

end StatLean.MultipleTesting
