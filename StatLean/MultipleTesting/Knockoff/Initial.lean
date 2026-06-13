import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.BinomialRatio

/-!
# Knock-off initial bound (Lu-BDA §19)

`knockoff_initial_le`: `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` every (non-tied) null is counted,
`V₊(0) + V₋(0) = N₀`, and by the knock-off sign field (Def. `kos` cond. 3, i.e.
`KnockoffScore.signs_iIndep`/`signs_fair`) `V₊(0) ~ Binomial(N₀, ½)`. The integral becomes the
finite sum bounded by `binom_ratio_sum_le_one`.

The algebraic half (`binom_ratio_sum_le_one`) is proved locally here via the identity
`C(N,k)·k/(N−k+1) = C(N+1,k) − C(N,k)` (from `Nat.choose_mul_succ_eq`) and the partial-sum
formula `∑_{k=0}^N C(N+1,k) = 2^{N+1} − 1`.  The probability half
(`knockoff_initial_integral_le_binom_sum`) — reducing the expectation to the binomial sum via the
i.i.d. fair-sign distribution of `V₋(0)` — is left as a named sorry.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

-- At t = 0 the magnitude condition `0 ≤ |Wⱼ|` is trivial; simplify to sign conditions alone.

private lemma Splus_zero (W : Fin d → Ω → ℝ) (ω : Ω) :
    Splus W 0 ω = Finset.univ.filter (fun j => 0 < W j ω) := by
  ext j
  simp only [Splus, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨abs_nonneg _, h⟩⟩

private lemma Sminus_zero (W : Fin d → Ω → ℝ) (ω : Ω) :
    Sminus W 0 ω = Finset.univ.filter (fun j => W j ω < 0) := by
  ext j
  simp only [Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨abs_nonneg _, h⟩⟩

/-- At threshold `0`, `V₊(0) + V₋(0) ≤ N₀` since they count disjoint subsets of `H₀`
(positive and negative nulls are disjoint; Lu-BDA §19). -/
private lemma vplus_add_vminus_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Vplus W H₀ 0 ω + Vminus W H₀ 0 ω ≤ H₀.card := by
  unfold Vplus Vminus
  rw [Splus_zero, Sminus_zero]
  have hdisj : Disjoint
      (Finset.univ.filter (fun j => 0 < W j ω) ∩ H₀)
      (Finset.univ.filter (fun j => W j ω < 0) ∩ H₀) :=
    Finset.disjoint_left.mpr fun j hj1 hj2 => by
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      linarith [hj1.1, hj2.1]
  have hunion_sub :
      (Finset.univ.filter (fun j => 0 < W j ω) ∩ H₀) ∪
      (Finset.univ.filter (fun j => W j ω < 0) ∩ H₀) ⊆ H₀ :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have h4 := Finset.card_union_of_disjoint hdisj
  have h5 := Finset.card_le_card hunion_sub
  omega

/-! ## Local algebraic proof of the binomial ratio sum inequality

`∑_{k=0}^N C(N,k)/2^N · k/(1+(N−k)) ≤ 1`.

Proof: each term equals `C(N+1,k)/2^N − C(N,k)/2^N` (from `Nat.choose_mul_succ_eq`), the sum
telescopes to `(∑_{k=0}^N C(N+1,k) − ∑_{k=0}^N C(N,k)) / 2^N = (2^{N+1}−1−2^N)/2^N = 1−1/2^N ≤ 1`.
This is independent of `BinomialRatio.binom_ratio_sum_le_one` (which has a sorry). -/

/-- Per-term identity: `C(N,k)/2^N · k/(1+(N−k)) = C(N+1,k)/2^N − C(N,k)/2^N`. Follows from
`Nat.choose_mul_succ_eq N k : C(N,k)·(N+1) = C(N+1,k)·(N+1−k)`. -/
private lemma binom_ratio_term_eq (N k : ℕ) (hkN : k ≤ N) :
    (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k))) =
    (N + 1).choose k / 2 ^ N - N.choose k / 2 ^ N := by
  have h2N : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hd_pos : (0 : ℝ) < 1 + ((N : ℝ) - k) := by linarith
  have hkN1 : k ≤ N + 1 := Nat.le_succ_of_le hkN
  -- Key: C(N,k) * (N+1) = C(N+1,k) * (1+(N−k)) in ℝ (from choose_mul_succ_eq)
  have hR : (N.choose k : ℝ) * ((N : ℝ) + 1) =
      ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) :=
    calc (N.choose k : ℝ) * ((N : ℝ) + 1)
        = ((N.choose k * (N + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = (((N + 1).choose k * (N + 1 - k) : ℕ) : ℝ) := by
            exact_mod_cast Nat.choose_mul_succ_eq N k
      _ = ((N + 1).choose k : ℝ) * ((N + 1 - k : ℕ) : ℝ) := by push_cast; ring
      _ = ((N + 1).choose k : ℝ) * (1 + ((N : ℝ) - k)) := by
            congr 1; rw [Nat.cast_sub hkN1]; push_cast; ring
  field_simp [h2N, hd_pos.ne']
  linear_combination hR

/-- `∑_{k=0}^N C(N,k)/2^N · k/(1+(N−k)) = 1 − 1/2^N ≤ 1`. -/
private lemma binom_ratio_sum_le_one_local (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k)))) ≤ 1 := by
  have h2N_pos : (0 : ℝ) < 2 ^ N := by positivity
  -- Sufficient: show the sum equals 1 − 1/2^N
  suffices h : ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) / 2 ^ N * ((k : ℝ) / (1 + ((N : ℝ) - k))) = 1 - 1 / 2 ^ N by
    linarith [div_pos one_pos h2N_pos]
  -- Rewrite each term via binom_ratio_term_eq
  rw [Finset.sum_congr rfl fun k hk =>
    binom_ratio_term_eq N k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  -- Split: ∑(A − B) = ∑A − ∑B
  rw [Finset.sum_sub_distrib]
  -- Compute ∑_{k=0}^N C(N,k)/2^N = 1
  have hN : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) / 2 ^ N = 1 := by
    rw [← Finset.sum_div]
    have : (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)) = 2 ^ N := by
      exact_mod_cast Nat.sum_range_choose N
    rw [this, div_self h2N_pos.ne']
  -- Compute ∑_{k=0}^N C(N+1,k)/2^N = 2 − 1/2^N
  have hN1 : ∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ) / 2 ^ N = 2 - 1 / 2 ^ N := by
    rw [← Finset.sum_div]
    -- Partial sum: ∑_{k=0}^N C(N+1,k) = 2^{N+1} − 1
    have hpartial : ∑ k ∈ Finset.range (N + 1), (N + 1).choose k = 2 ^ (N + 1) - 1 := by
      have h := Nat.sum_range_choose (N + 1)
      rw [Finset.sum_range_succ, Nat.choose_self] at h
      omega
    have hcastsum : (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ)) =
        (2 : ℝ) ^ (N + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ (N + 1) := Nat.one_le_two_pow
      calc (∑ k ∈ Finset.range (N + 1), ((N + 1).choose k : ℝ))
          = ((∑ k ∈ Finset.range (N + 1), (N + 1).choose k : ℕ) : ℝ) := by norm_cast
        _ = ((2 ^ (N + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hpartial
        _ = (2 : ℝ) ^ (N + 1) - 1 := by rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcastsum]
    have h2N1 : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by ring
    rw [h2N1]
    field_simp
    ring
  linarith [hN, hN1]

/-- The integral `E[V₊(0)/(1+V₋(0))]` is bounded by the binomial ratio sum (Lu-BDA §19).
Proof outline: `V₊(0) ≤ N₀ − V₋(0)` pointwise (`vplus_add_vminus_le`), so
`E[V₊(0)/(1+V₋(0))] ≤ E[(N₀−V₋(0))/(1+V₋(0))]` by monotone integration. Since
`sgnReal W j ω = −1 ↔ W j ω < 0`, we have `V₋(0) = #{j ∈ H₀ : sgnReal = −1}`, which
is the sum of i.i.d. fair coins by `signs_iIndep`/`signs_fair`, i.e., `V₋(0) ~ Bin(N₀, ½)`.
The expectation then expands as `∑_m C(N₀,m)/2^{N₀} · (N₀−m)/(1+m)`, which equals
`∑_k C(N₀,k)/2^{N₀} · k/(1+(N₀−k))` via the substitution `k = N₀−m`. -/
lemma knockoff_initial_integral_le_binom_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) -- USER-INPUT: knock-off score; Lu-BDA §19, Def. kos
    (H₀ : Finset (Fin d)) -- USER-INPUT: true null set; Lu-BDA §19
    (hW : KnockoffScore W H₀ μ) : -- USER-INPUT: W satisfies Def. kos cond. 3; Lu-BDA §19
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤
    ∑ k ∈ Finset.range (H₀.card + 1),
      (H₀.card.choose k : ℝ) / 2 ^ H₀.card * ((k : ℝ) / (1 + ((H₀.card : ℝ) - k))) := by
  -- Key sub-steps (hard probability half; see docstring for proof plan):
  -- 1. Pointwise: V₊(0)/(1+V₋(0)) ≤ (N₀−V₋(0))/(1+V₋(0)) via vplus_add_vminus_le
  -- 2. Monotone integral: ∫ V₊/(1+V₋) ∂μ ≤ ∫ (N₀−V₋)/(1+V₋) ∂μ
  -- 3. Distribution: V₋(0) ~ Bin(N₀,½) from i.i.d. signs (signs_iIndep + signs_fair)
  --    → ∫ (N₀−V₋)/(1+V₋) ∂μ = ∑_m C(N₀,m)/2^{N₀}·(N₀−m)/(1+m) = binom_sum
  sorry

/-- Initial bound (Lu-BDA §19): `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` the null positives
`V₊(0)` are `Binomial(N₀, ½)`-distributed (the null signs are i.i.d. fair coins), and the
expectation reduces to the binomial ratio sum ≤ 1 (proved algebraically via `choose_mul_succ_eq`). -/
theorem knockoff_initial_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) -- USER-INPUT: knock-off score statistic; Lu-BDA §19, Def. kos
    (H₀ : Finset (Fin d)) -- USER-INPUT: true null hypothesis set; Lu-BDA §19
    (hW : KnockoffScore W H₀ μ) : -- USER-INPUT: W satisfies Def. kos cond. 3; Lu-BDA §19
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤ 1 :=
  le_trans (knockoff_initial_integral_le_binom_sum μ W H₀ hW)
    (binom_ratio_sum_le_one_local H₀.card)

end StatLean.MultipleTesting
