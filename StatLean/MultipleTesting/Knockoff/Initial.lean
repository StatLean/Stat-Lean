import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.BinomialRatio

/-!
# Knock-off initial bound (Lu-BDA §19)

`knockoff_initial_le`: `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` every (non-tied) null is counted,
`V₊(0) + V₋(0) = N₀`, and by the knock-off sign field (Def. `kos` cond. 3, i.e.
`KnockoffScore.signs_iIndep`/`signs_fair`) `V₊(0) ~ Binomial(N₀, ½)`. The integral becomes the
finite sum bounded by `binom_ratio_sum_le_one`.
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
  -- Key sub-steps (all sorry'd here; see docstring for proof plan):
  -- 1. Pointwise: V₊(0)/(1+V₋(0)) ≤ (N₀−V₋(0))/(1+V₋(0)) via vplus_add_vminus_le
  -- 2. Monotone integral: ∫ V₊/(1+V₋) ∂μ ≤ ∫ (N₀−V₋)/(1+V₋) ∂μ
  -- 3. Distribution: V₋(0) ~ Bin(N₀,½) from i.i.d. signs → integral = binomial sum (with k=N₀−m)
  sorry

/-- Initial bound (Lu-BDA §19): `E[V₊(0)/(1+V₋(0))] ≤ 1`. At threshold `0` the null positives
`V₊(0)` are `Binomial(N₀, ½)`-distributed (the null signs are i.i.d. fair coins), and the
expectation reduces to `binom_ratio_sum_le_one`. -/
theorem knockoff_initial_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin d → Ω → ℝ) -- USER-INPUT: knock-off score statistic; Lu-BDA §19, Def. kos
    (H₀ : Finset (Fin d)) -- USER-INPUT: true null hypothesis set; Lu-BDA §19
    (hW : KnockoffScore W H₀ μ) : -- USER-INPUT: W satisfies Def. kos cond. 3; Lu-BDA §19
    ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ ≤ 1 :=
  le_trans (knockoff_initial_integral_le_binom_sum μ W H₀ hW) (binom_ratio_sum_le_one H₀.card)

end StatLean.MultipleTesting
