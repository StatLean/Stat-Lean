import StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-- To bound a square root it is enough to bound the radicand by a square. -/
private lemma sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hxy
    _ = y := Real.sqrt_sq hy

/-- **Cauchy–Schwarz for a finite average**: the average of `|f|` is at most the square root
of the average of `f²`. -/
private lemma avg_abs_le_sqrt_avg_sq {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i| :=
    mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hcs : (∑ i, |f i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => |f i|)
    simpa [Finset.card_univ, sq_abs] using h
  calc (Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|
      = Real.sqrt (((Fintype.card ι : ℝ)⁻¹ * ∑ i, |f i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow]
        have hstep : ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
        calc ((Fintype.card ι : ℝ)⁻¹) ^ 2 * (∑ i, |f i|) ^ 2
            ≤ ((Fintype.card ι : ℝ)⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ∑ i, f i ^ 2) := hstep
          _ = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ^ 2 := by field_simp

/-- The elementary cube inequality `|x − y|³ ≤ 4(|x|³ + |y|³)`. -/
private lemma abs_sub_cube_le (x y : ℝ) : |x - y| ^ 3 ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
  have h1 : |x - y| ≤ |x| + |y| := by
    have h := abs_add_le x (-y)
    simpa [sub_eq_add_neg, abs_neg] using h
  have h2 : |x - y| ^ 3 ≤ (|x| + |y|) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) h1 3
  nlinarith [abs_nonneg x, abs_nonneg y,
    mul_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg y)) (sq_nonneg (|x| - |y|))]

/-- `xy/(x+y) ≤ min x y`: the Stein scale is at most Hájek's scale. -/
private lemma mul_div_add_le_min {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * y / (x + y) ≤ min x y := by
  have hxy : (0 : ℝ) < x + y := by linarith
  refine le_min ?_ ?_
  · rw [div_le_iff₀ hxy]; nlinarith
  · rw [div_le_iff₀ hxy]; nlinarith

/-- `min x y ≤ 2 xy/(x+y)`: Hájek's scale is at most twice the Stein scale. -/
private lemma min_div_two_le_mul_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    min x y / 2 ≤ x * y / (x + y) := by
  have hxy : (0 : ℝ) < x + y := by linarith
  rw [div_le_div_iff₀ (by norm_num) hxy]
  rcases le_total x y with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-! ### The third-moment term of the swap pair -/

/-- **The third-moment term of the swap pair.** The increment of the swap pair is
`u (d(σq) − d(σp))`, so its cube is controlled by the third absolute moment of the population
alone: the average over the group *and* the swap index of `|W' − W|³` is at most
`8 |u|³ N⁻¹ ∑ |d|³`. Both `p` and `q` are single positions, so only the one-coordinate
marginal `avg_perm_apply` is used. -/
private lemma avg_cube_increment_le {N m : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a)
    (hm : 0 < m) (hmN : m < N) (d : Fin N → ℝ) (u : ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (Fintype.card (SwapIndex a) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
          |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
      ≤ 8 * |u| ^ 3 * ((N : ℝ)⁻¹ * ∑ l, |d l| ^ 3) := by
  classical
  have hcP : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcK : (0 : ℝ) < (Fintype.card (SwapIndex a) : ℝ) := by
    rw [card_swapIndex a ha]
    exact_mod_cast Nat.mul_pos hm (Nat.sub_pos_of_lt hmN)
  set T : ℝ := (N : ℝ)⁻¹ * ∑ l, |d l| ^ 3 with hT
  have h3 : (0 : ℝ) ≤ |u| ^ 3 := by positivity
  -- the bound for a single elementary swap
  have hper : ∀ k : SwapIndex a,
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
        ≤ 8 * |u| ^ 3 * T := by
    intro k
    have hb : ∀ σ : Equiv.Perm (Fin N),
        |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
          ≤ 4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) := by
      intro σ
      rw [stdBlockSumSwap_sub a d u σ k, abs_mul, mul_pow]
      calc |u| ^ 3 * |d (σ k.2.1) - d (σ k.1.1)| ^ 3
          ≤ |u| ^ 3 * (4 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3)) :=
            mul_le_mul_of_nonneg_left (abs_sub_cube_le _ _) h3
        _ = 4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) := by ring
    have hq := avg_perm_apply (α := Fin N) k.2.1 fun l => |d l| ^ 3
    have hp := avg_perm_apply (α := Fin N) k.1.1 fun l => |d l| ^ 3
    rw [Fintype.card_fin] at hq hp
    have hq' : ∑ σ : Equiv.Perm (Fin N), |d (σ k.2.1)| ^ 3
        = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * T := by
      rw [hT, ← hq, ← mul_assoc, mul_inv_cancel₀ hcP.ne', one_mul]
    have hp' : ∑ σ : Equiv.Perm (Fin N), |d (σ k.1.1)| ^ 3
        = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * T := by
      rw [hT, ← hp, ← mul_assoc, mul_inv_cancel₀ hcP.ne', one_mul]
    calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
        ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N),
              4 * |u| ^ 3 * (|d (σ k.2.1)| ^ 3 + |d (σ k.1.1)| ^ 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hb σ) (inv_nonneg.2 hcP.le)
      _ = 8 * |u| ^ 3 * T := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hq', hp']
          field_simp
          ring
  -- average over the swap index
  have hswap : ∀ (c₁ c₂ : ℝ) (g : SwapIndex a → ℝ),
      c₁ * c₂ * ∑ k, g k = c₂ * ∑ k, c₁ * g k := by
    intro c₁ c₂ g
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (Fintype.card (SwapIndex a) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
            |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3
      = (Fintype.card (SwapIndex a) : ℝ)⁻¹ * ∑ k : SwapIndex a,
          ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N),
              |stdBlockSumSwap a d u σ k - stdBlockSum a d u σ| ^ 3) := by
        rw [Finset.sum_comm]; exact hswap _ _ _
    _ ≤ (Fintype.card (SwapIndex a) : ℝ)⁻¹ * ∑ _k : SwapIndex a, 8 * |u| ^ 3 * T :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hper k) (inv_nonneg.2 hcK.le)
    _ = 8 * |u| ^ 3 * T := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcK.ne', one_mul]

end StatLean.HypothesisTesting
