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

/-! ### The variance-regression term of the swap pair -/

/-- **The variance-regression term of the swap pair.** With the Stein normalisation
`u² = λ = N/(m(N−m))`, the exact conditional variance `sum_sq_swapIndex_increment` gives
`(2λ)⁻¹ 𝔼[(W'−W)² ∣ σ] = (2m(N−m))⁻¹ (m ∑d² + (N−2m) A₂(σ) + 2 B(σ)²)`, whose group average is
`(N−1)⁻¹ ∑ d²` (`avg_perm_sum_sq_swapIndex_increment`). Subtracting the exact mean leaves two
fluctuations: that of the block sum of squares `A₂`, controlled by Cauchy–Schwarz and the
finite-population variance `avg_perm_blockSum_sq` applied to the *centred squares*
`d² − N⁻¹∑d²` — this is the fourth-moment input `∑ d⁴` — and that of `B²`, which is `O(1/N)`
in mean because `B` is the block sum itself. -/
private lemma avg_abs_one_sub_condSq_le {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) (hmN : m < N)
    (a : Fin m → Fin N) (ha : Function.Injective a) (d : Fin N → ℝ) (hd : ∑ l, d l = 0)
    {u : ℝ} (hu2 : u ^ 2 = (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
            condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
      ≤ |1 - (∑ l, d l ^ 2) / ((N : ℝ) - 1)|
        + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
            Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 4)
        + 2 * (∑ l, d l ^ 2) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  classical
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmNR : (0 : ℝ) < (N : ℝ) - (m : ℝ) := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  have hcP : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  set S₂ : ℝ := ∑ l, d l ^ 2 with hS₂
  set S₄ : ℝ := ∑ l, d l ^ 4 with hS₄
  have hS₂0 : (0 : ℝ) ≤ S₂ := Finset.sum_nonneg fun l _ => sq_nonneg _
  set AA : Equiv.Perm (Fin N) → ℝ := fun σ => ∑ r ∈ blockSet a, d (σ r) ^ 2 with hAA
  set BB : Equiv.Perm (Fin N) → ℝ := fun σ => ∑ r ∈ blockSet a, d (σ r) with hBB
  set c : ℝ := (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₂ with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    exact mul_nonneg (by positivity) hS₂0
  set coef₁ : ℝ := ((N : ℝ) - 2 * (m : ℝ)) / (2 * (m : ℝ) * ((N : ℝ) - m)) with hcoef₁
  set coef₂ : ℝ := ((m : ℝ) * ((N : ℝ) - m))⁻¹ with hcoef₂
  -- the exact pointwise decomposition of the variance-regression ratio
  have hXeq : ∀ σ : Equiv.Perm (Fin N),
      (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
          condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ
        = S₂ / ((N : ℝ) - 1) + coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))
          + coef₂ * ((BB σ) ^ 2 - c) := by
    intro σ
    rw [condSqIncrement, sum_sq_swapIndex_increment a ha d hd u σ, card_swapIndex a ha,
      Nat.cast_mul, Nat.cast_sub hmN.le, hu2, hcoef₁, hcoef₂, hc, hAA, hBB]
    field_simp
    ring
  -- the pointwise triangle inequality
  have hpt : ∀ σ : Equiv.Perm (Fin N),
      |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
          condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
        ≤ |1 - S₂ / ((N : ℝ) - 1)| + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
          + |coef₂| * |(BB σ) ^ 2 - c| := by
    intro σ
    rw [hXeq σ]
    have h1 : 1 - (S₂ / ((N : ℝ) - 1) + coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))
        + coef₂ * ((BB σ) ^ 2 - c))
        = (1 - S₂ / ((N : ℝ) - 1)) + (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
          + -(coef₂ * ((BB σ) ^ 2 - c))) := by ring
    rw [h1]
    calc |(1 - S₂ / ((N : ℝ) - 1)) + (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
            + -(coef₂ * ((BB σ) ^ 2 - c)))|
        ≤ |1 - S₂ / ((N : ℝ) - 1)| + |-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))
            + -(coef₂ * ((BB σ) ^ 2 - c))| := abs_add_le _ _
      _ ≤ |1 - S₂ / ((N : ℝ) - 1)| + (|-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)))|
            + |-(coef₂ * ((BB σ) ^ 2 - c))|) := by
          have hab := abs_add_le (-(coef₁ * (AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂))))
            (-(coef₂ * ((BB σ) ^ 2 - c)))
          linarith
      _ = |1 - S₂ / ((N : ℝ) - 1)| + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
            + |coef₂| * |(BB σ) ^ 2 - c| := by
          rw [abs_neg, abs_neg, abs_mul, abs_mul]; ring
  -- the fluctuation of the block sum of squares, by Cauchy-Schwarz
  set e : Fin N → ℝ := fun l => d l ^ 2 - (N : ℝ)⁻¹ * S₂ with he
  have hecent : ∑ l, e l = 0 := by
    rw [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN0.ne', one_mul, ← hS₂, sub_self]
  have hAe : ∀ σ : Equiv.Perm (Fin N),
      ∑ i, e (σ (a i)) = AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂) := by
    intro σ
    have hblock : AA σ = ∑ i, d (σ (a i)) ^ 2 := sum_blockSet a ha fun r => d (σ r) ^ 2
    rw [hblock, he]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hesq : ∑ l, e l ^ 2 ≤ S₄ := by
    have hexp : ∑ l, e l ^ 2 = S₄ - (N : ℝ) * ((N : ℝ)⁻¹ * S₂) ^ 2 := by
      have hterm : ∀ l : Fin N, e l ^ 2
          = d l ^ 4 - 2 * ((N : ℝ)⁻¹ * S₂) * d l ^ 2 + ((N : ℝ)⁻¹ * S₂) ^ 2 := by
        intro l; rw [he]; ring
      rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← hS₂, ← hS₄]
      field_simp
      ring
    rw [hexp]
    nlinarith [sq_nonneg ((N : ℝ)⁻¹ * S₂), hN0]
  have hAavg : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
      ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄) := by
    have hcs := avg_abs_le_sqrt_avg_sq (ι := Equiv.Perm (Fin N)) fun σ => ∑ i, e (σ (a i))
    have hsq := avg_perm_blockSum_sq hN a ha e hecent
    have hstep : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
        ≤ Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, e l ^ 2) := by
      have hL : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|
          = (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |∑ i, e (σ (a i))| :=
        congrArg _ (Finset.sum_congr rfl fun σ _ => by rw [hAe σ])
      rw [hL]
      refine hcs.trans (le_of_eq ?_)
      rw [hsq]
    refine hstep.trans ?_
    refine Real.sqrt_le_sqrt ?_
    exact mul_le_mul_of_nonneg_left hesq (by positivity)
  -- the fluctuation of the squared block sum
  have hBavg : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c| ≤ 2 * c := by
    have hpt2 : ∀ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c| ≤ (BB σ) ^ 2 + c := by
      intro σ
      calc |(BB σ) ^ 2 - c| ≤ |(BB σ) ^ 2| + |c| := by
            have h := abs_add_le ((BB σ) ^ 2) (-c)
            simpa [sub_eq_add_neg, abs_neg] using h
        _ = (BB σ) ^ 2 + c := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hc0]
    have hsq := avg_perm_blockSet_sq hN a ha d hd
    calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|
        ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), ((BB σ) ^ 2 + c) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt2 σ) (inv_nonneg.2 hcP.le)
      _ = 2 * c := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_add, ← mul_assoc, inv_mul_cancel₀ hcP.ne', one_mul, hBB, hsq, hc, ← hS₂]
          ring
  -- assemble
  have hsplit : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), (|1 - S₂ / ((N : ℝ) - 1)|
        + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)| + |coef₂| * |(BB σ) ^ 2 - c|)
      = |1 - S₂ / ((N : ℝ) - 1)|
        + |coef₁| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|)
        + |coef₂| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
            ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_add, mul_add, ← mul_assoc,
      inv_mul_cancel₀ hcP.ne', one_mul]
    ring
  have habs₁ : |coef₁| = |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) := by
    rw [hcoef₁, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (m : ℝ) * ((N : ℝ) - m))]
  have habs₂ : |coef₂| * (2 * c) = 2 * S₂ / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [hcoef₂, hc, abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) * ((N : ℝ) - m))⁻¹)]
    field_simp
  calc (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N),
            |1 - (2 * ((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))))⁻¹ *
              condSqIncrement (stdBlockSum a d u) (stdBlockSumSwap a d u) σ|
      ≤ (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          ∑ σ : Equiv.Perm (Fin N), (|1 - S₂ / ((N : ℝ) - 1)|
            + |coef₁| * |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)| + |coef₂| * |(BB σ) ^ 2 - c|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt σ) (inv_nonneg.2 hcP.le)
    _ = |1 - S₂ / ((N : ℝ) - 1)|
          + |coef₁| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin N), |AA σ - (m : ℝ) * ((N : ℝ)⁻¹ * S₂)|)
          + |coef₂| * ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
              ∑ σ : Equiv.Perm (Fin N), |(BB σ) ^ 2 - c|) := hsplit
    _ ≤ |1 - S₂ / ((N : ℝ) - 1)|
          + |coef₁| * Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄)
          + |coef₂| * (2 * c) := by
        gcongr
    _ = |1 - S₂ / ((N : ℝ) - 1)|
          + |(N : ℝ) - 2 * (m : ℝ)| / (2 * (m : ℝ) * ((N : ℝ) - m)) *
              Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * S₄)
          + 2 * S₂ / ((N : ℝ) * ((N : ℝ) - 1)) := by rw [habs₁, habs₂]

end StatLean.HypothesisTesting
