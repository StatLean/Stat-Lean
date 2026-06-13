import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
import StatLean.ConcentrationInequalities.Maximal.CoveringBall
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space

/-!
# ℓ²-Norm Maximal Inequality — Lu-BDA §4.2 (`thm:l2`)

For a centered sub-Gaussian random vector `X : Ω → EuclideanSpace ℝ (Fin d)` with
variance proxy `σ²‖u‖₊²` for every direction `u`, we prove:

**Expectation bound** (`l2_max_expectation`):  `E[‖X‖] ≤ 4σ√d`

**High-probability bound** (`l2_max_tail`): for any `δ > 0`, with probability ≥ 1 − δ,
`‖X‖ ≤ 4σ√d + 2σ√(2 log(1/δ))`

Proof idea (Lu §4.2 discretization): take a 1/2-net `N` of `closedBall 0 1` with
`|N| ≤ 5^d`.  The variational identity `‖x‖ = ⟨x/‖x‖, x⟩` and the net give
`‖x‖ ≤ 2 max_{v∈N} ⟨v, x⟩`.  Each inner product `⟨v, X⟩` is sub-Gaussian with
proxy `σ²` (since `‖v‖ ≤ 1`), so `expectation_max_le` / `tail_max_le` bound the
finite max; using `log 5 ≤ 2` yields `2√(2d log 5) ≤ 4√d`.

Deviation from book: `log 5 ≤ 2` (i.e., `5 ≤ e²`) is used to relax `√(2d log 5) ≤ 2√d`.
-/

open MeasureTheory ProbabilityTheory Real Metric Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Private helpers -/

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
private lemma hasSubgaussianMGF_mono {X : Ω → ℝ} {c d : ℝ≥0} {μ : Measure Ω}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    have hcd' : (c : ℝ) ≤ d := NNReal.coe_le_coe.mpr hcd
    nlinarith [sq_nonneg t]))

/-- Monotonicity of `IsSubGaussian` in the variance proxy. -/
private lemma isSubGaussian_mono {X : Ω → ℝ} {c d : ℝ≥0} {μ : Measure Ω}
    (h : IsSubGaussian X c μ) (hcd : c ≤ d) : IsSubGaussian X d μ :=
  hasSubgaussianMGF_mono h hcd

/-- If `X` is a sub-Gaussian vector (each direction `u` has `⟨u, X⟩` sub-Gaussian with
proxy `σ²‖u‖₊²`) and `‖v‖ ≤ 1`, then `⟨v, X⟩` is sub-Gaussian with proxy `σ²`. -/
private lemma isSubGaussian_inner_of_norm_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ ≤ 1) :
    IsSubGaussian (fun ω => inner ℝ v (X ω)) σ2 μ := by
  apply isSubGaussian_mono (hX v)
  nth_rewrite 2 [← mul_one σ2]
  apply mul_le_mul_of_nonneg_left _ (zero_le _)
  have h_nnnorm_le : (‖v‖₊ : ℝ) ≤ 1 := by exact_mod_cast hv
  have h_sq_le : (‖v‖₊ : ℝ) ^ 2 ≤ 1 := by
    nlinarith [NNReal.coe_nonneg ‖v‖₊, sq_nonneg (1 - (‖v‖₊ : ℝ))]
  exact_mod_cast h_sq_le

/-- `log 5 ≤ 2`, i.e., `5 ≤ e²`.  Used to relax `√(2d log 5) ≤ 2√d`. -/
private lemma log_five_le_two : Real.log 5 ≤ 2 := by
  rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
  apply Real.log_le_log (by norm_num)
  have h := Real.sum_le_exp_of_nonneg (x := 2) (by norm_num) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h; linarith

/-- Integrability of `fun ω => ⨆ j : Fin d, f j ω` when each `f j` is integrable.
Dominated by `∑ ‖f j ω‖`. -/
private lemma integrable_iSup_fin
    {d : ℕ} [NeZero d] {μ : Measure Ω}
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Integrable (f j) μ) :
    Integrable (fun ω => ⨆ j, f j ω) μ := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  apply Integrable.mono' (g := fun ω => ∑ j : Fin d, ‖f j ω‖)
  · exact integrable_finset_sum _ (fun j _ => (hf j).norm)
  · exact (AEMeasurable.iSup (fun j =>
        (hf j).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  · filter_upwards with ω
    simp only [Real.norm_eq_abs]
    have hbdd : BddAbove (Set.range (fun j => f j ω)) := Finite.bddAbove_range _
    have h1 : ⨆ j, f j ω ≤ ∑ j : Fin d, |f j ω| :=
      ciSup_le fun j =>
        (le_abs_self _).trans
          (Finset.single_le_sum (f := fun k => |f k ω|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j))
    have h2 : -(⨆ j, f j ω) ≤ ∑ j : Fin d, |f j ω| :=
      calc -(⨆ j, f j ω)
          ≤ -(f 0 ω) := neg_le_neg (le_ciSup hbdd 0)
        _ ≤ |f 0 ω| := by rw [← abs_neg]; exact le_abs_self _
        _ ≤ ∑ j : Fin d, |f j ω| :=
            Finset.single_le_sum (f := fun k => |f k ω|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ 0)
    exact abs_le.mpr ⟨by linarith, h1⟩

/-! ### Common net infrastructure (used by both main theorems) -/

/-- Build a 1/2-net `F : Finset` of the unit ball in `EuclideanSpace ℝ (Fin d)`.
Returns `⟨F, he, hcov⟩` where `F` is a Finset, `he` enumerates it, `hcov` is the
covering property, and the cardinality satisfies `F.card ≤ 5^d`. -/
private structure L2NetData (d : ℕ) [NeZero d] where
  F : Finset (EuclideanSpace ℝ (Fin d))
  hF_nonempty : F.Nonempty
  hF_norm : ∀ v ∈ F, ‖v‖ ≤ 1
  hF_cover : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
               ∃ v ∈ F, dist x v ≤ 1 / 2
  hF_card_le : F.card ≤ 5 ^ d

/-- Construct the 1/2-net data via `Metric.minimalCover`. -/
private noncomputable def buildL2Net (d : ℕ) [NeZero d]
    [DecidableEq (EuclideanSpace ℝ (Fin d))] : L2NetData d := by
  let ε' : ℝ≥0 := Real.toNNReal (1 / 2)
  have hcov_ne_top : Metric.coveringNumber ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _)
      (coveringNumber_closedBall_le (d := d) (ε := 1 / 2) (by norm_num) (by norm_num))
  let N := Metric.minimalCover ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hN_cov : Metric.IsCover ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) N :=
    Metric.isCover_minimalCover hcov_ne_top
  have hN_fin : N.Finite := Metric.finite_minimalCover
  have hN_sub : N ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    Metric.minimalCover_subset
  let F := hN_fin.toFinset
  have hN_nonempty : N.Nonempty := by
    obtain ⟨v, hv_N, _⟩ := hN_cov (Metric.mem_closedBall_self zero_le_one)
    exact ⟨v, hv_N⟩
  have hF_nonempty : F.Nonempty := hN_fin.toFinset_nonempty.mpr hN_nonempty
  have hF_norm : ∀ v ∈ F, ‖v‖ ≤ 1 := fun v hv => by
    have := hN_sub (hN_fin.mem_toFinset.mp hv)
    simp only [mem_closedBall, dist_zero_right] at this; exact this
  have hF_cover : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∃ v ∈ F, dist x v ≤ 1 / 2 := fun x hx => by
    obtain ⟨v, hv_N, hv_edist⟩ := hN_cov hx
    refine ⟨v, hN_fin.mem_toFinset.mpr hv_N, ?_⟩
    rw [← edist_le_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc edist x v ≤ (ε' : ℝ≥0∞) := hv_edist
      _ = ENNReal.ofReal (1 / 2) := by simp [ε', ENNReal.ofReal, Real.toNNReal]
  have hF_card_le : F.card ≤ 5 ^ d := by
    apply ENat.coe_le_coe.mp
    calc (F.card : ℕ∞)
        = N.encard := hN_fin.encard_eq_coe_toFinset_card.symm
      _ = Metric.coveringNumber ε' (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
            Metric.encard_minimalCover hcov_ne_top
      _ = coveringNumber (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (1 / 2 : ℝ) := rfl
      _ ≤ (⌊(1 + 2 / (1 / 2 : ℝ)) ^ d⌋₊ : ℕ∞) :=
            coveringNumber_closedBall_le (by norm_num) (by norm_num)
      _ = ((5 : ℕ) ^ d : ℕ∞) := by
            norm_cast
            rw [show ⌊(1 + 2 / (1 / 2 : ℝ)) ^ d⌋₊ = 5 ^ d from by
              have : (1 + 2 / (1 / 2 : ℝ)) ^ d = ((5 ^ d : ℕ) : ℝ) := by push_cast; norm_num
              rw [this, Nat.floor_natCast]]
  exact ⟨F, hF_nonempty, hF_norm, hF_cover, hF_card_le⟩

/-! ### Main theorems -/

/-- **ℓ²-Norm Maximal Inequality — expectation bound** (Lu-BDA §4.2, `thm:l2`).

For a centered sub-Gaussian random vector `X : Ω → EuclideanSpace ℝ (Fin d)` with
variance proxy `σ²‖u‖₊²` for every direction `u`, under a probability measure `μ`:
```
E[‖X‖] ≤ 4σ√d
```

Proof (Lu §4.2): take a 1/2-net `N` of `closedBall 0 1` with `|N| ≤ 5^d`.  The
variational identity `‖x‖ = ⟨x/‖x‖, x⟩` and the net give `‖x‖ ≤ 2 max_{v∈N} ⟨v,x⟩`.
Each `⟨v, X⟩` is sub-Gaussian with proxy `σ²`, so `expectation_max_le` gives
`E[max ⟨v,X⟩] ≤ σ√(2 log|N|) ≤ σ√(2d log 5) ≤ 2σ√d`.  Combined: `E‖X‖ ≤ 4σ√d`.

Deviation from book: constant uses `log 5 ≤ 2`. -/
theorem l2_max_expectation
    {d : ℕ} [NeZero d]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: E[X] = 0; Lu-BDA §4.2 (thm:l2)
    (hcenter : ∫ ω, X ω ∂μ = 0)
    -- USER-INPUT: ⟨u, X⟩ sub-Gaussian with proxy σ²‖u‖₊²; Lu-BDA §4.2 (thm:l2)
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    -- LEAN-ONLY: Bochner integrability; implied by sub-Gaussianity in finite dimension
    (hX_int : Integrable X μ) :
    ∫ ω, ‖X ω‖ ∂μ ≤ 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) := by
  haveI : DecidableEq (EuclideanSpace ℝ (Fin d)) := Classical.decEq _
  -- *** Step 1: Construct 1/2-net ***
  let net := buildL2Net d
  let F := net.F
  let k := F.card
  have hk_pos : 0 < k := Finset.card_pos.mpr net.hF_nonempty
  haveI hk_ne : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk_pos⟩
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
  -- *** Step 2: Enumerate net as Fin k → E ***
  let e : Fin k → EuclideanSpace ℝ (Fin d) := fun j => (F.equivFin.symm j : F).val
  have he_norm : ∀ j, ‖e j‖ ≤ 1 := fun j =>
    net.hF_norm (e j) (F.equivFin.symm j).prop
  -- *** Step 3: Y j ω = ⟨e j, X ω⟩ is centered sub-Gaussian ***
  let Y : Fin k → Ω → ℝ := fun j ω => inner ℝ (e j) (X ω)
  have hY_int : ∀ j, Integrable (Y j) μ := fun j =>
    (innerSL ℝ (e j) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integrable_comp hX_int
  have hcenter_Y : ∀ j, ∫ ω, Y j ω ∂μ = 0 := fun j => by
    simp only [Y, ← innerSL_apply_apply]
    rw [(innerSL ℝ (e j)).integral_comp_comm hX_int, hcenter, map_zero]
  have hY_sg : ∀ j, IsSubGaussian (Y j) σ2 μ := fun j =>
    isSubGaussian_inner_of_norm_le hX (he_norm j)
  -- *** Step 4: Discretization — ‖X ω‖ ≤ 2 * ⨆ j, Y j ω ***
  have hdiscr : ∀ ω, ‖X ω‖ ≤ 2 * ⨆ j, Y j ω := fun ω => by
    by_cases hx0 : X ω = 0
    · simp only [hx0, norm_zero, Y, inner_zero_right, ciSup_const, mul_zero, le_refl]
    · have hx_pos : 0 < ‖X ω‖ := norm_pos_iff.mpr hx0
      -- u* = ‖X ω‖⁻¹ • X ω is a unit vector in closedBall 0 1
      let u_star := ‖X ω‖⁻¹ • X ω
      have hu_star_norm : ‖u_star‖ = 1 := norm_smul_inv_norm hx0
      have hu_star_ball : u_star ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        simp only [mem_closedBall, dist_zero_right, hu_star_norm, le_refl]
      -- Get net point v with dist u_star v ≤ 1/2
      obtain ⟨v, hv_F, hv_dist⟩ := net.hF_cover u_star hu_star_ball
      -- Find index j₀ with e j₀ = v
      have hv_in_F : v ∈ F := hv_F
      let j₀ : Fin k := F.equivFin ⟨v, hv_in_F⟩
      have he_j₀ : e j₀ = v := by
        change (F.equivFin.symm (F.equivFin ⟨v, hv_in_F⟩) : F).val = v
        rw [Equiv.symm_apply_apply]
      -- inner ℝ u_star (X ω) = ‖X ω‖
      have h_inner_ustar : inner ℝ u_star (X ω) = ‖X ω‖ := by
        simp only [u_star, real_inner_smul_left, real_inner_self_eq_norm_sq, sq]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx_pos), one_mul]
      -- Cauchy-Schwarz: ⟨v - u_star, X ω⟩ ≥ -(1/2)‖X ω‖
      have hvu : ‖v - u_star‖ ≤ 1 / 2 := by
        rw [← dist_eq_norm, dist_comm]; exact hv_dist
      have h_diff_inner : -(1 / 2) * ‖X ω‖ ≤ inner ℝ (v - u_star) (X ω) := by
        linarith [neg_abs_le (inner ℝ (v - u_star) (X ω)),
                  (abs_real_inner_le_norm (v - u_star) (X ω)).trans
                    (mul_le_mul_of_nonneg_right hvu (norm_nonneg _))]
      -- ⟨v, X ω⟩ ≥ ‖X ω‖ / 2
      have h_inner_v : ‖X ω‖ / 2 ≤ inner ℝ v (X ω) := by
        have h_split : inner ℝ v (X ω) =
            inner ℝ u_star (X ω) + inner ℝ (v - u_star) (X ω) := by
          rw [inner_sub_left]; ring
        rw [h_split, h_inner_ustar]; linarith
      -- Conclude via iSup ≥ Y j₀ ω ≥ ‖X ω‖ / 2
      have hbdd : BddAbove (Set.range (fun j => Y j ω)) := Finite.bddAbove_range _
      have hY_j₀ : Y j₀ ω = inner ℝ v (X ω) := by simp [Y, he_j₀]
      linarith [le_ciSup hbdd j₀, hY_j₀ ▸ h_inner_v]
  -- *** Step 5: Integrability of ⨆ j, Y j ***
  have hint_supr : Integrable (fun ω => ⨆ j, Y j ω) μ :=
    integrable_iSup_fin hY_int
  -- *** Step 6: Expectation bound via expectation_max_le ***
  have hE_max : ∫ ω, ⨆ j, Y j ω ∂μ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log k) :=
    expectation_max_le hcenter_Y hY_sg
  have hE_norm_le : ∫ ω, ‖X ω‖ ∂μ ≤ 2 * ∫ ω, ⨆ j, Y j ω ∂μ := by
    have h := integral_mono hX_int.norm (hint_supr.const_mul 2) (fun ω => hdiscr ω)
    rwa [integral_const_mul] at h
  -- *** Step 7: k ≤ 5^d and log k ≤ 2d ***
  have hk_le : k ≤ 5 ^ d := net.hF_card_le
  have hlog_k : Real.log k ≤ 2 * (d : ℝ) := by
    calc Real.log (k : ℝ)
        ≤ Real.log ((5 : ℕ) ^ d : ℝ) := by
              apply Real.log_le_log (by exact_mod_cast hk_pos)
              exact_mod_cast hk_le
      _ = (d : ℝ) * Real.log 5 := by push_cast; rw [Real.log_pow]
      _ ≤ (d : ℝ) * 2 := mul_le_mul_of_nonneg_left log_five_le_two (Nat.cast_nonneg d)
      _ = 2 * d := by ring
  -- *** Step 8: √(2 log k) ≤ 2√d ***
  have hsqrt_bound : Real.sqrt (2 * Real.log k) ≤ 2 * Real.sqrt (d : ℝ) := by
    have h4d : 2 * Real.log k ≤ 4 * (d : ℝ) := by linarith
    rw [show (2 : ℝ) * Real.sqrt (d : ℝ) = Real.sqrt (4 * (d : ℝ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show Real.sqrt 4 = 2 from by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]; exact Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h4d
  -- *** Step 9: Conclude ***
  calc ∫ ω, ‖X ω‖ ∂μ
      ≤ 2 * ∫ ω, ⨆ j, Y j ω ∂μ := hE_norm_le
    _ ≤ 2 * (Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log k)) :=
          mul_le_mul_of_nonneg_left hE_max (by norm_num)
    _ ≤ 2 * (Real.sqrt (σ2 : ℝ) * (2 * Real.sqrt (d : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hsqrt_bound (Real.sqrt_nonneg _)
    _ = 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) := by ring

/-!
### Tail bound — numerical algebra lemma (named sorry, ESCALATE)

The tail bound requires showing `k · exp(-(t/2)²/(2σ²)) ≤ δ` for
`t = 4σ√d + 2σ√(2 log(1/δ))` and `k ≤ 5^d`.  The proof proceeds by:
- `5^d ≤ exp(2d)` (from `log 5 ≤ 2`)
- `(t/2)² / (2σ²) = 2d + cross + log(1/δ) ≥ 2d + log(1/δ)` (cross term ≥ 0)
- So `5^d · exp(-(t/2)²/(2σ²)) ≤ exp(2d) · exp(-2d) · δ = δ`
The `σ² = 0` corner case needs separate treatment (X = 0 a.s. gives μ-measure 0).
-/

/-- Numerical core of `l2_max_tail`: the exponential product is ≤ δ.
**ESCALATE**: requires algebraic manipulation of exponentials + two corner cases
(`σ² = 0`, `log(1/δ) ≤ 0`). -/
private lemma l2_tail_numerical
    {d : ℕ} [NeZero d] {σ2 : ℝ≥0} {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hk_pos : 0 < k) (hk_le : k ≤ 5 ^ d)
    (t : ℝ) (ht : t = 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
                       2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ))) :
    (k : ℝ) * Real.exp (-(t / 2) ^ 2 / (2 * (σ2 : ℝ))) ≤ δ := by
  sorry

/-- **ℓ²-Norm Maximal Inequality — high-probability tail bound** (Lu-BDA §4.2, `thm:l2`).

For a centered sub-Gaussian random vector `X : Ω → EuclideanSpace ℝ (Fin d)` with
variance proxy `σ²‖u‖₊²` for every direction `u`, and any `δ > 0`:
```
μ {ω | 4σ√d + 2σ√(2 log(1/δ)) < ‖X ω‖} ≤ ENNReal.ofReal δ
```

Proof: `{‖X‖ > t} ⊆ {max_j ⟨e_j, X⟩ > t/2}` by discretization; apply `tail_max_le`
with net size `k ≤ 5^d` and the numerical estimate `l2_tail_numerical`.

Deviation from book: constant uses `log 5 ≤ 2`. -/
theorem l2_max_tail
    {d : ℕ} [NeZero d]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    -- USER-INPUT: E[X] = 0; Lu-BDA §4.2 (thm:l2)
    (hcenter : ∫ ω, X ω ∂μ = 0)
    -- USER-INPUT: ⟨u, X⟩ sub-Gaussian with proxy σ²‖u‖₊²; Lu-BDA §4.2 (thm:l2)
    (hX : ∀ u : EuclideanSpace ℝ (Fin d),
        IsSubGaussian (fun ω => inner ℝ u (X ω)) (σ2 * ‖u‖₊ ^ 2) μ)
    -- LEAN-ONLY: Bochner integrability; implied by sub-Gaussianity in finite dimension
    (hX_int : Integrable X μ)
    -- USER-INPUT: δ > 0; Lu-BDA §4.2 (thm:l2)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
           2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ)) < ‖X ω‖}
      ≤ ENNReal.ofReal δ := by
  haveI : DecidableEq (EuclideanSpace ℝ (Fin d)) := Classical.decEq _
  -- *** Step 1: Build net ***
  let net := buildL2Net d
  let F := net.F
  let k := F.card
  have hk_pos : 0 < k := Finset.card_pos.mpr net.hF_nonempty
  haveI hk_ne : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk_pos⟩
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk_pos
  let e : Fin k → EuclideanSpace ℝ (Fin d) := fun j => (F.equivFin.symm j : F).val
  have he_norm : ∀ j, ‖e j‖ ≤ 1 := fun j =>
    net.hF_norm (e j) (F.equivFin.symm j).prop
  -- *** Step 2: Y j ω = ⟨e j, X ω⟩ ***
  let Y : Fin k → Ω → ℝ := fun j ω => inner ℝ (e j) (X ω)
  have hcenter_Y : ∀ j, ∫ ω, Y j ω ∂μ = 0 := fun j => by
    simp only [Y, ← innerSL_apply_apply]
    rw [(innerSL ℝ (e j)).integral_comp_comm hX_int, hcenter, map_zero]
  have hY_sg : ∀ j, IsSubGaussian (Y j) σ2 μ := fun j =>
    isSubGaussian_inner_of_norm_le hX (he_norm j)
  -- *** Step 3: Discretization ‖X ω‖ ≤ 2 * ⨆ j, Y j ω ***
  have hdiscr : ∀ ω, ‖X ω‖ ≤ 2 * ⨆ j, Y j ω := fun ω => by
    by_cases hx0 : X ω = 0
    · simp only [hx0, norm_zero, Y, inner_zero_right, ciSup_const, mul_zero, le_refl]
    · have hx_pos : 0 < ‖X ω‖ := norm_pos_iff.mpr hx0
      let u_star := ‖X ω‖⁻¹ • X ω
      have hu_star_norm : ‖u_star‖ = 1 := norm_smul_inv_norm hx0
      obtain ⟨v, hv_F, hv_dist⟩ := net.hF_cover u_star
        (by simp only [mem_closedBall, dist_zero_right, hu_star_norm, le_refl])
      let j₀ : Fin k := F.equivFin ⟨v, hv_F⟩
      have he_j₀ : e j₀ = v := by
        change (F.equivFin.symm (F.equivFin ⟨v, hv_F⟩) : F).val = v
        rw [Equiv.symm_apply_apply]
      have h_inner_ustar : inner ℝ u_star (X ω) = ‖X ω‖ := by
        simp only [u_star, real_inner_smul_left, real_inner_self_eq_norm_sq, sq]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx_pos), one_mul]
      have hvu : ‖v - u_star‖ ≤ 1 / 2 := by rw [← dist_eq_norm, dist_comm]; exact hv_dist
      have h_diff_inner : -(1 / 2) * ‖X ω‖ ≤ inner ℝ (v - u_star) (X ω) := by
        linarith [neg_abs_le (inner ℝ (v - u_star) (X ω)),
                  (abs_real_inner_le_norm (v - u_star) (X ω)).trans
                    (mul_le_mul_of_nonneg_right hvu (norm_nonneg _))]
      have h_inner_v : ‖X ω‖ / 2 ≤ inner ℝ v (X ω) := by
        have h_split : inner ℝ v (X ω) =
            inner ℝ u_star (X ω) + inner ℝ (v - u_star) (X ω) := by
          rw [inner_sub_left]; ring
        rw [h_split, h_inner_ustar]; linarith
      have hbdd : BddAbove (Set.range (fun j => Y j ω)) := Finite.bddAbove_range _
      linarith [le_ciSup hbdd j₀, show Y j₀ ω = inner ℝ v (X ω) from by simp [Y, he_j₀],
                h_inner_v]
  -- *** Step 4: Apply tail_max_le + numerical bound ***
  set t := 4 * Real.sqrt (σ2 : ℝ) * Real.sqrt (d : ℝ) +
           2 * Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (1 / δ))
  have h_subset : {ω | t < ‖X ω‖} ⊆ {ω | t / 2 < ⨆ j, Y j ω} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith [hdiscr ω]
  calc μ {ω | t < ‖X ω‖}
      ≤ μ {ω | t / 2 < ⨆ j, Y j ω} := measure_mono h_subset
    _ ≤ ENNReal.ofReal ((k : ℝ) * Real.exp (-(t / 2) ^ 2 / (2 * ↑σ2))) :=
          tail_max_le hcenter_Y hY_sg (by positivity)
    _ ≤ ENNReal.ofReal δ :=
          ENNReal.ofReal_le_ofReal (l2_tail_numerical hδ hk_pos net.hF_card_le t rfl)

end StatLean.ConcentrationInequalities
