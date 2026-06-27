import StatLean.Minimaxity.ForMathlib.TotalVariation
import StatLean.Minimaxity.ForMathlib.KLDivergence

/-!
# Pinsker–Csiszár–Kullback inequality — Lemma 15.2 (Wainwright §15.1.3)

The total variation distance is controlled by the Kullback–Leibler divergence:
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`  (Eq. (15.8)).

Wainwright outlines the proof in Exercise 15.6: reduce to the Bernoulli case via the partition
`A = {p ≥ q}` and Jensen's inequality. We state it with the `ℝ≥0∞` square root (`rpow (1/2)`),
so the bound is vacuously true when the KL divergence is infinite.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2.
-/

open MeasureTheory InformationTheory Real Set
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- Derivative of `a ↦ a · log(a/c)` (a fixed nonzero `c`): `a · log(a/c) ↦ log(y/c) + 1`.
Reusable building block for the scalar Bernoulli–Pinsker convexity argument. -/
private lemma mul_log_div_hasDerivAt {c : ℝ} (hc : c ≠ 0) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun a => a * Real.log (a / c)) (Real.log (y / c) + 1) y := by
  have hgy : HasDerivAt (fun a => a / c) (1 / c) y := (hasDerivAt_id y).div_const c
  have hlog : HasDerivAt (fun a => Real.log (a / c)) y⁻¹ y := by
    have h := (Real.hasDerivAt_log (div_ne_zero hy hc)).comp y hgy
    convert h using 1
    field_simp
  have hp := (hasDerivAt_id y).mul hlog
  convert hp using 1
  simp only [id_eq, one_mul]
  rw [mul_inv_cancel₀ hy]

/-- **Scalar Bernoulli–Pinsker inequality** (Wainwright Exercise 15.6, pointwise step):
for `a, b ∈ (0, 1)`,
`2 (a − b)² ≤ a log(a/b) + (1 − a) log((1 − a)/(1 − b)) = D(Bern(a) ‖ Bern(b))`.

This is the elementary one-variable calculus fact underlying Pinsker's inequality:
the function `F(a) = a log(a/b) + (1 − a) log((1 − a)/(1 − b)) − 2 (a − b)²` satisfies
`F(b) = F'(b) = 0` and `F''(a) = 1/(a(1 − a)) − 4 ≥ 0` (since `a(1 − a) ≤ 1/4`), hence is
convex with minimum `0` at `a = b`. -/
private lemma bernoulli_pinsker_scalar {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  have hb0' : b ≠ 0 := hb0.ne'
  have hb1' : (1 - b) ≠ 0 := by linarith
  -- the function whose nonnegativity we want, its derivative `G`, and second derivative `H`
  set g : ℝ → ℝ := fun a =>
    a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) - 2 * (a - b) ^ 2 with hg_def
  set G : ℝ → ℝ := fun x => Real.log (x / b) - Real.log ((1 - x) / (1 - b)) - 4 * (x - b) with hG_def
  set H : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4 with hH_def
  -- g'(x) = G x on (0,1)
  have hg' : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt g (G x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxne : x ≠ 0 := hx0.ne'
    have hsne : (1 - x) ≠ 0 := by linarith
    have t1 := mul_log_div_hasDerivAt hb0' hxne
    have hsub : HasDerivAt (fun a => (1:ℝ) - a) (-1) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have t2base := mul_log_div_hasDerivAt hb1' hsne
    have t2 := t2base.comp x hsub
    have t3 : HasDerivAt (fun a => 2 * (a - b) ^ 2) (4 * (x - b)) x := by
      have h := ((hasDerivAt_id x).sub_const b).pow 2
      have h2 := h.const_mul (2 : ℝ)
      convert h2 using 1
      simp only [id_eq]; ring
    have hsum := (t1.add t2).sub t3
    convert hsum using 1
    ring
  -- G'(x) = H x on (0,1)
  have hG' : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt G (H x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxne : x ≠ 0 := hx0.ne'
    have hsne : (1 - x) ≠ 0 := by linarith
    have hgx : HasDerivAt (fun a => a / b) (1 / b) x := (hasDerivAt_id x).div_const b
    have hl1 : HasDerivAt (fun a => Real.log (a / b)) x⁻¹ x := by
      have h := (Real.hasDerivAt_log (div_ne_zero hxne hb0')).comp x hgx
      convert h using 1; field_simp
    have hsub : HasDerivAt (fun a => (1:ℝ) - a) (-1) x := by
      simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have hgs : HasDerivAt (fun a => a / (1 - b)) (1 / (1 - b)) (1 - x) :=
      (hasDerivAt_id (1 - x)).div_const (1 - b)
    have hl2base : HasDerivAt (fun u => Real.log (u / (1 - b))) (1 - x)⁻¹ (1 - x) := by
      have h := (Real.hasDerivAt_log (div_ne_zero hsne hb1')).comp (1 - x) hgs
      convert h using 1; field_simp
    have hl2 := hl2base.comp x hsub
    have t3 : HasDerivAt (fun a => 4 * (a - b)) (4 : ℝ) x := by
      have h := ((hasDerivAt_id x).sub_const b).const_mul (4 : ℝ)
      convert h using 1; ring
    have hsum := (hl1.sub hl2).sub t3
    convert hsum using 1
    ring
  -- H x ≥ 0 on (0,1), since 1/(x(1−x)) ≥ 4
  have hH_nonneg : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ H x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hs0 : 0 < 1 - x := by linarith
    have hid : x⁻¹ + (1 - x)⁻¹ = 1 / (x * (1 - x)) := by field_simp; ring
    have h4 : 4 ≤ x⁻¹ + (1 - x)⁻¹ := by
      rw [hid, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * x - 1)]
    simp only [hH_def]; linarith
  -- G is monotone on (0,1) (its derivative H is nonnegative)
  have hGmono : MonotoneOn G (Ioo (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · exact fun x hx => (hG' x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      exact fun x hx => (hG' x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hG' x hx).deriv]
      exact hH_nonneg x hx
  have hbmem : b ∈ Ioo (0:ℝ) 1 := ⟨hb0, hb1⟩
  -- G b = 0 and g b = 0 (tangent at the minimizer)
  have hGb : G b = 0 := by
    simp only [hG_def, div_self hb0', div_self hb1', Real.log_one, sub_self, mul_zero]
  have hgb : g b = 0 := by
    simp only [hg_def, div_self hb0', div_self hb1', Real.log_one, mul_zero, sub_self]
    ring
  -- conclude g a ≥ 0 by monotonicity of g on [b,a] (resp. antitonicity on [a,b])
  have hga : 0 ≤ g a := by
    rcases le_total b a with hba | hab
    · have hsub : Icc b a ⊆ Ioo (0:ℝ) 1 := fun x hx =>
        ⟨lt_of_lt_of_le hb0 hx.1, lt_of_le_of_lt hx.2 ha1⟩
      have hgmono : MonotoneOn g (Icc b a) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
        · exact fun x hx => (hg' x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hg' x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hxin : x ∈ Icc b a := interior_subset hx
          rw [(hg' x (hsub hxin)).deriv]
          exact hGb ▸ hGmono hbmem (hsub hxin) hxin.1
      have := hgmono (left_mem_Icc.mpr hba) (right_mem_Icc.mpr hba) hba
      rw [hgb] at this; exact this
    · have hsub : Icc a b ⊆ Ioo (0:ℝ) 1 := fun x hx =>
        ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
      have hganti : AntitoneOn g (Icc a b) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
        · exact fun x hx => (hg' x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hg' x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hxin : x ∈ Icc a b := interior_subset hx
          rw [(hg' x (hsub hxin)).deriv]
          exact hGb ▸ hGmono (hsub hxin) hbmem hxin.2
      have := hganti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
      rw [hgb] at this; exact this
  simp only [hg_def] at hga
  linarith

/-- **Data-processing core of Pinsker's inequality** (Wainwright Exercise 15.6).

The KL divergence dominates `2 · ‖ℙ − ℚ‖²_TV`. By the data-processing inequality for KL under
the binary partition `A = {q ≤ p}` (densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`),
`D(ℚ ‖ ℙ) ≥ D(Bern(ℚ A) ‖ Bern(ℙ A))`, and on the optimal set `A` the total variation equals
`ℙ A − ℚ A`. Combined with the scalar Bernoulli–Pinsker inequality
`bernoulli_pinsker_scalar` this gives the bound. -/
private lemma klDiv_ge_two_mul_tvDist_sq (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * (tvDist μ ν).toReal ^ 2) ≤ klDiv ν μ := by
  sorry -- TODO(mmx, Wainwright Ex 15.6): KL data-processing under the 2-cell partition
        -- A = {q ≤ p} (klDiv monotone under the indicator pushforward), the optimal-set
        -- identity tvDist = ℙ A − ℚ A (cf. `tvDist_eq_lintegral_tsub`), then
        -- `bernoulli_pinsker_scalar` with a = (ν A).toReal, b = (μ A).toReal.

/-- **Bernoulli crux of Pinsker's inequality** (Wainwright Exercise 15.6).

With densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`, the half-`L¹` form of total variation
is bounded by the KL divergence through the data-processing reduction to the Bernoulli partition
`A = {p ≥ q}` and the pointwise inequality
`2 (δ_p − δ_q)² ≤ δ_p log(δ_p/δ_q) + (1 − δ_p) log((1 − δ_p)/(1 − δ_q))` followed by Jensen.
This is the genuine analytic core; the public theorem `pinsker_tv_le_kl` follows by the density
form `tvDist_eq_half_lintegral`. -/
private lemma pinsker_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [← tvDist_eq_half_lintegral]
  by_cases hkl : klDiv ν μ = ⊤
  · rw [hkl, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top),
        ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact le_top
  · have htv1 : tvDist μ ν ≤ 1 := tvDist_le_one μ ν
    have htvne : tvDist μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top htv1
    set t : ℝ := (tvDist μ ν).toReal with ht
    set k : ℝ := (klDiv ν μ).toReal with hk
    have ht_nn : 0 ≤ t := ENNReal.toReal_nonneg
    have hk_nn : 0 ≤ k := ENNReal.toReal_nonneg
    have htv_eq : tvDist μ ν = ENNReal.ofReal t := (ENNReal.ofReal_toReal htvne).symm
    have hkl_eq : klDiv ν μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hkl).symm
    -- Core scalar bound `2 t² ≤ k` from the data-processing lemma.
    have hcore : 2 * t ^ 2 ≤ k := by
      have h := klDiv_ge_two_mul_tvDist_sq μ ν
      rw [← ht, hkl_eq] at h
      exact (ENNReal.ofReal_le_ofReal_iff hk_nn).mp h
    -- Assemble in `ℝ≥0∞`.
    rw [htv_eq, hkl_eq,
        show (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal k = ENNReal.ofReal (k / 2) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat,
              div_eq_mul_inv, mul_comm],
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht_nn).symm]
    exact Real.sqrt_le_sqrt (by linarith)

/-- **Pinsker–Csiszár–Kullback inequality** (Wainwright Lemma 15.2, Eq. (15.8)):
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2. -/
theorem pinsker_tv_le_kl (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact pinsker_half_lintegral_le μ ν

end StatLean.Minimaxity
