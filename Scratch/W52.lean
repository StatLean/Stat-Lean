import StatLean.HypothesisTesting.Bootstrap.Edgeworth

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform

namespace StatLean.HypothesisTesting
namespace Edgeworth

/-- The truncation error at the **third** power, weighted by the eighth. -/
lemma abs_cube_sub_cube_truncAt_le {m τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    |(x - m) ^ 3 - (truncAt m τ x - m) ^ 3| ≤ (x - m) ^ 8 / τ ^ 5 := by
  have ha : (x - m) ^ 8 = |x - m| ^ 8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rcases le_or_gt |x - m| τ with h | h
  · simp only [truncAt, if_pos h, sub_self, abs_zero]
    positivity
  · simp only [truncAt, if_neg (not_le.2 h), sub_self]
    rw [show ((0 : ℝ) ^ 3) = 0 by ring, sub_zero, le_div_iff₀ (by positivity), ha]
    have h5 : τ ^ 5 ≤ |x - m| ^ 5 := pow_le_pow_left₀ hτ.le h.le 5
    have h3 : (0 : ℝ) ≤ |x - m| ^ 3 := by positivity
    calc |(x - m) ^ 3| * τ ^ 5 = |x - m| ^ 3 * τ ^ 5 := by rw [abs_pow]
      _ ≤ |x - m| ^ 3 * |x - m| ^ 5 := by gcongr
      _ = |x - m| ^ 8 := by ring

/-- **The skewness ratio comparison, as pure arithmetic.** -/
private lemma abs_skewness_ratio_sub_le {a a' v v' : ℝ} (hv : 0 < v)
    (hlo : v / 2 ≤ v') (hhi : v' ≤ 4 * v) :
    |a' / Real.sqrt v' ^ 3 - a / Real.sqrt v ^ 3|
      ≤ 8 * |a' - a| / Real.sqrt v ^ 3 + 56 * |a| * |v' - v| / Real.sqrt v ^ 5 := by
  have hv' : 0 < v' := lt_of_lt_of_le (by linarith) hlo
  set s : ℝ := Real.sqrt v with hsdef
  set s' : ℝ := Real.sqrt v' with hs'def
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hs' : 0 < s' := Real.sqrt_pos.2 hv'
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hs'2 : s' ^ 2 = v' := Real.sq_sqrt hv'.le
  have h1 : s ≤ 2 * s' := by nlinarith
  have h2 : s' ≤ 2 * s := by nlinarith
  have hcube : s ^ 3 ≤ 8 * s' ^ 3 := by nlinarith
  have e : (s - s') * (s + s') = v - v' := by linear_combination hs2 - hs'2
  have hsd : |s - s'| ≤ |v' - v| / s := by
    rw [le_div_iff₀ hs]
    have habs : |s - s'| * (s + s') = |v - v'| := by
      rw [← abs_of_pos (show (0 : ℝ) < s + s' by linarith), ← abs_mul, e]
    calc |s - s'| * s ≤ |s - s'| * (s + s') := by nlinarith [abs_nonneg (s - s')]
      _ = |v - v'| := habs
      _ = |v' - v| := abs_sub_comm _ _
  have hnum : |s ^ 3 - s' ^ 3| ≤ 7 * s * |v' - v| := by
    have hfac : s ^ 3 - s' ^ 3 = (s - s') * (s ^ 2 + s * s' + s' ^ 2) := by ring
    rw [hfac, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ s ^ 2 + s * s' + s' ^ 2 by positivity)]
    have hb : s ^ 2 + s * s' + s' ^ 2 ≤ 7 * s ^ 2 := by nlinarith
    calc |s - s'| * (s ^ 2 + s * s' + s' ^ 2) ≤ |v' - v| / s * (7 * s ^ 2) := by
          exact mul_le_mul hsd hb (by positivity) (by positivity)
      _ = 7 * s * |v' - v| := by field_simp
  have key : a' / s' ^ 3 - a / s ^ 3
      = (a' - a) / s' ^ 3 + a * (s ^ 3 - s' ^ 3) / (s' ^ 3 * s ^ 3) := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(a' - a) / s' ^ 3| ≤ 8 * |a' - a| / s ^ 3 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < s' ^ 3 by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg (a' - a), hcube, pow_pos hs 3, pow_pos hs' 3]
  have t2 : |a * (s ^ 3 - s' ^ 3) / (s' ^ 3 * s ^ 3)| ≤ 56 * |a| * |v' - v| / s ^ 5 := by
    have hden : (0 : ℝ) < s' ^ 3 * s ^ 3 := by positivity
    rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity : (0 : ℝ) < s ^ 5),
      abs_mul]
    have hA : (0 : ℝ) ≤ |a| := abs_nonneg a
    have hV : (0 : ℝ) ≤ |v' - v| := abs_nonneg _
    calc |a| * |s ^ 3 - s' ^ 3| * s ^ 5 ≤ |a| * (7 * s * |v' - v|) * s ^ 5 := by gcongr
      _ = 7 * (|a| * |v' - v| * ((8 * s' ^ 3 - s ^ 3) * s ^ 3))
            + 7 * |a| * |v' - v| * s ^ 6 - 7 * (|a| * |v' - v| * ((8 * s' ^ 3 - s ^ 3)
              * s ^ 3)) := by ring
      _ ≤ 56 * |a| * |v' - v| * (s' ^ 3 * s ^ 3) := by
          have hp : (0 : ℝ) ≤ |a| * |v' - v| * ((8 * s' ^ 3 - s ^ 3) * s ^ 3) := by
            have : (0 : ℝ) ≤ 8 * s' ^ 3 - s ^ 3 := by linarith
            positivity
          nlinarith [hp]
  linarith

/-- Every power of the centred truncation is integrable: the summand is bounded by `τ`. -/
lemma integrable_truncAt_sub_pow (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (k : ℕ) : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ k) F := by
  refine Integrable.mono' (integrable_const (τ ^ k))
    (((measurable_truncAt m τ).sub_const m).pow_const k).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_truncAt_sub_le hτ x) k

/-- The mean of the truncated law, as the centring shift. -/
lemma integral_id_map_truncAt_eq (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    (∫ s, s ∂(F.map (truncAt m τ))) = m + ∫ x, (truncAt m τ x - m) ∂F := by
  have hTm : Measurable (truncAt m τ) := measurable_truncAt m τ
  have hI1 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 1) F :=
    integrable_truncAt_sub_pow F m hτ 1
  simp only [pow_one] at hI1
  have hmap : (∫ s, s ∂(F.map (truncAt m τ))) = ∫ x, truncAt m τ x ∂F :=
    integral_map hTm.aemeasurable (by fun_prop)
  have hsplit : ∫ x, truncAt m τ x ∂F = (∫ x, ((truncAt m τ x - m) + m) ∂F) := by
    congr 1; funext x; ring
  rw [hmap, hsplit, integral_add hI1 (integrable_const m), integral_const]
  simp [add_comm]

/-- The variance of the truncated law, in the moments of the centred truncation. -/
lemma variance_map_truncAt_eq (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    Var[fun t : ℝ => t; F.map (truncAt m τ)]
      = (∫ x, (truncAt m τ x - m) ^ 2 ∂F) - (∫ x, (truncAt m τ x - m) ∂F) ^ 2 := by
  have hTm : Measurable (truncAt m τ) := measurable_truncAt m τ
  haveI : IsProbabilityMeasure (F.map (truncAt m τ)) :=
    Measure.isProbabilityMeasure_map hTm.aemeasurable
  have hI1 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 1) F :=
    integrable_truncAt_sub_pow F m hτ 1
  simp only [pow_one] at hI1
  have hI2 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 2) F :=
    integrable_truncAt_sub_pow F m hτ 2
  set δ : ℝ := ∫ x, (truncAt m τ x - m) ∂F with hδ
  rw [variance_eq_integral (by fun_prop), integral_id_map_truncAt_eq F m hτ, ← hδ,
    integral_map hTm.aemeasurable (by fun_prop)]
  have hpt : (fun x : ℝ => (truncAt m τ x - (m + δ)) ^ 2)
      = fun x : ℝ => (truncAt m τ x - m) ^ 2 - 2 * δ * (truncAt m τ x - m) + δ ^ 2 := by
    funext x; ring
  have e1 : ∫ x, ((truncAt m τ x - m) ^ 2 - 2 * δ * (truncAt m τ x - m) + δ ^ 2) ∂F
      = (∫ x, ((truncAt m τ x - m) ^ 2 - 2 * δ * (truncAt m τ x - m)) ∂F)
        + ∫ _x : ℝ, δ ^ 2 ∂F :=
    integral_add (hI2.sub (hI1.const_mul (2 * δ))) (integrable_const _)
  have e2 : ∫ x, ((truncAt m τ x - m) ^ 2 - 2 * δ * (truncAt m τ x - m)) ∂F
      = (∫ x, (truncAt m τ x - m) ^ 2 ∂F) - ∫ x, 2 * δ * (truncAt m τ x - m) ∂F :=
    integral_sub hI2 (hI1.const_mul (2 * δ))
  have e3 : ∫ x, 2 * δ * (truncAt m τ x - m) ∂F = 2 * δ * δ := by
    rw [integral_const_mul, ← hδ]
  rw [hpt, e1, e2, e3]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The third central moment of the truncated law, in the moments of the centred truncation. -/
lemma integral_third_central_map_truncAt_eq (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ t, (t - ∫ s, s ∂(F.map (truncAt m τ))) ^ 3 ∂(F.map (truncAt m τ)))
      = (∫ x, (truncAt m τ x - m) ^ 3 ∂F)
        - 3 * (∫ x, (truncAt m τ x - m) ∂F) * (∫ x, (truncAt m τ x - m) ^ 2 ∂F)
        + 2 * (∫ x, (truncAt m τ x - m) ∂F) ^ 3 := by
  have hTm : Measurable (truncAt m τ) := measurable_truncAt m τ
  have hI1 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 1) F :=
    integrable_truncAt_sub_pow F m hτ 1
  simp only [pow_one] at hI1
  have hI2 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 2) F :=
    integrable_truncAt_sub_pow F m hτ 2
  have hI3 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 3) F :=
    integrable_truncAt_sub_pow F m hτ 3
  set δ : ℝ := ∫ x, (truncAt m τ x - m) ∂F with hδ
  rw [integral_id_map_truncAt_eq F m hτ, ← hδ,
    integral_map hTm.aemeasurable (by fun_prop)]
  have hpt : (fun x : ℝ => (truncAt m τ x - (m + δ)) ^ 3)
      = fun x : ℝ => (truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2
          + 3 * δ ^ 2 * (truncAt m τ x - m) - δ ^ 3 := by
    funext x; ring
  have e1 : ∫ x, ((truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2
        + 3 * δ ^ 2 * (truncAt m τ x - m) - δ ^ 3) ∂F
      = (∫ x, ((truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2
            + 3 * δ ^ 2 * (truncAt m τ x - m)) ∂F) - ∫ _x : ℝ, δ ^ 3 ∂F :=
    integral_sub ((hI3.sub (hI2.const_mul (3 * δ))).add (hI1.const_mul (3 * δ ^ 2)))
      (integrable_const _)
  have e2 : ∫ x, ((truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2
        + 3 * δ ^ 2 * (truncAt m τ x - m)) ∂F
      = (∫ x, ((truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2) ∂F)
        + ∫ x, 3 * δ ^ 2 * (truncAt m τ x - m) ∂F :=
    integral_add (hI3.sub (hI2.const_mul (3 * δ))) (hI1.const_mul (3 * δ ^ 2))
  have e3 : ∫ x, ((truncAt m τ x - m) ^ 3 - 3 * δ * (truncAt m τ x - m) ^ 2) ∂F
      = (∫ x, (truncAt m τ x - m) ^ 3 ∂F) - ∫ x, 3 * δ * (truncAt m τ x - m) ^ 2 ∂F :=
    integral_sub hI3 (hI2.const_mul (3 * δ))
  have e4 : ∫ x, 3 * δ * (truncAt m τ x - m) ^ 2 ∂F
      = 3 * δ * ∫ x, (truncAt m τ x - m) ^ 2 ∂F := integral_const_mul _ _
  have e5 : ∫ x, 3 * δ ^ 2 * (truncAt m τ x - m) ∂F = 3 * δ ^ 2 * δ := by
    rw [integral_const_mul, ← hδ]
  rw [hpt, e1, e2, e3, e4, e5]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **The skewness of a truncated law, in the moments of the centred truncation.** -/
lemma skewness_map_truncAt_eq (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    skewness (F.map (truncAt m τ))
      = ((∫ x, (truncAt m τ x - m) ^ 3 ∂F)
          - 3 * (∫ x, (truncAt m τ x - m) ∂F) * (∫ x, (truncAt m τ x - m) ^ 2 ∂F)
          + 2 * (∫ x, (truncAt m τ x - m) ∂F) ^ 3)
        / Real.sqrt ((∫ x, (truncAt m τ x - m) ^ 2 ∂F)
            - (∫ x, (truncAt m τ x - m) ∂F) ^ 2) ^ 3 := by
  rw [skewness, integral_third_central_map_truncAt_eq F m hτ, variance_map_truncAt_eq F m hτ]

/-- The truncation defect at the second moment. -/
lemma abs_integral_sq_truncAt_sub_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 2) F)
    (hF4 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 4) F)
    {τ : ℝ} (hτ : 0 < τ) :
    |(∫ x, (truncAt (∫ s, s ∂F) τ x - ∫ s, s ∂F) ^ 2 ∂F) - ∫ x, (x - ∫ s, s ∂F) ^ 2 ∂F|
      ≤ (∫ x, (x - ∫ s, s ∂F) ^ 4 ∂F) / τ ^ 2 := by
  set m : ℝ := ∫ s, s ∂F with hm
  have hI2 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 2) F :=
    integrable_truncAt_sub_pow F m hτ.le 2
  rw [← integral_sub hI2 hF2]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono (hI2.sub hF2).abs (hF4.div_const (τ ^ 2)) ?_).trans_eq ?_
  · intro x
    calc |(truncAt m τ x - m) ^ 2 - (x - m) ^ 2|
        = |(x - m) ^ 2 - (truncAt m τ x - m) ^ 2| := abs_sub_comm _ _
      _ ≤ (x - m) ^ 4 / τ ^ 2 := abs_sq_sub_sq_truncAt_le hτ x
  · rw [integral_div]

/-- The truncation defect at the third moment, priced by the eighth. -/
lemma abs_integral_cube_truncAt_sub_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF3 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 3) F)
    (hF8 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 8) F)
    {τ : ℝ} (hτ : 0 < τ) :
    |(∫ x, (truncAt (∫ s, s ∂F) τ x - ∫ s, s ∂F) ^ 3 ∂F) - ∫ x, (x - ∫ s, s ∂F) ^ 3 ∂F|
      ≤ (∫ x, (x - ∫ s, s ∂F) ^ 8 ∂F) / τ ^ 5 := by
  set m : ℝ := ∫ s, s ∂F with hm
  have hI3 : Integrable (fun x : ℝ => (truncAt m τ x - m) ^ 3) F :=
    integrable_truncAt_sub_pow F m hτ.le 3
  rw [← integral_sub hI3 hF3]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono (hI3.sub hF3).abs (hF8.div_const (τ ^ 5)) ?_).trans_eq ?_
  · intro x
    calc |(truncAt m τ x - m) ^ 3 - (x - m) ^ 3|
        = |(x - m) ^ 3 - (truncAt m τ x - m) ^ 3| := abs_sub_comm _ _
      _ ≤ (x - m) ^ 8 / τ ^ 5 := abs_cube_sub_cube_truncAt_le hτ x
  · rw [integral_div]

/-- Truncation never increases the second moment. -/
lemma integral_sq_truncAt_le (F : Measure ℝ) [IsProbabilityMeasure F] (m : ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hF2 : Integrable (fun x : ℝ => (x - m) ^ 2) F) :
    (∫ x, (truncAt m τ x - m) ^ 2 ∂F) ≤ ∫ x, (x - m) ^ 2 ∂F := by
  refine integral_mono (integrable_truncAt_sub_pow F m hτ 2) hF2 fun x => ?_
  have h := abs_truncAt_sub_le_abs m τ x
  nlinarith [abs_nonneg (truncAt m τ x - m), sq_abs (truncAt m τ x - m), sq_abs (x - m)]

/-- **ITEM 4 OF THE WAVE-49 RESIDUE — THE SKEWNESS COMPARISON, AT A GENERAL TRUNCATION
LEVEL.**  The skewness of the truncated law differs from that of the sampling law by the
truncation defects of the second and third moments, transported through the ratio. -/
theorem abs_skewness_map_truncAt_sub_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF1 : Integrable (fun x : ℝ => x) F)
    (hF2 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 2) F)
    (hF3 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 3) F)
    (hF4 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 4) F)
    (hF8 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 8) F)
    (hFvar : 0 < Var[fun t : ℝ => t; F]) {τ e₂ e₄ e₈ : ℝ} (hτ : 0 < τ)
    (h2 : (∫ x, (x - ∫ s, s ∂F) ^ 4 ∂F) / τ ^ 2 ≤ e₂)
    (h4 : (∫ x, (x - ∫ s, s ∂F) ^ 4 ∂F) / τ ^ 3 ≤ e₄)
    (h8 : (∫ x, (x - ∫ s, s ∂F) ^ 8 ∂F) / τ ^ 5 ≤ e₈) (he₄ : 0 ≤ e₄)
    (hwin : e₂ + e₄ ^ 2 ≤ Var[fun t : ℝ => t; F] / 2) :
    |skewness (F.map (truncAt (∫ s, s ∂F) τ)) - skewness F|
      ≤ 8 * (e₈ + 3 * e₄ * Var[fun t : ℝ => t; F] + 2 * e₄ ^ 3)
          / Real.sqrt Var[fun t : ℝ => t; F] ^ 3
        + 56 * |∫ x, (x - ∫ s, s ∂F) ^ 3 ∂F| * (e₂ + e₄ ^ 2)
          / Real.sqrt Var[fun t : ℝ => t; F] ^ 5 := by
  set m : ℝ := ∫ s, s ∂F with hm
  set v : ℝ := Var[fun t : ℝ => t; F] with hv
  have hvint : v = ∫ x, (x - m) ^ 2 ∂F := by
    rw [hv, variance_eq_integral (by fun_prop)]
  set A : ℝ := ∫ x, (truncAt m τ x - m) ^ 3 ∂F with hA
  set B : ℝ := ∫ x, (truncAt m τ x - m) ^ 2 ∂F with hB
  set δ : ℝ := ∫ x, (truncAt m τ x - m) ∂F with hδ
  set μ₃ : ℝ := ∫ x, (x - m) ^ 3 ∂F with hμ₃
  have hτ4 : (0 : ℝ) ≤ ∫ x, (x - m) ^ 4 ∂F :=
    integral_nonneg fun x => by positivity
  -- the three defects
  have hδb : |δ| ≤ e₄ := by
    have h := abs_integral_truncAt_sub_le F hF1 hF4 hτ
    rw [integral_id_map_truncAt_eq F m hτ.le, ← hδ, ← hm] at h
    simpa using h.trans h4
  have hBb : |B - v| ≤ e₂ := by
    have h := abs_integral_sq_truncAt_sub_le F hF2 hF4 hτ
    rw [← hB, ← hvint] at h
    exact h.trans h2
  have hAb : |A - μ₃| ≤ e₈ := by
    have h := abs_integral_cube_truncAt_sub_le F hF3 hF8 hτ
    rw [← hA, ← hμ₃] at h
    exact h.trans h8
  have hBnn : 0 ≤ B := integral_nonneg fun x => by positivity
  have hBv : B ≤ v := by rw [hvint]; exact integral_sq_truncAt_le F m hτ.le hF2
  -- the variance window
  have hδ2 : δ ^ 2 ≤ e₄ ^ 2 := by nlinarith [abs_nonneg δ, sq_abs δ]
  have hlo : v / 2 ≤ B - δ ^ 2 := by
    have := abs_le.1 hBb
    nlinarith [sq_nonneg δ]
  have hhi : B - δ ^ 2 ≤ 4 * v := by
    have := abs_le.1 hBb
    nlinarith [sq_nonneg δ, sq_nonneg e₄]
  -- the two comparisons the ratio consumes
  have habs : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y)
    simpa [sub_eq_add_neg] using h
  have hnum : |(A - 3 * δ * B + 2 * δ ^ 3) - μ₃| ≤ e₈ + 3 * e₄ * v + 2 * e₄ ^ 3 := by
    have h1 : |3 * δ * B| ≤ 3 * e₄ * v := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg hBnn]
      exact mul_le_mul (by linarith [hδb]) hBv hBnn (by linarith [he₄])
    have h2 : |2 * δ ^ 3| ≤ 2 * e₄ ^ 3 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow]
      have h3 : |δ| ^ 3 ≤ e₄ ^ 3 := pow_le_pow_left₀ (abs_nonneg δ) hδb 3
      linarith
    have e : (A - 3 * δ * B + 2 * δ ^ 3) - μ₃ = ((A - μ₃) - 3 * δ * B) + 2 * δ ^ 3 := by ring
    have s1 : |((A - μ₃) - 3 * δ * B) + 2 * δ ^ 3| ≤ |(A - μ₃) - 3 * δ * B| + |2 * δ ^ 3| :=
      abs_add_le _ _
    have s2 : |(A - μ₃) - 3 * δ * B| ≤ |A - μ₃| + |3 * δ * B| := habs _ _
    rw [e]
    linarith
  have hden : |(B - δ ^ 2) - v| ≤ e₂ + e₄ ^ 2 := by
    have := abs_le.1 hBb
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg δ, hδ2]
  -- the skewness identities
  have hskew : skewness (F.map (truncAt m τ))
      = (A - 3 * δ * B + 2 * δ ^ 3) / Real.sqrt (B - δ ^ 2) ^ 3 := by
    rw [skewness_map_truncAt_eq F m hτ.le, ← hA, ← hB, ← hδ]
  have hskewF : skewness F = μ₃ / Real.sqrt v ^ 3 := rfl
  rw [hskew, hskewF]
  refine (abs_skewness_ratio_sub_le hFvar hlo hhi).trans ?_
  have hs3 : (0 : ℝ) < Real.sqrt v ^ 3 := by positivity
  have hs5 : (0 : ℝ) < Real.sqrt v ^ 5 := by positivity
  gcongr

/-- The window of the skewness comparison at `τ = √n`, as pure arithmetic. -/
private lemma skewness_window {μ₄ v nR : ℝ} (h₄ : 0 ≤ μ₄) (hv : 0 < v) (hn : 1 ≤ nR)
    (hthr : 2 * (μ₄ + μ₄ ^ 2) / v ≤ nR) : μ₄ / nR + (μ₄ / nR) ^ 2 ≤ v / 2 := by
  have hn0 : (0 : ℝ) < nR := lt_of_lt_of_le one_pos hn
  have hnn : (0 : ℝ) ≤ nR ^ 2 - nR := by nlinarith
  have h1 : (μ₄ / nR) ^ 2 ≤ μ₄ ^ 2 / nR := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_nonneg (sq_nonneg μ₄) hnn]
  have h2 : (2 : ℝ) * (μ₄ + μ₄ ^ 2) ≤ nR * v := by
    rw [div_le_iff₀ hv] at hthr
    exact hthr
  have h3 : μ₄ / nR + μ₄ ^ 2 / nR ≤ v / 2 := by
    have e : μ₄ / nR + μ₄ ^ 2 / nR = (μ₄ + μ₄ ^ 2) / nR := by ring
    rw [e, div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 2)]
    nlinarith [h2]
  linarith

/-- The `n`-ledger of the skewness comparison at `τ = √n`, as pure arithmetic. -/
private lemma skewness_ledger {μ₃ μ₄ μ₈ v s₃ s₅ nR : ℝ} (h₄ : 0 ≤ μ₄) (h₈ : 0 ≤ μ₈)
    (hv : 0 < v) (hs₃ : 0 < s₃) (hs₅ : 0 < s₅) (hn : 1 ≤ nR) :
    8 * (μ₈ / nR + 3 * (μ₄ / nR) * v + 2 * (μ₄ / nR) ^ 3) / s₃
        + 56 * |μ₃| * (μ₄ / nR + (μ₄ / nR) ^ 2) / s₅
      ≤ (8 * (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / s₃
          + 56 * |μ₃| * (μ₄ + μ₄ ^ 2) / s₅ + 1) / nR := by
  have hn0 : (0 : ℝ) < nR := lt_of_lt_of_le one_pos hn
  have hinv3 : (1 : ℝ) / nR ^ 3 ≤ 1 / nR := by
    refine one_div_le_one_div_of_le hn0 ?_
    nlinarith [mul_nonneg (mul_nonneg hn0.le (sub_nonneg.2 hn)) (by linarith : (0 : ℝ) ≤ nR + 1)]
  have hinv2 : (1 : ℝ) / nR ^ 2 ≤ 1 / nR := by
    refine one_div_le_one_div_of_le hn0 ?_
    nlinarith
  have k1 : μ₈ / nR + 3 * (μ₄ / nR) * v + 2 * (μ₄ / nR) ^ 3
      ≤ (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / nR := by
    have e : (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / nR
        - (μ₈ / nR + 3 * (μ₄ / nR) * v + 2 * (μ₄ / nR) ^ 3)
        = 2 * μ₄ ^ 3 * (1 / nR - 1 / nR ^ 3) := by
      field_simp
      ring
    have hp : (0 : ℝ) ≤ 2 * μ₄ ^ 3 * (1 / nR - 1 / nR ^ 3) :=
      mul_nonneg (by nlinarith [pow_nonneg h₄ 3]) (by linarith)
    linarith
  have k2 : μ₄ / nR + (μ₄ / nR) ^ 2 ≤ (μ₄ + μ₄ ^ 2) / nR := by
    have e : (μ₄ + μ₄ ^ 2) / nR - (μ₄ / nR + (μ₄ / nR) ^ 2)
        = μ₄ ^ 2 * (1 / nR - 1 / nR ^ 2) := by
      field_simp
      ring
    have hp : (0 : ℝ) ≤ μ₄ ^ 2 * (1 / nR - 1 / nR ^ 2) :=
      mul_nonneg (sq_nonneg μ₄) (by linarith)
    linarith
  have hrw : (8 * (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / s₃
        + 56 * |μ₃| * (μ₄ + μ₄ ^ 2) / s₅ + 1) / nR
      = 8 * ((μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / nR) / s₃
        + 56 * |μ₃| * ((μ₄ + μ₄ ^ 2) / nR) / s₅ + 1 / nR := by
    field_simp
  rw [hrw]
  have t1 : 8 * (μ₈ / nR + 3 * (μ₄ / nR) * v + 2 * (μ₄ / nR) ^ 3) / s₃
      ≤ 8 * ((μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / nR) / s₃ := by gcongr
  have t2 : 56 * |μ₃| * (μ₄ / nR + (μ₄ / nR) ^ 2) / s₅
      ≤ 56 * |μ₃| * ((μ₄ + μ₄ ^ 2) / nR) / s₅ := by gcongr
  have hpos : (0 : ℝ) < 1 / nR := by positivity
  linarith

/-- **ITEM 4 OF THE WAVE-49 RESIDUE, AT THE CHAIN'S OWN TRUNCATION LEVEL `τ = √n`.**  The
skewness of the truncated law and the skewness of the sampling law differ by `O(n⁻¹)`. -/
theorem exists_abs_skewness_map_truncAt_sqrt_sub_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF1 : Integrable (fun x : ℝ => x) F)
    (hF2 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 2) F)
    (hF3 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 3) F)
    (hF4 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 4) F)
    (hF8 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 8) F)
    (hFvar : 0 < Var[fun t : ℝ => t; F]) :
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n →
      |skewness (F.map (truncAt (∫ s, s ∂F) (Real.sqrt (n : ℝ)))) - skewness F| ≤ C / n := by
  set m : ℝ := ∫ s, s ∂F with hm
  set v : ℝ := Var[fun t : ℝ => t; F] with hv
  set μ₃ : ℝ := ∫ x, (x - m) ^ 3 ∂F with hμ₃
  set μ₄ : ℝ := ∫ x, (x - m) ^ 4 ∂F with hμ₄
  set μ₈ : ℝ := ∫ x, (x - m) ^ 8 ∂F with hμ₈
  have hμ₄nn : 0 ≤ μ₄ := integral_nonneg fun x => by positivity
  have hμ₈nn : 0 ≤ μ₈ := integral_nonneg fun x => by positivity
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hFvar
  have hs3 : (0 : ℝ) < Real.sqrt v ^ 3 := pow_pos hsv 3
  have hs5 : (0 : ℝ) < Real.sqrt v ^ 5 := pow_pos hsv 5
  have hnum1 : (0 : ℝ) ≤ 8 * (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / Real.sqrt v ^ 3 := by
    refine div_nonneg ?_ hs3.le
    nlinarith [pow_nonneg hμ₄nn 3, hFvar.le]
  have hnum2 : (0 : ℝ) ≤ 56 * |μ₃| * (μ₄ + μ₄ ^ 2) / Real.sqrt v ^ 5 := by
    refine div_nonneg ?_ hs5.le
    nlinarith [abs_nonneg μ₃, sq_nonneg μ₄]
  refine ⟨8 * (μ₈ + 3 * μ₄ * v + 2 * μ₄ ^ 3) / Real.sqrt v ^ 3
      + 56 * |μ₃| * (μ₄ + μ₄ ^ 2) / Real.sqrt v ^ 5 + 1,
    max 1 ⌈2 * (μ₄ + μ₄ ^ 2) / v⌉₊, by linarith,
    lt_of_lt_of_le Nat.one_pos (le_max_left 1 _), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hceil : ⌈2 * (μ₄ + μ₄ ^ 2) / v⌉₊ ≤ n := le_trans (le_max_right 1 _) hn
  have hthr : 2 * (μ₄ + μ₄ ^ 2) / v ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  set sn : ℝ := Real.sqrt (n : ℝ) with hsn
  have hsn0 : 0 < sn := Real.sqrt_pos.2 hn0
  have hsq : sn ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hsn1 : (1 : ℝ) ≤ sn := by nlinarith
  have hb2 : μ₄ / sn ^ 2 ≤ μ₄ / (n : ℝ) := by rw [hsq]
  have hb4 : μ₄ / sn ^ 3 ≤ μ₄ / (n : ℝ) := by
    refine div_le_div_of_nonneg_left hμ₄nn hn0 ?_
    have h3 : sn ^ 3 = (n : ℝ) * sn := by
      have hh : sn ^ 3 = sn ^ 2 * sn := by ring
      rw [hh, hsq]
    rw [h3]; nlinarith
  have hb8 : μ₈ / sn ^ 5 ≤ μ₈ / (n : ℝ) := by
    refine div_le_div_of_nonneg_left hμ₈nn hn0 ?_
    have h5 : sn ^ 5 = (n : ℝ) ^ 2 * sn := by
      have hh : sn ^ 5 = (sn ^ 2) ^ 2 * sn := by ring
      rw [hh, hsq]
    rw [h5]; nlinarith
  have hcore := abs_skewness_map_truncAt_sub_le F hF1 hF2 hF3 hF4 hF8 hFvar (τ := sn)
    (e₂ := μ₄ / (n : ℝ)) (e₄ := μ₄ / (n : ℝ)) (e₈ := μ₈ / (n : ℝ)) hsn0 hb2 hb4 hb8
    (div_nonneg hμ₄nn hn0.le) (skewness_window hμ₄nn hFvar hnR hthr)
  exact hcore.trans (skewness_ledger hμ₄nn hμ₈nn hFvar hs3 hs5 hnR)

end Edgeworth
end StatLean.HypothesisTesting
