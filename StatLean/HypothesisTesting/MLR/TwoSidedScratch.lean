import StatLean.HypothesisTesting.MLR.TwoSided

/-!
# Scratch: brick (a) of the `isUMP_twoSided` quantile-sweep roadmap
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting.Scratch2

/-- local copy of the private `twoSidedVal` -/
noncomputable def tsVal (C₁ C₂ γ₁ γ₂ t : ℝ) : ℝ :=
  if t = C₁ then γ₁ else if t = C₂ then γ₂ else if C₁ < t then if t < C₂ then 1 else 0 else 0

/-- The `p`-sublevel set of a distribution function is nonempty and bounded below. -/
lemma cdf_level_nonempty_bddBelow (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    {y : ℝ | p ≤ cdf ν y}.Nonempty ∧ BddBelow {y : ℝ | p ≤ cdf ν y} := by
  constructor
  · obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop ν).eventually_const_lt hp1).exists
    exact ⟨y, hy.le⟩
  · obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot ν).eventually_lt_const hp0)
    refine ⟨b, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy
    by_contra hcon
    exact absurd (hb y (not_le.mp hcon).le) (not_lt.mpr hy)

/-- The two defining inequalities of a quantile: the distribution function has reached `p` at
`quantile F p`, and its left limit there has not passed `p`. -/
lemma cdf_quantile_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ cdf ν (quantile (⇑(cdf ν)) p) ∧
      Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) p) ≤ p := by
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
    fun y => (cdf ν).right_continuous y
  obtain ⟨hne, hbdd⟩ := cdf_level_nonempty_bddBelow ν hp0 hp1
  have hA : p ≤ cdf ν (quantile (⇑(cdf ν)) p) :=
    (quantile_le_iff hmono hrc hne hbdd).mp le_rfl
  refine ⟨hA, ?_⟩
  have hB : ∀ y, y < quantile (⇑(cdf ν)) p → cdf ν y < p := by
    intro y hy
    by_contra h
    exact absurd ((quantile_le_iff hmono hrc hne hbdd).mpr (not_lt.mp h)) (not_le.mpr hy)
  have htend : Tendsto (⇑(cdf ν)) (𝓝[<] (quantile (⇑(cdf ν)) p))
      (𝓝 (Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) p))) :=
    hmono.tendsto_leftLim _
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hB y hy).le

/-- **Brick (a): the randomized window attached to a quantile pair.**

For a law `ν` on the line, a level `α` and a starting level `s`, the two-sided test whose
boundaries are the `s`- and `(s+α)`-quantiles of `ν` has size exactly `α`, the boundary
weights being the fractions of the two boundary atoms that the level window `(s, s+α)` cuts
off. -/
lemma exists_twoSided_constants_window (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α s : ℝ} (hα0 : 0 < α) (hs0 : 0 < s) (hs1 : s + α < 1)
    (hlt : quantile (⇑(cdf ν)) s < quantile (⇑(cdf ν)) (s + α)) :
    ∃ γ₁ γ₂ : ℝ, γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∫ t, tsVal (quantile (⇑(cdf ν)) s) (quantile (⇑(cdf ν)) (s + α)) γ₁ γ₂ t ∂ν = α := by
  classical
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  set F : ℝ → ℝ := ⇑(cdf ν) with hF
  set C₁ : ℝ := quantile F s with hC₁
  set C₂ : ℝ := quantile F (s + α) with hC₂
  obtain ⟨hA₁, hL₁⟩ := cdf_quantile_bounds ν hs0 (by linarith)
  obtain ⟨hA₂, hL₂⟩ := cdf_quantile_bounds ν (by linarith) hs1
  set L₁ : ℝ := Function.leftLim F C₁ with hL₁def
  set L₂ : ℝ := Function.leftLim F C₂ with hL₂def
  -- the three masses
  have hm₁ : (ν {C₁}).toReal = F C₁ - L₁ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_singleton C₁,
      ENNReal.toReal_ofReal (by simpa [hL₁def] using hmono.leftLim_le (le_refl C₁))]
  have hm₂ : (ν {C₂}).toReal = F C₂ - L₂ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_singleton C₂,
      ENNReal.toReal_ofReal (by simpa [hL₂def] using hmono.leftLim_le (le_refl C₂))]
  have hFle : F C₁ ≤ L₂ := hmono.le_leftLim hlt
  have hmo : (ν (Set.Ioo C₁ C₂)).toReal = L₂ - F C₁ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_Ioo,
      ENNReal.toReal_ofReal (by simpa [hL₂def] using sub_nonneg.2 hFle)]
  -- the boundary weights
  set γ₁ : ℝ := if (ν {C₁}).toReal = 0 then 0 else (F C₁ - s) / (ν {C₁}).toReal with hγ₁
  set γ₂ : ℝ := if (ν {C₂}).toReal = 0 then 0 else (s + α - L₂) / (ν {C₂}).toReal with hγ₂
  have hkey₁ : γ₁ * (ν {C₁}).toReal = F C₁ - s := by
    rw [hγ₁]
    by_cases h : (ν {C₁}).toReal = 0
    · rw [if_pos h, zero_mul]
      rw [hm₁] at h
      have : L₁ = F C₁ := by linarith
      linarith [hL₁, hA₁, this]
    · rw [if_neg h, div_mul_cancel₀ _ h]
  have hkey₂ : γ₂ * (ν {C₂}).toReal = s + α - L₂ := by
    rw [hγ₂]
    by_cases h : (ν {C₂}).toReal = 0
    · rw [if_pos h, zero_mul]
      rw [hm₂] at h
      have : L₂ = F C₂ := by linarith
      linarith [hL₂, hA₂, this]
    · rw [if_neg h, div_mul_cancel₀ _ h]
  have hγ₁mem : γ₁ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ₁]
    by_cases h : (ν {C₁}).toReal = 0
    · rw [if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < (ν {C₁}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
      rw [if_neg h]
      refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
      rw [div_le_one hpos, hm₁]
      linarith
  have hγ₂mem : γ₂ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ₂]
    by_cases h : (ν {C₂}).toReal = 0
    · rw [if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < (ν {C₂}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
      rw [if_neg h]
      refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
      rw [div_le_one hpos, hm₂]
      linarith
  refine ⟨γ₁, γ₂, hγ₁mem, hγ₂mem, ?_⟩
  -- the test is a sum of three indicators
  have hne : C₁ ≠ C₂ := ne_of_lt hlt
  have hfun : (fun t => tsVal C₁ C₂ γ₁ γ₂ t)
      = fun t => γ₁ * Set.indicator {C₁} (1 : ℝ → ℝ) t
        + γ₂ * Set.indicator {C₂} (1 : ℝ → ℝ) t
        + Set.indicator (Set.Ioo C₁ C₂) (1 : ℝ → ℝ) t := by
    funext t
    simp only [tsVal, Set.indicator_apply, Set.mem_singleton_iff, Set.mem_Ioo, Pi.one_apply]
    by_cases h1 : t = C₁
    · subst h1; simp [hne]
    · by_cases h2 : t = C₂
      · subst h2; simp [h1]
      · by_cases h3 : C₁ < t
        · by_cases h4 : t < C₂ <;> simp [h1, h2, h3, h4]
        · simp [h1, h2, h3]
  rw [hfun]
  have hi₁ : Integrable (fun t : ℝ => Set.indicator {C₁} (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton C₁)
  have hi₂ : Integrable (fun t : ℝ => Set.indicator {C₂} (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton C₂)
  have hi₃ : Integrable (fun t : ℝ => Set.indicator (Set.Ioo C₁ C₂) (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioo
  have hA : Integrable (fun t : ℝ => γ₁ * Set.indicator {C₁} (1 : ℝ → ℝ) t
      + γ₂ * Set.indicator {C₂} (1 : ℝ → ℝ) t) ν := (hi₁.const_mul γ₁).add (hi₂.const_mul γ₂)
  rw [integral_add hA hi₃,
    integral_add (hi₁.const_mul γ₁) (hi₂.const_mul γ₂), integral_const_mul, integral_const_mul,
    integral_indicator_one (measurableSet_singleton C₁),
    integral_indicator_one (measurableSet_singleton C₂),
    integral_indicator_one measurableSet_Ioo]
  simp only [measureReal_def]
  rw [hkey₁, hkey₂, hmo]
  ring

end StatLean.HypothesisTesting.Scratch2
