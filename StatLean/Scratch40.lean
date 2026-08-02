import StatLean.HypothesisTesting.Bootstrap.Edgeworth

/-! Scratch module for wave 40. Deleted before the final commit. -/

namespace StatLean.HypothesisTesting

open MeasureTheory

noncomputable def surrogateSlopeBound (r x v₀ : ℝ) : ℝ :=
  36 / 25 * |x| * |r| * (1 / 2 + 3 * |v₀| * |r| / 4)

noncomputable def surrogateDefect (r x v₀ K L : ℝ) : ℝ :=
  |r| / 2 * (K * L) * L + 3 * r ^ 2 / 2 * (6 / 5 * |x|) * (K * L) ^ 2
    + r ^ 2 / 2 * (K * L) ^ 3 + 3 * r ^ 2 / 8 * (6 / 5 * |x|) * L ^ 2
    + 3 * r ^ 2 / 4 * (K * L) * |v₀| * L + 3 * r ^ 2 / 8 * (K * L) * L ^ 2

lemma surrogateDefect_nonneg (r x v₀ : ℝ) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) :
    0 ≤ surrogateDefect r x v₀ K L := by
  unfold surrogateDefect; positivity

lemma abs_le_surrogateSlopeBound {r x v₀ m₀ κ : ℝ} (hm₀ : |m₀| ≤ 6 / 5 * |x|)
    (hκ : |κ| ≤ 6 / 5 * |m₀| * |r| * (1 / 2 + 3 * |v₀| * |r| / 4)) :
    |κ| ≤ surrogateSlopeBound r x v₀ := by
  refine hκ.trans ?_
  unfold surrogateSlopeBound
  have h1 : (0 : ℝ) ≤ |r| * (1 / 2 + 3 * |v₀| * |r| / 4) := by positivity
  nlinarith [h1, hm₀]

lemma abs_sub_affine_centre_le' {r x v₀ h m₀ m κ K L : ℝ}
    (hm₀b : |m₀| ≤ 6 / 5 * |x|) (hκb : |κ| ≤ K) (hhb : |h| ≤ L)
    (hm0 : (m₀ - m₀ * v₀ * r / 2 + m₀ ^ 3 * r ^ 2 / 2 + 3 * m₀ * v₀ ^ 2 * r ^ 2 / 8) = x)
    (hm : (m - m * (v₀ + h) * r / 2 + m ^ 3 * r ^ 2 / 2
      + 3 * m * (v₀ + h) ^ 2 * r ^ 2 / 8) = x)
    (hκ : (1 - v₀ * r / 2 + 3 * m₀ ^ 2 * r ^ 2 / 2 + 3 * v₀ ^ 2 * r ^ 2 / 8) * κ
        + (-(m₀ * r / 2) + 3 * m₀ * v₀ * r ^ 2 / 4) = 0) :
    |m - (m₀ + κ * h)| ≤ 6 / 5 * surrogateDefect r x v₀ K L := by
  have hK : (0 : ℝ) ≤ K := (abs_nonneg κ).trans hκb
  have hL : (0 : ℝ) ≤ L := (abs_nonneg h).trans hhb
  refine (abs_sub_affine_centre_le hm0 hm hκ).trans ?_
  have e1 : (κ * h) ^ 2 = (|κ| * |h|) ^ 2 := by rw [← abs_mul, sq_abs]
  have e2 : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  rw [e1, e2]
  unfold surrogateDefect
  gcongr <;> positivity

theorem measure_abs_surrogate_window_slab_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {U V : Ω → ℝ} {r x w v₀ L A η₀ ρ : ℝ} (hw : 0 ≤ w) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hslab : ∀ κ' c' w' : ℝ, 0 ≤ w' →
      (P {ω | |U ω - κ' * V ω - c'| ≤ w'}).toReal ≤ A * w' + η₀)
    (htail : (P {ω | L < |V ω - v₀|}).toReal ≤ ρ) :
    (P {ω | |(U ω - U ω * V ω * r / 2 + U ω ^ 3 * r ^ 2 / 2
        + 3 * U ω * V ω ^ 2 * r ^ 2 / 8) - x| ≤ w}).toReal
      ≤ A * (6 / 5 * w + 6 / 5 * surrogateDefect r x v₀ (surrogateSlopeBound r x v₀) L)
        + η₀ + ρ := by
  obtain ⟨m₀, hm₀b, hm₀⟩ := exists_surrogate_centre r v₀ x
  obtain ⟨κ, hκlin, hκb⟩ := exists_surrogate_slope r m₀ v₀
  have hK0 : (0 : ℝ) ≤ surrogateSlopeBound r x v₀ := by
    unfold surrogateSlopeBound; positivity
  have hκK : |κ| ≤ surrogateSlopeBound r x v₀ := abs_le_surrogateSlopeBound hm₀b hκb
  set W : ℝ := 6 / 5 * w + 6 / 5 * surrogateDefect r x v₀ (surrogateSlopeBound r x v₀) L
    with hWdef
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    have := surrogateDefect_nonneg r x v₀ hK0 hL
    linarith
  have hsub : {ω | |(U ω - U ω * V ω * r / 2 + U ω ^ 3 * r ^ 2 / 2
        + 3 * U ω * V ω ^ 2 * r ^ 2 / 8) - x| ≤ w}
      ⊆ {ω | |U ω - κ * V ω - (m₀ - κ * v₀)| ≤ W} ∪ {ω | L < |V ω - v₀|} := by
    intro ω hω
    by_cases hv : L < |V ω - v₀|
    · exact Or.inr hv
    · refine Or.inl ?_
      simp only [Set.mem_setOf_eq]
      push_neg at hv
      obtain ⟨m, -, hm⟩ := exists_surrogate_centre r (V ω) x
      have hVeq : v₀ + (V ω - v₀) = V ω := by ring
      have hm' : (m - m * (v₀ + (V ω - v₀)) * r / 2 + m ^ 3 * r ^ 2 / 2
          + 3 * m * (v₀ + (V ω - v₀)) ^ 2 * r ^ 2 / 8) = x := by rw [hVeq]; exact hm
      have h1 : |U ω - m| ≤ 6 / 5 * w := abs_sub_surrogate_centre_le hm hω
      have h2 : |m - (m₀ + κ * (V ω - v₀))|
          ≤ 6 / 5 * surrogateDefect r x v₀ (surrogateSlopeBound r x v₀) L :=
        abs_sub_affine_centre_le' hm₀b hκK hv hm₀ hm' hκlin
      have hid : U ω - κ * V ω - (m₀ - κ * v₀)
          = (U ω - m) + (m - (m₀ + κ * (V ω - v₀))) := by ring
      have : |U ω - κ * V ω - (m₀ - κ * v₀)| ≤ |U ω - m| + |m - (m₀ + κ * (V ω - v₀))| := by
        rw [hid]; exact abs_add_le _ _
      rw [hWdef]
      linarith
  have hfin : ∀ S : Set Ω, P S ≠ ⊤ := fun S => measure_ne_top P S
  have h1 : P {ω | |(U ω - U ω * V ω * r / 2 + U ω ^ 3 * r ^ 2 / 2
        + 3 * U ω * V ω ^ 2 * r ^ 2 / 8) - x| ≤ w}
      ≤ P {ω | |U ω - κ * V ω - (m₀ - κ * v₀)| ≤ W} + P {ω | L < |V ω - v₀|} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) h1
  rw [ENNReal.toReal_add (hfin _) (hfin _)] at h2
  have h3 := hslab κ (m₀ - κ * v₀) W hW0
  linarith

theorem measure_abs_deltaSurrogate_sub_le_of_slab
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {G : Ω → EuclideanSpace ℝ (Fin 2)} {σ r x w v₀ L A η₀ ρ : ℝ}
    (hw : 0 ≤ w) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hslab : ∀ κ' c' w' : ℝ, 0 ≤ w' →
      (P {ω | |G ω 0 / σ - κ' * (G ω 1 / σ ^ 2) - c'| ≤ w'}).toReal ≤ A * w' + η₀)
    (htail : (P {ω | L < |G ω 1 / σ ^ 2 - v₀|}).toReal ≤ ρ) :
    (P {ω | |deltaSurrogate σ r (G ω) - x| ≤ w}).toReal
      ≤ A * (6 / 5 * w + 6 / 5 * surrogateDefect r x v₀ (surrogateSlopeBound r x v₀) L)
        + η₀ + ρ := by
  have hset : {ω | |deltaSurrogate σ r (G ω) - x| ≤ w}
      = {ω | |((G ω 0 / σ) - (G ω 0 / σ) * (G ω 1 / σ ^ 2) * r / 2
          + (G ω 0 / σ) ^ 3 * r ^ 2 / 2
          + 3 * (G ω 0 / σ) * (G ω 1 / σ ^ 2) ^ 2 * r ^ 2 / 8) - x| ≤ w} := rfl
  rw [hset]
  exact measure_abs_surrogate_window_slab_le P (U := fun ω => G ω 0 / σ)
    (V := fun ω => G ω 1 / σ ^ 2) hw hL hA hslab htail

lemma ledger_optimum_cube {a b L : ℝ} (hL : 0 < L) (hb : a * L ^ 6 = b) :
    a * L ^ 2 + b / L ^ 4 = 2 * (a * L ^ 2) ∧ (a * L ^ 2) ^ 3 = a ^ 2 * b := by
  have hL4 : (L : ℝ) ^ 4 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [← hb]
    field_simp
    ring
  · rw [← hb]; ring

theorem measure_abs_gt_le_fourth_moment_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Ω → ℝ}
    (hg4 : Integrable (fun ω => g ω ^ 4) P) {L : ℝ} (hL : 0 < L) :
    (P {ω | L < |g ω|}).toReal ≤ (∫ ω, g ω ^ 4 ∂P) / L ^ 4 := by
  have hmk := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => g ω ^ 4) (Filter.Eventually.of_forall fun ω => by positivity)
    hg4 (L ^ 4)
  have hsub : {ω | L < |g ω|} ⊆ {ω | L ^ 4 ≤ g ω ^ 4} := by
    intro ω hω
    have hω' : L < |g ω| := hω
    have hpow : L ^ 4 ≤ |g ω| ^ 4 := pow_le_pow_left₀ hL.le hω'.le 4
    have habs : |g ω| ^ 4 = g ω ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g ω ^ 4)]
    rw [habs] at hpow
    exact hpow
  have hmono : (P {ω | L < |g ω|}).toReal ≤ (P {ω | L ^ 4 ≤ g ω ^ 4}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 4)]
  have hmk' : L ^ 4 * (P {ω | L ^ 4 ≤ g ω ^ 4}).toReal ≤ ∫ ω, g ω ^ 4 ∂P := by
    simpa [measureReal_def] using hmk
  nlinarith [hmono, hmk', (by positivity : (0 : ℝ) < L ^ 4)]

end StatLean.HypothesisTesting
