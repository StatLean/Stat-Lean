import StatLean.Bayesian.BernsteinVonMises.PriorSmallBall

/-! SCRATCH FILE (temporary, not imported anywhere). The weighted prior tail split. -/

open MeasureTheory ProbabilityTheory Filter Topology
open StatLean.Bayesian
open scoped ENNReal

namespace ScratchB

variable {k : ℕ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- The parameter-side tail set corresponding to the local ball `‖h‖ ≥ R`. -/
def tailSet (θ₀ : EuclideanSpace ℝ (Fin k)) (R : ℝ) (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {θ | R / Real.sqrt n ≤ ‖θ - θ₀‖}

theorem measurableSet_tailSet (θ₀ : EuclideanSpace ℝ (Fin k)) (R : ℝ) (n : ℕ) :
    MeasurableSet (tailSet θ₀ R n) :=
  measurableSet_le measurable_const (by fun_prop)

/-! Bricks supplied elsewhere (leave these two `sorry`s ALONE — they are being proved in a
parallel file; you may use them freely). -/

/-- **The pointwise weight-absorption inequality** (given). -/
theorem weighted_exp_split {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
      (1 + (Real.sqrt n * r) ^ p) * Real.exp (-c * n * min (r ^ 2) 1)
        ≤ K * Real.exp (-(c / 2) * n * min (r ^ 2) 1)
          + K * (1 + r ^ p) * Real.exp (-(c / 2) * n) := by
  sorry

/-- `n^{kk/2} e^{-a n} → 0` (given). -/
theorem sqrt_pow_mul_exp_neg_tendsto (kk : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.sqrt n ^ kk * Real.exp (-a * n)) atTop (𝓝 0) := by
  sorry

/-! ### Helper lemmas -/

/-- Elementary `rpow` subadditivity up to the factor `2 ^ p`. -/
private lemma rpow_add_le_two_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by linarith) hmax hp
  have h2 : (2 * max a b) ^ p = 2 ^ p * max a b ^ p :=
    Real.mul_rpow (by norm_num) (le_trans ha (le_max_left a b))
  have h3 : max a b ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := Real.rpow_nonneg ha p; linarith
    · rw [max_eq_left h]; have := Real.rpow_nonneg hb p; linarith
  have h4 : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
  calc (a + b) ^ p ≤ (2 * max a b) ^ p := h1
    _ = 2 ^ p * max a b ^ p := h2
    _ ≤ 2 ^ p * (a ^ p + b ^ p) := by nlinarith

/-- Measurability of `θ ↦ ‖θ - θ₀‖ ^ p` (`rpow`, `0 ≤ p`). -/
private lemma measurable_norm_sub_rpow (θ₀ : EuclideanSpace ℝ (Fin k)) {p : ℝ} (hp : 0 ≤ p) :
    Measurable fun θ : EuclideanSpace ℝ (Fin k) => ‖θ - θ₀‖ ^ p :=
  ((Real.continuous_rpow_const hp).comp
    (by fun_prop : Continuous fun θ : EuclideanSpace ℝ (Fin k) => ‖θ - θ₀‖)).measurable

/-! ### THE TARGET -/

/-- **The weighted Step-A tail split** (vdV p. 148). -/
theorem weighted_prior_tail_tendsto
    (hπ : HasLocalDensity π θ₀ r₀ f) {p : ℝ} (hp : 0 ≤ p)
    (hmom : ∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π < ∞) {c : ℝ} (hc : 0 < c)
    {Mseq : ℕ → ℝ} (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n ^ k) *
        ∫⁻ θ in tailSet θ₀ (Mseq n) n,
          ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
            Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hsplit⟩ := weighted_exp_split hp hc
  have hc2 : (0 : ℝ) < c / 2 := half_pos hc
  -- measurability of the two auxiliary integrands
  have hmG1 : ∀ n : ℕ, Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) := by
    intro n; fun_prop
  have hmG2 : Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) :=
    (measurable_const.add (measurable_norm_sub_rpow θ₀ hp)).ennreal_ofReal
  have hmMom : Measurable fun θ : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (‖θ‖ ^ p) :=
    (((Real.continuous_rpow_const hp).comp continuous_norm).measurable).ennreal_ofReal
  -- Step 4: the `p`-moment integral of `‖θ - θ₀‖` is finite
  have hbd : ∀ θ : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ≤
      1 + ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (‖θ‖ ^ p) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
    intro θ
    have hn0 : (0 : ℝ) ≤ ‖θ‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    have hn1 : (0 : ℝ) ≤ ‖θ₀‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    have h2p : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) p
    have h1 : ‖θ - θ₀‖ ≤ ‖θ‖ + ‖θ₀‖ := norm_sub_le θ θ₀
    have h2 : ‖θ - θ₀‖ ^ p ≤ (‖θ‖ + ‖θ₀‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) h1 hp
    have h3 : (‖θ‖ + ‖θ₀‖) ^ p ≤ 2 ^ p * (‖θ‖ ^ p + ‖θ₀‖ ^ p) :=
      rpow_add_le_two_rpow (norm_nonneg _) (norm_nonneg _) hp
    calc ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p)
        ≤ ENNReal.ofReal (1 + 2 ^ p * (‖θ‖ ^ p + ‖θ₀‖ ^ p)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = 1 + ENNReal.ofReal (2 ^ p) *
            (ENNReal.ofReal (‖θ‖ ^ p) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul h2p, ENNReal.ofReal_add hn0 hn1]
  have hCfin : (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) ≠ ∞ := by
    have hle : (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) ≤
        1 + ENNReal.ofReal (2 ^ p) *
          ((∫⁻ θ, ENNReal.ofReal (‖θ‖ ^ p) ∂π) + ENNReal.ofReal (‖θ₀‖ ^ p)) := by
      refine le_trans (lintegral_mono hbd) (le_of_eq ?_)
      rw [lintegral_add_left measurable_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left hmMom]
      simp
    refine ne_top_of_le_ne_top ?_ hle
    refine (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ?_⟩).ne
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hmom, ENNReal.ofReal_lt_top⟩)
  -- Step 1: the pointwise `ℝ≥0∞` bound
  have key : ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin k)),
      ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
          Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1))
          + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
              * ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) := by
    intro n θ
    refine le_trans (ENNReal.ofReal_le_ofReal (hsplit n ‖θ - θ₀‖ (norm_nonneg _))) (le_of_eq ?_)
    have hp1 : (0 : ℝ) ≤ K * Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1) :=
      mul_nonneg hK.le (Real.exp_pos _).le
    have hrp : (0 : ℝ) ≤ 1 + ‖θ - θ₀‖ ^ p := by
      have := Real.rpow_nonneg (norm_nonneg (θ - θ₀)) p; linarith
    have hp2 : (0 : ℝ) ≤ K * (1 + ‖θ - θ₀‖ ^ p) * Real.exp (-(c / 2) * n) :=
      mul_nonneg (mul_nonneg hK.le hrp) (Real.exp_pos _).le
    have hp3 : (0 : ℝ) ≤ K * Real.exp (-(c / 2) * n) :=
      mul_nonneg hK.le (Real.exp_pos _).le
    rw [ENNReal.ofReal_add hp1 hp2, ENNReal.ofReal_mul hK.le]
    congr 1
    rw [show K * (1 + ‖θ - θ₀‖ ^ p) * Real.exp (-(c / 2) * n)
        = K * Real.exp (-(c / 2) * n) * (1 + ‖θ - θ₀‖ ^ p) from by ring,
      ENNReal.ofReal_mul hp3, ENNReal.ofReal_mul hK.le]
  -- Step 2: integrate the pointwise bound over the tail set
  have hint : ∀ n : ℕ,
      (∫⁻ θ in tailSet θ₀ (Mseq n) n, ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
          Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) ≤
        ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
            ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
          + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
              * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) := by
    intro n
    have hne : ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n)) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    calc (∫⁻ θ in tailSet θ₀ (Mseq n) n, ENNReal.ofReal ((1 + (Real.sqrt n * ‖θ - θ₀‖) ^ p) *
            Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
        ≤ ∫⁻ θ in tailSet θ₀ (Mseq n) n,
            (ENNReal.ofReal K *
                ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1))
              + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                  * ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p)) ∂π := lintegral_mono (key n)
      _ = ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
              ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
            + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
                    ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) := by
          rw [lintegral_add_left (measurable_const.mul (hmG1 n)),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ hne]
      _ ≤ ENNReal.ofReal K * (∫⁻ θ in tailSet θ₀ (Mseq n) n,
              ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
            + ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(c / 2) * n))
                * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π) :=
          add_le_add le_rfl (mul_le_mul_right (setLIntegral_le_lintegral _ _) _)
  -- Step 3 / 5: the two limits
  have hA : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt n ^ k) *
      ∫⁻ θ in tailSet θ₀ (Mseq n) n,
        ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π) atTop (𝓝 0) :=
    StatLean.Bayesian.prior_tail_split hπ hc2 hM
  have hB : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-(c / 2) * n))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (sqrt_pow_mul_exp_neg_tendsto k hc2)
    simpa using this
  -- Step 6: squeeze
  have hU : Tendsto (fun n : ℕ =>
      ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in tailSet θ₀ (Mseq n) n,
            ENNReal.ofReal (Real.exp (-(c / 2) * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
        + ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt n ^ k * Real.exp (-(c / 2) * n))
            * (∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hA
      (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hB
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h1 h2
    have h3 := ENNReal.Tendsto.mul_const (b := ∫⁻ θ, ENNReal.ofReal (1 + ‖θ - θ₀‖ ^ p) ∂π)
      h2 (Or.inr hCfin)
    rw [zero_mul] at h3
    simpa using h1.add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
  have h := mul_le_mul_right (hint n) (ENNReal.ofReal (Real.sqrt n ^ k))
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.sqrt n ^ k)]
  ring

end ScratchB
