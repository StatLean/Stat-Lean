import StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct

/-!
# Squared Hellinger distance — book form and tensorization (Wainwright §15.1.3)

Wainwright's squared Hellinger distance (Eq. (15.9))

`H²(ℙ ‖ ℚ) = ∫ (√p − √q)² dν ∈ [0, 2]`

is the squared `L²(ν)`-distance between the square-root densities. We define it with the
canonical common dominating measure `ξ = ℙ + ℚ`, and reuse the StatLean Hellinger-product
machinery (`StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct`, a cross-area
`ForMathlib` import) for the tensorization properties:

* `sqHellinger_le_two` — `H²(ℙ ‖ ℚ) ≤ 2` (Eq. (15.9));
* `sqHellinger_pi_le_nsmul` — the i.i.d. bound `H²(ℙ^{1:n} ‖ ℚ^{1:n}) ≤ n · H²(ℙ ‖ ℚ)`
  (Eq. (15.12b)), via `1 − (1 − x)ⁿ ≤ n x`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9)/(15.12).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Squared Hellinger distance** (Wainwright Eq. (15.9)): `H²(ℙ ‖ ℚ) = ∫ (√p − √q)² dν`,
the squared `L²`-distance between square-root densities, taken here against the common
dominating measure `ξ = ℙ + ℚ` (`p = dℙ/dξ`, `q = dℚ/dξ`).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
noncomputable def sqHellinger (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((Real.sqrt (μ.rnDeriv (μ + ν) x).toReal
      - Real.sqrt (ν.rnDeriv (μ + ν) x).toReal) ^ 2) ∂(μ + ν)

/-- The squared Hellinger distance is symmetric. -/
theorem sqHellinger_comm (μ ν : Measure α) : sqHellinger μ ν = sqHellinger ν μ := by
  unfold sqHellinger
  rw [add_comm ν μ]
  refine lintegral_congr fun x => ?_
  congr 1
  ring

/-- **The squared Hellinger distance lies in `[0, 2]`** (Wainwright Eq. (15.9)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
theorem sqHellinger_le_two (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν ≤ 2 := by
  have hμ : μ ≪ μ + ν := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hν : ν ≪ μ + ν := by rw [add_comm]; exact (Measure.le_add_right le_rfl).absolutelyContinuous
  calc sqHellinger μ ν
      ≤ ∫⁻ x, (μ.rnDeriv (μ + ν) x + ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
        refine lintegral_mono_ae ?_
        filter_upwards [μ.rnDeriv_ne_top (μ + ν), ν.rnDeriv_ne_top (μ + ν)] with x hp hq
        set P := μ.rnDeriv (μ + ν) x
        set Q := ν.rnDeriv (μ + ν) x
        have hp0 : 0 ≤ P.toReal := ENNReal.toReal_nonneg
        have hq0 : 0 ≤ Q.toReal := ENNReal.toReal_nonneg
        have h2 : (Real.sqrt P.toReal - Real.sqrt Q.toReal) ^ 2 ≤ P.toReal + Q.toReal := by
          have e1 := Real.sq_sqrt hp0
          have e2 := Real.sq_sqrt hq0
          nlinarith [Real.sqrt_nonneg P.toReal, Real.sqrt_nonneg Q.toReal,
            mul_nonneg (Real.sqrt_nonneg P.toReal) (Real.sqrt_nonneg Q.toReal)]
        calc ENNReal.ofReal ((Real.sqrt P.toReal - Real.sqrt Q.toReal) ^ 2)
            ≤ ENNReal.ofReal (P.toReal + Q.toReal) := ENNReal.ofReal_le_ofReal h2
          _ = ENNReal.ofReal P.toReal + ENNReal.ofReal Q.toReal := ENNReal.ofReal_add hp0 hq0
          _ = P + Q := by rw [ENNReal.ofReal_toReal hp, ENNReal.ofReal_toReal hq]
    _ = ∫⁻ x, μ.rnDeriv (μ + ν) x ∂(μ + ν) + ∫⁻ x, ν.rnDeriv (μ + ν) x ∂(μ + ν) :=
        lintegral_add_left (Measure.measurable_rnDeriv _ _) _
    _ = 2 := by
        rw [Measure.lintegral_rnDeriv hμ, Measure.lintegral_rnDeriv hν, measure_univ, measure_univ,
          one_add_one_eq_two]

-- Crux of Eq. (15.12b): bridge `sqHellinger` to the StatLean `eLpNorm` form and reuse
-- `HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample` together with
-- `1 − (1 − x)ⁿ ≤ n x`. This is non-trivial coercion/`eLpNorm`-squaring work across the
-- two Hellinger encodings and is left as a named debt.
private lemma sqHellinger_pi_le_nsmul_aux (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      ≤ n • sqHellinger μ ν := by
  sorry -- TODO(mmx): Eq. (15.12b) — bridge to eLpNorm Hellinger product + 1-(1-x)ⁿ ≤ n·x

/-- **I.i.d. tensorization bound for the squared Hellinger distance** (Wainwright Eq. (15.12b)):
`H²(ℙ^{1:n} ‖ ℚ^{1:n}) ≤ n · H²(ℙ ‖ ℚ)`, obtained from the affinity-product identity (Eq. (15.12a))
and the elementary inequality `1 − (1 − x)ⁿ ≤ n x`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.12b). -/
theorem sqHellinger_pi_le_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      ≤ n • sqHellinger μ ν :=
  sqHellinger_pi_le_nsmul_aux n μ ν

end StatLean.Minimaxity
