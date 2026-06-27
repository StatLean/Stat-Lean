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
open AsymptoticStatistics.ForMathlib.HellingerProduct

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
  refine lintegral_congr (fun x => ?_)
  congr 1
  ring

/-- Common absolute-continuity facts for the canonical dominating measure `ξ = μ + ν`. -/
private theorem absCont_left (μ ν : Measure α) : μ ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

private theorem absCont_right (μ ν : Measure α) : ν ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

/-- **Bridge to the Bochner form.** The `ℝ≥0∞`-valued definition of `sqHellinger` equals
`ENNReal.ofReal` of the real `L²`-residual integral `∫ (√p − √q)² dξ` (with `ξ = μ + ν`),
since the integrand is nonnegative and integrable (the square-root density residual is in
`L²(ξ)`). This lets us reuse the real-valued StatLean affinity machinery. -/
private theorem sqHellinger_eq_ofReal_integral (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν = ENNReal.ofReal
      (∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
              - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν)) := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  have hint :=
    (hellinger_per_sample_residual_memLp_two hμ hν).integrable_sq
  unfold sqHellinger
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- **The squared Hellinger distance lies in `[0, 2]`** (Wainwright Eq. (15.9)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
theorem sqHellinger_le_two (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν ≤ 2 := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  rw [sqHellinger_eq_ofReal_integral, integral_per_sample_residual_sq_eq hμ hν]
  have hA := integral_sqrt_mul_sqrt_nonneg μ ν (μ + ν)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Bridge to the StatLean product form.** The squared Hellinger distance of the `n`-fold
i.i.d. products, against its canonical dominating measure `Measure.pi μ + Measure.pi ν`, equals
`ENNReal.ofReal` of the per-coordinate-product residual integral against `Measure.pi (μ + ν)`
(the dominating measure used by `StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct`).

This packages two standard measure-theoretic facts about the squared Hellinger functional:
(i) the Radon–Nikodym derivative of a product measure factorises coordinatewise,
`(Measure.pi μ).rnDeriv (Measure.pi ξ) =ᵃᵉ ∏ⱼ μ.rnDeriv ξ`, and
(ii) the squared Hellinger integral is invariant under the choice of common dominating measure
(here switching `Measure.pi μ + Measure.pi ν` for `Measure.pi (μ + ν)`).

-- TODO(mmx, Wainwright Eq. (15.12)): discharge the product-rnDeriv factorisation and
-- dominating-measure invariance. Genuine measure-theoretic lemma (no Mathlib `rnDeriv_pi`),
-- lifted per CLAUDE.md §2 as a named, well-defined sub-lemma. -/
private theorem sqHellinger_pi_eq_ofReal_product_integral (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = ENNReal.ofReal
          (∫ X : Fin n → α,
            ((∏ j, Real.sqrt (μ.rnDeriv (μ + ν) (X j)).toReal)
              - ∏ j, Real.sqrt (ν.rnDeriv (μ + ν) (X j)).toReal) ^ 2
            ∂(Measure.pi fun _ : Fin n => (μ + ν))) := by
  sorry

/-- **I.i.d. tensorization bound for the squared Hellinger distance** (Wainwright Eq. (15.12b)):
`H²(ℙ^{1:n} ‖ ℚ^{1:n}) ≤ n · H²(ℙ ‖ ℚ)`, obtained from the affinity-product identity (Eq. (15.12a))
and the elementary inequality `1 − (1 − x)ⁿ ≤ n x`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.12b). -/
theorem sqHellinger_pi_le_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      ≤ n • sqHellinger μ ν := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  rw [sqHellinger_pi_eq_ofReal_product_integral, sqHellinger_eq_ofReal_integral,
      ← ENNReal.ofReal_nsmul]
  apply ENNReal.ofReal_le_ofReal
  rw [nsmul_eq_mul]
  exact hellinger_product_residual_sq_le_n_per_sample hμ hν

end StatLean.Minimaxity
