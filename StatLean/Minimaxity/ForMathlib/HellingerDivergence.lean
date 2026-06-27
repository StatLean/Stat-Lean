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
  sorry

/-- **The squared Hellinger distance lies in `[0, 2]`** (Wainwright Eq. (15.9)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
theorem sqHellinger_le_two (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν ≤ 2 := by
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
  sorry

end StatLean.Minimaxity
