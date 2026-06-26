import StatLean.MultipleTesting.ForMathlib.GammaMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The chi-squared distribution and the sum-of-squares law — ForMathlib brick

The chi-squared distribution defined through Mathlib's Gamma, and the identity that a sum of squared
i.i.d. standard Gaussians is chi-squared (Candès, Lecture 2, §2.3):

* `chiSquared k := Gamma(k/2, 1/2)` (`def`; a probability measure for `k ≥ 1`);
* `mgf_chiSquared` — `E[e^{tX}] = ((1/2)/((1/2)−t))^{k/2}` (the χ² MGF `(1−2t)^{−k/2}`), from the
  merged Gamma MGF;
* `integral_id_chiSquared` / `variance_chiSquared` — mean `k`, variance `2k` (from the Gamma
  mean `a/r` and variance `a/r²` at `a=k/2`, `r=1/2`);
* `map_sum_sq_eq_chiSquared` — **`∑ᵢ Zᵢ² ∼ χ²ₙ`** for i.i.d. `Zᵢ ∼ N(0,1)` (the exact law).

The mean/variance feed the chi-squared test's `H₀` moments `E[Tₙ]=n`, `Var[Tₙ]=2n`
(`ChiSquaredTest/Distribution.lean`). Theorem-agnostic.

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory Real

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The **chi-squared distribution** with `k` degrees of freedom, `χ²ₖ := Gamma(k/2, 1/2)`
(Candès L2 §2.3). A probability measure for `k ≥ 1`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ := gammaMeasure ((k : ℝ) / 2) (1 / 2)

/-- `χ²ₖ` is a probability measure for `k ≥ 1`. -/
instance isProbabilityMeasure_chiSquared (k : ℕ) [NeZero k] :
    IsProbabilityMeasure (chiSquared k) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  unfold chiSquared
  exact isProbabilityMeasure_gammaMeasure (by linarith) (by norm_num)

/-- **MGF of `χ²ₖ`**: `E[e^{tX}] = ((1/2)/((1/2)−t))^{k/2}` for `t < 1/2` (`k ≥ 1`) — the
χ² moment generating function `(1−2t)^{−k/2}`. From `mgf_gammaMeasure`. -/
theorem mgf_chiSquared {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, Real.exp (t * x) ∂(chiSquared k) = ((1 / 2) / ((1 / 2) - t)) ^ ((k : ℝ) / 2) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold chiSquared
  exact mgf_gammaMeasure (by linarith) (by norm_num) ht

/-- **Mean of `χ²ₖ`**: `E[X] = k` (`k ≥ 1`). From the Gamma mean `a/r` at `a=k/2`, `r=1/2`. -/
theorem integral_id_chiSquared {k : ℕ} (hk : 0 < k) :
    ∫ x, x ∂(chiSquared k) = (k : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold chiSquared
  rw [integral_id_gammaMeasure (by linarith) (by norm_num)]
  ring

/-- **Variance of `χ²ₖ`**: `E[(X−k)²] = 2k` (`k ≥ 1`). From the Gamma variance `a/r²`. -/
theorem variance_chiSquared {k : ℕ} (hk : 0 < k) :
    ∫ x, (x - (k : ℝ)) ^ 2 ∂(chiSquared k) = 2 * (k : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have hr : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hcenter : ((k : ℝ) / 2) / (1 / 2) = (k : ℝ) := by ring
  have hvar := variance_gammaMeasure ha hr
  rw [hcenter] at hvar
  unfold chiSquared
  rw [hvar]
  ring

/-- **Sum-of-squares law** (Candès L2 §2.3): for i.i.d. `Zᵢ ∼ N(0,1)`, `∑ᵢ Zᵢ² ∼ χ²ₙ`.
The exact distributional identity behind the chi-squared test statistic `Tₙ = ‖Y‖²` under `H₀`. -/
theorem map_sum_sq_eq_chiSquared {n : ℕ} (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin n → Ω → ℝ)
    -- USER-INPUT: each Zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (Z i))
    -- USER-INPUT: each Zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (Z i) μ = gaussianReal 0 1)
    -- USER-INPUT: the Zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun Z μ) :
    Measure.map (fun ω => ∑ i, (Z i ω) ^ 2) μ = chiSquared n := by
  sorry

end StatLean.MultipleTesting
