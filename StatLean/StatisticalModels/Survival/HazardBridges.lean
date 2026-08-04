import StatLean.StatisticalModels.Survival.CumulativeHazard
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Classical hazard bridges: `Λ = −log S` and the discrete product formula

The two regime-specific bridges between the cumulative-hazard measure and the survival
function (the fully general mixed-case bridge is the product integral — deliberately
deferred, see below):

* **Continuous bridge (S4.1).** For an atomless event-time law, on the region where survival
  is positive, $\Lambda(0, t] = -\log S(t)$, equivalently $S(t) = e^{-\Lambda(0,t]}$ — the
  identity every parametric survival model is built on.
* **Probability integral transform (`map_cdf_of_noAtoms`)** — the reusable brick behind
  Route A: an atomless law pushed through its own CDF is uniform on `(0, 1]`.
* **Discrete bridge (S4.2).** For a law supported (below `t`) on finitely many atoms,
  $S(t) = \prod_{s \le t} (1 - \Delta\Lambda(s))$ — the population product-limit identity
  mirrored by the Kaplan–Meier estimator.

**Deferred (named debt D-S1):** the mixed-case bridge via the product integral
$S(t) = \prodi_{(0,t]} (1 - \Lambda(ds))$ requires genuine product-integration theory
(R. D. Gill and S. Johansen, "A survey of product-integration with a view toward application
in survival analysis," *Ann. Statist.* **18** (1990), 1501–1555) — a future milestone; the
two regime bridges here cover the textbook uses.

**Reference.** ABGK §II.1 (the `Λ = −log S` identity in the continuous case; the discrete
hazard product) (verify §); J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis
of Failure Time Data*, 2nd ed., Wiley, 2002, §1.2 (verify §). PIT: classical.

**Proof formalization notes.** Route A for S4.1: transport the hazard integral through the
CDF (the PIT brick) to the explicit 1-D integral `∫ (1−u)⁻¹ du = −log(1−·)` (FTC on
`[0, F t]`, `F t < 1` from positive survival). Route B fallback: compare the Stieltjes
measures of `−log S` and `Λ` on `Ioc`-generators. The discrete bridge is a sorted induction
over the atoms with the S-B1 atom formula `ΔΛ = ΔF/S(−)` per step. Sub-probability
generalizations are a later pass (D-S5).

**Bibliographic comments.** `S = e^{−Λ}` in the continuous case is classical actuarial
mathematics; its measure-hazard formulation and the warning that it FAILS with atoms
(whence the product integral) is emphasized by Gill–Johansen (1990) and ABGK §II.6.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

/-- **Probability integral transform** (reusable brick): an atomless probability law on ℝ
pushed through its own CDF is uniform on `(0, 1]`. -/
theorem map_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (fun t => ProbabilityTheory.cdf μ t) = volume.restrict (Ioc (0 : ℝ) 1) := by
  sorry

/-- **S4.1, continuous bridge**: for an atomless event-time law, where survival is positive,
`Λ(0, t] = −log S(t)` (ABGK §II.1; Kalbfleisch–Prentice §1.2). -/
theorem cumHazard_Ioc_eq_neg_log (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: continuous (atomless) law — the identity FAILS with atoms; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: inside the support (positive survival); ABGK §II.1
    (ht : survival μ t ≠ 0) :
    (cumHazard μ (Ioc 0 t)).toReal = -Real.log (survivalReal μ t) := by
  sorry

/-- **S4.1', exponential form**: `S(t) = e^{−Λ(0,t]}` under the same hypotheses. -/
theorem survivalReal_eq_exp_neg_cumHazard (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: atomless; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: positive survival; ABGK §II.1
    (ht : survival μ t ≠ 0) :
    survivalReal μ t = Real.exp (-(cumHazard μ (Ioc 0 t)).toReal) := by
  sorry

/-- The cumulative hazard of an atomless law is finite up to any time with positive
survival (the `toReal` in S4.1 is honest). -/
theorem cumHazard_Ioc_lt_top (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ)
    -- USER-INPUT: atomless; ABGK §II.6
    [NoAtoms μ] {t : ℝ}
    -- USER-INPUT: positive survival; ABGK §II.1
    (ht : survival μ t ≠ 0) :
    cumHazard μ (Ioc 0 t) < ⊤ := by
  sorry

/-- **S4.2, discrete bridge**: for an event-time law whose mass below `t` sits on the finite
set `E`, the survival function is the product of one-minus-hazard-jumps —
`S(t) = ∏_{s ∈ E, s ≤ t} (1 − ΔΛ(s))` (ABGK §II.1 discrete case; the population identity
behind Kaplan–Meier). -/
theorem survivalReal_eq_prod_one_sub_jump (μ : Measure ℝ)
    -- USER-INPUT: event-time law; ABGK §II.1
    (hev : IsEventTimeLaw μ) (E : Finset ℝ) {t : ℝ}
    -- USER-INPUT: finitely supported below t — all mass in `Iic t` sits on E; ABGK §II.1
    (hsupp : μ (Iic t \ (E.filter (· ≤ t) : Finset ℝ)) = 0) :
    survivalReal μ t = ∏ s ∈ E.filter (· ≤ t), (1 - (cumHazardJump μ s).toReal) := by
  sorry

end StatLean.StatisticalModels.Survival
