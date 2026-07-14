import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuity of translation in L²(ℝ)

For `f ∈ L²(ℝ)`: `∫ (f(x + t) − f(x))² dx → 0` as `t → 0`.

This is the sole analytic input through which the exact asymptotic mean integrated squared
error of kernel density estimators acquires its `o(1)`: the difference between the bias
integrand and its small-bandwidth limit is controlled by `L²`-moduli of translates of the
(weak) second derivative.

**Proof formalization notes.** Stated with the lower Lebesgue integral (no integrability side
conditions; the hypothesis `MemLp f 2` makes the value finite). Proof route: density of
continuous compactly supported functions in `L²`
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` or the
`ContinuousMap`-density theorems), uniform continuity on compacts for the smooth
approximation, and a `3ε` argument; translation invariance of Lebesgue measure
(`Real.map_volume_add_left` / `lintegral_add_right_eq_self`) equates the translated norms.
An alternative route is via the Fourier–Plancherel isometry if available on the pin.

**Bibliographic comments.** Classical; see e.g. E. M. Stein and G. Weiss, *Introduction to
Fourier Analysis on Euclidean Spaces* (Princeton, 1971), Ch. I.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StatLean.NonparametricStatistics

/-- **Continuity of translation in `L²(ℝ)`**: for square-integrable `f`,
`∫⁻ (f(x+t) − f(x))² dx → 0` as `t → 0`. -/
theorem tendsto_lintegral_sq_sub_translate {f : ℝ → ℝ}
    -- LEAN-ONLY: measurability of `f`; standard regularity
    (hf : Measurable f)
    -- USER-INPUT: square integrability of `f`; classical hypothesis of the translation lemma
    (hf2 : MemLp f 2 volume) :
    Tendsto (fun t : ℝ => ∫⁻ x, ENNReal.ofReal ((f (x + t) - f x) ^ 2))
      (𝓝 0) (𝓝 0) := by
  sorry

end StatLean.NonparametricStatistics
