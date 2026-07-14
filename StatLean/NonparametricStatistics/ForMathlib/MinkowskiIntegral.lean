import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNRpow

/-!
# Generalized Minkowski integral inequality (L² form)

For a jointly measurable `g : α → β → ℝ≥0∞` and σ-finite measures `μ, ν`:
$$ \Bigl(\int \Bigl(\int g(u,x)\,d\mu(u)\Bigr)^2 d\nu(x)\Bigr)^{1/2}
   \;\le\; \int \Bigl(\int g(u,x)^2\,d\nu(x)\Bigr)^{1/2} d\mu(u). $$

"The `L²(ν)`-norm of an integral is at most the integral of the `L²(ν)`-norms" — the
continuous analogue of the triangle inequality, used to push `L²` moduli of continuity through
kernel-weighted integrals in the integrated-bias analysis of kernel estimators.

**Proof formalization notes.** Stated for `ℝ≥0∞`-valued integrands (the applications are
absolute values of real functions, inserted via `ENNReal.ofReal`), so no integrability side
conditions are needed. Proof route: the classical `L²` duality argument — for `S(x) = ∫ g(u,x)
dμ(u)`, bound `∫ S·φ dν` for `φ` in the unit ball of `L²(ν)` by Tonelli–Fubini
(`lintegral_lintegral_swap`) and the Cauchy–Schwarz inequality for `∫⁻`
(`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`), then take `φ = S/‖S‖₂` (or argue via
`ENNReal.rpow` algebra directly). Alternatively search for a Mathlib `eLpNorm`-level Minkowski
integral inequality first — if one exists on the pin, this lemma is a thin wrapper.

**Bibliographic comments.** H. Minkowski, *Geometrie der Zahlen* (Leipzig, 1896); the integral
form is classical, see G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities* (Cambridge,
1934), Theorem 202.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Generalized Minkowski inequality, `L²` form** (for `ℝ≥0∞`-valued integrands):
`‖∫ g(u, ·) dμ(u)‖_{L²(ν)} ≤ ∫ ‖g(u, ·)‖_{L²(ν)} dμ(u)`. -/
theorem lintegral_lintegral_sq_rpow_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    {g : α → β → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability, needed for the Tonelli–Fubini swap; standard
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x, (∫⁻ u, g u x ∂μ) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ u, (∫⁻ x, (g u x) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
  sorry

end StatLean.NonparametricStatistics
