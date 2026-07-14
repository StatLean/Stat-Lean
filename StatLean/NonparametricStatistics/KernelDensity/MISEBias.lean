import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral
import StatLean.NonparametricStatistics.ForMathlib.TranslationL2
import StatLean.NonparametricStatistics.SmoothnessClasses.NikolskiTaylor

/-!
# Exact asymptotics of the integrated squared bias

For a differentiable density whose derivative is absolutely continuous with square-integrable
a.e. second derivative `w`, and a kernel of order `1` with finite second moment:
$$ \Bigl|\ \int b^2(x)\,dx \;-\; \frac{h^4}{4}\,S_K^2 \int w^2 \ \Bigr| \;\le\; \varepsilon\,h^4
   \qquad (0 < h < h_0(\varepsilon)),\qquad S_K = \int u^2 K(u)\,du. $$
This is the bias half of the exact asymptotic MISE: as `h → 0`, `∫b² ~ (h⁴/4)·S_K²·∫w²`.

**Proof formalization notes.** From the order-`2` integral remainder (with `ℓ = 2` playing the
role of `holderIndex` at `β = 2`),
`b(x) = h²∫u²K(u)∫₀¹(1−τ)·w(x+τuh) dτ du` (a.e. `x`); compare with the constant-`w` surrogate
`h²·(S_K/2)·w(x)` whose squared `L²` norm is exactly `(h⁴/4)S_K²∫w²`. The difference is
controlled by two generalized Minkowski applications and the `L²`-continuity of translation
(`tendsto_lintegral_sq_sub_translate`) applied to `w`, with a split of the `u`-integral at
`|u| ≤ h^{-1/2}` and the envelope `u²|K(u)|` for the far range. This is the analytically
hardest step of the exact MISE; the split thresholds and the `ε`-bookkeeping follow the
classical appendix computation.

The absolute continuity of `p'` is encoded by the explicit a.e.-derivative witness
`w` with `deriv p b − deriv p a = ∫_a^b w` — the honest rendering of "`p'` absolutely
continuous with `p'' = w ∈ L²`".

**Bibliographic comments.** The exact MISE expansion is due to G. S. Watson and
M. R. Leadbetter, *Ann. Math. Statist.* **34** (1963), 480–491; the second-order form with
the `(h⁴/4)S_K²∫(p'')²` bias constant is the classical optimal-bandwidth computation of
M. S. Bartlett, *Sankhyā Ser. A* **25** (1963), 245–254, and V. A. Epanechnikov, *Theory
Probab. Appl.* **14** (1969), 153–158.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Integrated squared bias, exact asymptotics**: under the second-order smoothness
hypotheses, for every `ε > 0` there is `h₀ > 0` such that for all `0 < h < h₀`, `n ≥ 1`:
`ofReal ((h⁴/4)·S_K²·∫w² − ε·h⁴) ≤ ∫ b² ≤ ofReal ((h⁴/4)·S_K²·∫w² + ε·h⁴)`. -/
theorem kde_integrated_sq_bias_asymptotic {p K w : ℝ → ℝ}
    -- USER-INPUT: `p` is a probability density; the sampling model
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    -- USER-INPUT: `p` is differentiable; second-order smoothness input
    (hp1 : Differentiable ℝ p)
    -- USER-INPUT: `p'` is absolutely continuous with a.e. derivative `w`; second-order
    -- smoothness input (the classical `p'' = w`)
    (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    -- USER-INPUT: square-integrable second derivative; second-order smoothness input
    (hw2 : MemLp w 2 volume)
    -- USER-INPUT: kernel of order 1; classical input of the second-order expansion
    (hK : IsKernelOfOrder K 1)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite second moment of the kernel; classical input
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), 1 ≤ n →
        IsIIDSample P X (densityMeasure p) → (∀ i, Measurable (X i)) →
        ∀ h : ℝ, 0 < h → h < h₀ →
          ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε * h ^ 4)
              ≤ (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)) ∧
            (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
              ≤ ENNReal.ofReal
                  (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε * h ^ 4) := by
  sorry

end StatLean.NonparametricStatistics
