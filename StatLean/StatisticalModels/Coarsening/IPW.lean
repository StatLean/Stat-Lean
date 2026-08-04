import StatLean.StatisticalModels.Coarsening.Basic

/-!
# Inverse-probability weighting — the Horvitz–Thompson identity under MAR

**Headline (C3).** Under a MAR mechanism with uniform positivity, the inverse-propensity-
weighted observed outcome has the full-data mean:
$$\mathbb E_{\text{obs}}\Big[\frac{R\,Y}{\pi(X)}\Big] = \mathbb E_Q[Y].$$
This is exactly the identification statement that the semiparametric example
`AsymptoticStatistics.Examples.MARMean` *assumes* of its estimand `marMean_Ψ` ("supplied
separately by the caller") — supplied here at the model level; the agreement lemma with
`marMean_Ψ` lands in `Coarsening.Ignorability` (batch C-B2) after the observed-carrier
transport.

**Reference.** D. G. Horvitz and D. J. Thompson, "A generalization of sampling without
replacement from a finite universe," *J. Amer. Statist. Assoc.* **47** (1952), 663–685
(the inverse-inclusion-probability estimator) (`HT52`); J. M. Robins, A. Rotnitzky, and
L. P. Zhao, "Estimation of regression coefficients when some regressors are not always
observed," *J. Amer. Statist. Assoc.* **89** (1994), 846–866, §2 (IPW under MAR); van der
Vaart, *Asymptotic Statistics*, CUP 1998, §25.5.3, Example 25.43 (`vdV §25.5.3`).

**Proof formalization notes.** Pushforward unfolding (`integral_map` along `missingObserve`
— the integrand composed with the coarsening map depends only on the full datum), then
`MeasureTheory.integral_compProd` over `Q ⊗ₘ ρ'` and the two-point Bool integral: the inner
integral is `π(x)·(y/π(x)) + 0 = y` under positivity. Integrability side conditions come from
`‖R·Y/π(X)‖ ≤ ‖Y‖/δ`.

**Bibliographic comments.** The IPW identity is the measure-theoretic core of
Horvitz–Thompson (1952) survey estimation, imported to missing-data problems by
Robins–Rotnitzky–Zhao (1994); positivity/overlap as an explicit hypothesis is emphasized
throughout the modern causal-inference literature (Rosenbaum–Rubin 1983).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The IPW integrand on the observed carrier: `(x, r, ry) ↦ r · ry / π(x)`. -/
noncomputable def ipwIntegrand (ρ' : Kernel 𝓧 Bool) (o : 𝓧 × Bool × ℝ) : ℝ :=
  ind o.2.1 * o.2.2 / propensity ρ' o.1

/-- The IPW integrand is bounded by the outcome over the overlap constant along the
coarsening map (the integrability workhorse). -/
theorem abs_ipwIntegrand_comp_le (ρ' : Kernel 𝓧 Bool) {δ : ℝ}
    -- USER-INPUT: uniform positivity (overlap), δ > 0; Rosenbaum–Rubin 1983
    (hδ : 0 < δ) (hpos : HasPositivity ρ' δ) (p : 𝓧 × ℝ × Bool) :
    |ipwIntegrand ρ' (missingObserve p)| ≤ |p.2.1| / δ := by
  sorry

/-- **C3, the Horvitz–Thompson identity under MAR** (`HT52`; Robins–Rotnitzky–Zhao 1994 §2;
`vdV §25.5.3` Example 25.43): under a MAR mechanism with uniform positivity, the
inverse-propensity-weighted observed outcome recovers the full-data outcome mean. -/
theorem ipw_identity (Q : Measure (𝓧 × ℝ)) [IsProbabilityMeasure Q]
    (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] {δ : ℝ}
    -- USER-INPUT: uniform positivity (overlap), δ > 0; Rosenbaum–Rubin 1983
    (hδ : 0 < δ) (hpos : HasPositivity ρ' δ)
    -- USER-INPUT: integrable outcome; HT52
    (hY : Integrable (fun p : 𝓧 × ℝ => p.2) Q) :
    ∫ o, ipwIntegrand ρ' o ∂(observedLaw Q (ρ'.comap Prod.fst measurable_fst))
      = ∫ p, p.2 ∂Q := by
  sorry

end StatLean.StatisticalModels.Coarsening
