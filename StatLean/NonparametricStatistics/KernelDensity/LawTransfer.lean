import StatLean.NonparametricStatistics.KernelDensity.Defs

/-!
# Law transfer for density-sampled observations

The bridge between sample-space expectations and Lebesgue integrals against the density: for
`X` with law `densityMeasure p`,

* `isProbabilityMeasure_densityMeasure` — a measurable density induces a probability measure;
* `integral_comp_law_densityMeasure` / `lintegral_comp_law_densityMeasure` — the change of
  variables `E_P[g(X)] = ∫ g(z)·p(z) dz` (Bochner and lower-Lebesgue forms);
* `kdeMeanAt_eq_integral_kernel` — the mean of the kernel estimator at `x` in the classical
  form `E[p̂ₙ(x)] = ∫ K(u)·p(x + uh) du`.

These lemmas are the only place where `HasLaw`/`withDensity` plumbing appears; all risk files
consume the clean integral forms.

**Proof formalization notes.** Bochner transfer: `HasLaw.integral_comp` +
`integral_withDensity_eq_integral_toReal_smul` (plus `ENNReal.toReal_ofReal` on the
nonnegative density). Lower-Lebesgue transfer: `HasLaw.lintegral_comp`-style map lemma +
`lintegral_withDensity_eq_lintegral_mul`. The mean formula composes the transfer with the
scaling change of variables `z = x + u·h` (`Measure.integral_comp_mul_left` family and
translation invariance); its integrability hypothesis is discharged by consumers
(`integrable_kernel_mul_holder` in `KernelDensity/Bias.lean` for Hölder densities).

**Bibliographic comments.** Routine measure-theoretic plumbing; no attribution applicable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A measurable probability density induces a probability measure via `withDensity`. -/
theorem isProbabilityMeasure_densityMeasure {p : ℝ → ℝ}
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p)
    -- USER-INPUT: `p` is a probability density (nonnegative, unit mass)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1) :
    IsProbabilityMeasure (densityMeasure p) := by
  sorry

/-- **Law transfer, Bochner form**: for `X` with law `densityMeasure p` and integrable
`g·p`, `E_P[g(X)] = ∫ g(z)·p(z) dz`. -/
theorem integral_comp_law_densityMeasure {X : Ω → ℝ} {p : ℝ → ℝ}
    -- USER-INPUT: `X` has Lebesgue density `p`; the sampling model
    (hX : HasLaw X (densityMeasure p) P)
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    {g : ℝ → ℝ}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hg : Measurable g)
    -- LEAN-ONLY: integrability against the density; discharged by consumers
    (hint : Integrable fun z => g z * p z) :
    ∫ ω, g (X ω) ∂P = ∫ z, g z * p z := by
  sorry

/-- **Law transfer, lower-Lebesgue form**: for `X` with law `densityMeasure p` and measurable
`g : ℝ → ℝ≥0∞`, `∫⁻ g(X) dP = ∫⁻ g(z)·ofReal (p z) dz`. -/
theorem lintegral_comp_law_densityMeasure {X : Ω → ℝ} {p : ℝ → ℝ}
    -- USER-INPUT: `X` has Lebesgue density `p`; the sampling model
    (hX : HasLaw X (densityMeasure p) P)
    -- LEAN-ONLY: measurability of the density; standard regularity
    (hp : Measurable p)
    {g : ℝ → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hg : Measurable g) :
    ∫⁻ ω, g (X ω) ∂P = ∫⁻ z, g z * ENNReal.ofReal (p z) := by
  sorry

/-- **Mean of the kernel estimator** at `x`, in the classical bias-analysis form:
`E_P[p̂ₙ(x)] = ∫ K(u)·p(x + u·h) du` (for a nonempty sample and positive bandwidth). -/
theorem kdeMeanAt_eq_integral_kernel {n : ℕ} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ} {x : ℝ}
    -- LEAN-ONLY: nonempty sample; with `n = 0` the estimator is identically `0`
    (hn : 0 < n)
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability; standard regularity
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hK : Measurable K)
    -- LEAN-ONLY: integrability of the transferred integrand; discharged by consumers via
    -- `integrable_kernel_mul_holder`
    (hint : Integrable fun u => K u * p (x + u * h)) :
    kdeMeanAt P X K h x = ∫ u, K u * p (x + u * h) := by
  sorry

end StatLean.NonparametricStatistics
