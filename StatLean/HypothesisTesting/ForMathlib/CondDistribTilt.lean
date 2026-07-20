import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional distributions under a product-form density tilt

Let `ρ` be a measure on a product `𝓤 × 𝓣` (with `𝓤` standard Borel) and let
$$P = \rho \cdot \bigl(g(u)\,k(t)\bigr)$$
be the measure obtained from `ρ` by a density that **factorises** into a `u`-part and a
`t`-part. The `t`-part reweights only the second marginal, so it cancels from every
conditional law: the conditional distribution of `U` given `T = t` under `P` is the
*normalised `g`-tilt* of the conditional distribution under `ρ`,
$$P(\mathrm du \mid T = t) \;=\; \frac{g(u)\,\rho(\mathrm du \mid T = t)}
    {\int g \, \mathrm d\rho(\cdot \mid T = t)} ,$$
for `P`-almost every value `t` of the conditioning variable.

This is the engine behind **conditional exponential families**: in a multiparameter
exponential family with sufficient statistic `T` and interest statistic `U`, the density
relative to a fixed base measure factorises exactly in this way (the nuisance parameters
enter only through `k`), so the conditional law of `U` given `T = t` depends on the
interest parameter alone. Everything about conditional tests — similar regions, Neyman
structure, the conditional construction of unbiased tests — is downstream of this single
cancellation.

## Main results

* `condTiltNormalizer` — the conditional normalising constant `t ↦ ∫ g dρ(· | T = t)`.
* `measurable_condTiltNormalizer` — its measurability in `t`.
* `condTiltNormalizer_pos_lt_top_ae` — it is strictly positive and finite for almost every
  `t` under the tilted measure.
* `condDistrib_fst_withDensity_tilt` — the tilt identity above, as an almost-everywhere
  equality of the two `condDistrib` kernels.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.4 (UMP Unbiased Tests for Multiparameter Exponential Families),
supporting material for Lemma 4.4.1: conditional distributions under a product-form density
tilt. (`TSH4 §4.4 Lem 4.4.1`.)

**Proof formalization notes.**
* Densities are `ℝ≥0∞`-valued (`g k : 𝓤 → ℝ≥0∞`, `𝓣 → ℝ≥0∞`), matching
  `MeasureTheory.Measure.withDensity` natively and avoiding `ENNReal.ofReal` bookkeeping;
  a real nonnegative density is fed in as `ENNReal.ofReal ∘ p`.
* Mathlib's `condDistrib` is only defined for finite measures, so `ρ` and the tilted
  measure `P` are assumed finite. The σ-finite case reduces to this one by exhausting
  `𝓤 × 𝓣` along an increasing sequence of finite pieces and using a.e.-uniqueness of the
  disintegration; that reduction is *not* formalised here — the finite case is what the
  conditional-test applications use (all measures involved are probability measures).
* Neither the positivity nor the finiteness of the normaliser is a hypothesis: both are
  consequences of `P` being finite and are isolated in
  `condTiltNormalizer_pos_lt_top_ae`. Where the normaliser vanishes or blows up, the
  tilted second marginal puts no mass, so the a.e. statement is unaffected.
* The proof route is `Measure.compProd_map_condDistrib` in both directions: expand `P` as
  `(P.map Prod.snd) ⊗ₘ condDistrib Prod.fst Prod.snd P`, expand the right-hand side the
  same way from `ρ`, and conclude by a.e.-uniqueness of the disintegration
  (`Measure.eq_condKernel_of_measure_eq_compProd`-style), the two composed measures being
  equal by `lintegral_withDensity` on rectangles.
* `P` is a variable constrained by the equation `hP` rather than a literal
  `ρ.withDensity …` in the statement, so that the finiteness instance for `P` can be
  supplied by the caller.

**Bibliographic comments.** Conditional probability given a σ-algebra is due to
A. N. Kolmogorov, *Grundbegriffe der Wahrscheinlichkeitsrechnung*, Springer, 1933;
existence of *regular* conditional distributions on standard Borel spaces is due to
J. L. Doob, *Stochastic Processes*, Wiley, 1953, Ch. I §9, building on V. A. Rokhlin's
theory of Lebesgue spaces ("On the fundamental ideas of measure theory," *Mat. Sbornik*
**25** (1949), 107–150). The statistical use of the cancellation formalised here — the
conditional law of the interest statistic given a sufficient statistic, and the resulting
similar regions — goes back to J. Neyman ("Sur la vérification des hypothèses statistiques
composées," *Bull. Soc. Math. France* **63** (1935), 246–266) and E. L. Lehmann and
H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓤 𝓣 : Type*} [MeasurableSpace 𝓤] [StandardBorelSpace 𝓤] [Nonempty 𝓤]
  [MeasurableSpace 𝓣]

/-- The **conditional normalising constant** of a `u`-density `g` with respect to a measure
`ρ` on `𝓤 × 𝓣`: the mass of `g` under the conditional law of the first coordinate given
that the second coordinate equals `t`,
`C(t) = ∫ g(u) ρ(du | T = t)`.

Values `0` and `∞` are permitted by the definition; both occur only on a null set of `t`
for the tilted measure (`condTiltNormalizer_pos_lt_top_ae`). -/
noncomputable def condTiltNormalizer (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    (g : 𝓤 → ℝ≥0∞) (t : 𝓣) : ℝ≥0∞ :=
  ∫⁻ u, g u ∂(condDistrib Prod.fst Prod.snd ρ t)

/-- The conditional normalising constant is a measurable function of the conditioning
value. Consequence of the joint measurability of a kernel's `lintegral`
(`ProbabilityTheory.Kernel.measurable_lintegral`). -/
lemma measurable_condTiltNormalizer (ρ : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    {g : 𝓤 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g) :
    Measurable (condTiltNormalizer ρ g) := by
  sorry

/-- Under the tilted measure, the conditional normalising constant is strictly positive and
finite almost everywhere in the conditioning variable.

Positivity: on `{C = 0}` the `g`-tilt contributes no mass, so the second marginal of the
tilted measure vanishes there. Finiteness: the total mass of the tilted measure is
`∫ k(t) C(t) dρ_T(t)`, which is finite by assumption, so `k · C < ∞` almost everywhere,
and the tilted second marginal is carried by `{k > 0}`. -/
lemma condTiltNormalizer_pos_lt_top_ae (ρ P : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    [IsFiniteMeasure P] {g : 𝓤 → ℝ≥0∞} {k : 𝓣 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g)
    -- USER-INPUT: the `t`-density is measurable.
    (hk : Measurable k)
    -- USER-INPUT: `P` is the product-form tilt of `ρ`.
    (hP : P = ρ.withDensity fun p => g p.1 * k p.2) :
    ∀ᵐ t ∂(P.map Prod.snd),
      0 < condTiltNormalizer ρ g t ∧ condTiltNormalizer ρ g t < ⊤ := by
  sorry

/-- **Conditional law under a product-form tilt.**

If `P = ρ · (g(u) k(t))`, then for `P`-almost every value `t` of the second coordinate the
conditional law of the first coordinate given the second is the `g`-tilt of the
corresponding conditional law under `ρ`, renormalised:
$$P(\cdot \mid T = t) \;=\; C(t)^{-1}\,\bigl(g \cdot \rho(\cdot \mid T = t)\bigr),
  \qquad C(t) = \int g \,\mathrm d\rho(\cdot \mid T = t).$$

The `t`-factor `k` has disappeared: it changes the marginal law of `T` but not the
conditional law of `U` given `T`. -/
theorem condDistrib_fst_withDensity_tilt (ρ P : Measure (𝓤 × 𝓣)) [IsFiniteMeasure ρ]
    [IsFiniteMeasure P] {g : 𝓤 → ℝ≥0∞} {k : 𝓣 → ℝ≥0∞}
    -- USER-INPUT: the `u`-density is measurable.
    (hg : Measurable g)
    -- USER-INPUT: the `t`-density is measurable.
    (hk : Measurable k)
    -- USER-INPUT: `P` is the product-form tilt of `ρ`.
    (hP : P = ρ.withDensity fun p => g p.1 * k p.2) :
    ∀ᵐ t ∂(P.map Prod.snd),
      condDistrib Prod.fst Prod.snd P t
        = (condTiltNormalizer ρ g t)⁻¹ •
            ((condDistrib Prod.fst Prod.snd ρ t).withDensity g) := by
  sorry

end StatLean.HypothesisTesting
