import StatLean.PointEstimation.UMVU.Defs
import StatLean.PointEstimation.Sufficiency.Defs
import StatLean.PointEstimation.Model.Defs
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Rao–Blackwellization: averaging an estimator over the fibers of a sufficient statistic

Given a sufficient statistic `T` with θ-free reconstruction kernel `Q : S ⇝ 𝓧`, any estimator
`δ` can be replaced by its average over the reconstruction fibers,
$$ \eta(t) \;=\; \int \delta(x)\, dQ_t(x), $$
an estimator that reads the data only through `T`. Averaging preserves unbiasedness and can
only decrease the risk, for every loss that is convex in the decision:

* `rbEstimator` — the fiberwise average displayed above;
* `isUnbiased_rbEstimator` — unbiasedness is preserved;
* `risk_rbEstimator_le` — the risk decreases, for every nonnegative convex loss;
* `variance_rbEstimator_le` — the squared-error case.

**Reference.** Classical conditioning (Rao–Blackwell) theorem for sufficient statistics.

**Proof formalization notes.**
* **Plain Jensen, not conditional Jensen.** Because the reconstruction kernel is available as
  data, the inequality is proved *pointwise in `t`* by ordinary Jensen's inequality
  (`ConvexOn.map_integral_le`) applied to the probability measure `Q t`, and only then
  integrated against the law of the statistic. No conditional-expectation machinery, no
  conditional Jensen, and no filtration bookkeeping is involved. This is the main reason the
  area's sufficiency carrier is a kernel rather than a σ-field.
* **Fiber integrability is derived, not assumed.** The hypotheses ask only for integrability
  under the members `P θ`. That `δ` (respectively `ρ θ ∘ δ`, respectively `δ²`) is integrable
  against `Q t` for almost every `t` follows from the reconstruction identity
  `Q ∘ₘ (statLaw P T θ) = P θ` together with the fact that an iterated `∫⁻` is finite only if
  its inner integral is finite almost everywhere. Assuming the fiber conditions instead would
  be hypothesis laundering: they are forced by the setup, not free inputs.
* `rbEstimator` is defined by a Bochner integral, hence returns the junk value `0` on fibers
  where `δ` fails to be integrable. Under the hypotheses of the theorems below this happens
  only on a null set of values of the statistic, so the junk never propagates.
* Risks are `ℝ≥0∞`-valued and losses enter through `ENNReal.ofReal`, matching `Model.Defs`.
  The convex loss is required nonnegative, so that `ENNReal.ofReal` loses no information, and
  continuous, which for a convex function on all of `ℝ` is automatic; the hypothesis is kept
  explicit only to avoid importing the convex-continuity machinery, and may be dropped once
  it is available.
* The finite-risk hypothesis `hρi` is a genuine restriction only in appearance: if the risk of
  `δ` is infinite the inequality is trivially true, so the statement could be strengthened by
  case analysis. It is kept because the Jensen step consumes exactly this integrability.

**Bibliographic comments.** The theorem is due to C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37**
(1945), 81–91) and D. Blackwell ("Conditional expectation and unbiased sequential
estimation," *Ann. Math. Statist.* **18** (1947), 105–110); its extension from squared error
to arbitrary convex losses, via Jensen's inequality, is standard and appears in E. L. Lehmann
and H. Scheffé ("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10**
(1950), 305–340). The formulation in terms of a reconstruction kernel rather than a
conditional expectation follows R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The **Rao–Blackwellized estimator**: the average of `δ` over the reconstruction fiber at
`s`, `η(s) = ∫ δ dQ_s`. Formalizes conditioning an estimator on a sufficient statistic, with
the θ-free reconstruction kernel `Q` supplying the conditional distribution.

Edge behavior: the Bochner integral returns `0` at any `s` where `δ` is not `Q s`-integrable;
under the hypotheses of the theorems in this file, this occurs only on a null set of values of
the statistic. -/
noncomputable def rbEstimator (Q : Kernel S 𝓧) (δ : 𝓧 → ℝ) : S → ℝ :=
  fun s => ∫ x, δ x ∂(Q s)

/-- **Rao–Blackwellization preserves unbiasedness.** Averaging an unbiased estimator over the
fibers of a sufficient statistic yields an unbiased estimator of the same estimand which
depends on the data only through the statistic. -/
theorem isUnbiased_rbEstimator (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ))
    -- USER-INPUT: the estimator is unbiased for the estimand
    (hδu : IsUnbiased P g δ) :
    IsUnbiased P g (fun x => rbEstimator Q δ (T x)) := by
  sorry

/-- **Rao–Blackwellization does not increase the risk**, for any loss that is convex and
nonnegative in the decision argument. -/
theorem risk_rbEstimator_le (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ)) (ρ : Θ → ℝ → ℝ)
    -- USER-INPUT: the loss is convex in the decision argument; the classical hypothesis
    (hconv : ∀ θ, ConvexOn ℝ Set.univ (ρ θ))
    -- LEAN-ONLY: continuity of the loss, automatic for a convex function on all of `ℝ`
    (hcont : ∀ θ, Continuous (ρ θ))
    -- USER-INPUT: the loss is nonnegative, so that `ENNReal.ofReal` loses nothing
    (hnn : ∀ θ y, 0 ≤ ρ θ y)
    -- USER-INPUT: the risk of `δ` is finite (otherwise the inequality is trivial)
    (hρi : ∀ θ, Integrable (fun x => ρ θ (δ x)) (P θ)) (θ : Θ) :
    risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ (T x)) θ ≤
      risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) δ θ := by
  sorry

/-- **Rao–Blackwellization does not increase the variance** — the squared-error case. -/
theorem variance_rbEstimator_le (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; classical sufficiency input
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimator lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) (θ : Θ) :
    variance (fun x => rbEstimator Q δ (T x)) (P θ) ≤ variance δ (P θ) := by
  sorry

end StatLean.PointEstimation
