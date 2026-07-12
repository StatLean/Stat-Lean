import StatLean.Bayesian.DirichletLaplace.NormalMeansModel

/-!
# Converting a test into a posterior-mass bound (the testing lemma)

The Ghosal–Ghosh–van der Vaart step that turns a good frequentist test `A` (a "reject `θ ∈ C`"
region) into a bound on the truth-averaged posterior mass of `C`. Starting from the posterior ↔
ratio bridge (`NormalMeansModel.lintegral_posterior_eq_lintegral_ratio`), the truth-average of the
ratio `dlNumer θ₀ Π C / dlDenom θ₀ Π` is bounded in three moves:

1. `lintegral_ratio_split` — cut at the denominator event `{dlDenom < dbar}`. On the bad event the ratio
   is `≤ 1` (`dlRatio_le_one_ae`), contributing at most `P₀{dlDenom < dbar}` (this is discharged
   separately by the denominator lower bound, `C7`).
2. `lintegral_ratio_on_event_le_test` — the change-of-measure core: for a test `A` with uniform
   Type-II error `K θ Aᶜ ≤ b` on `θ ∈ C`, Fubini (`lintegral_dlNumer_eq_prior`-style) gives
   `∫_{Aᶜ} dlNumer θ₀ Π C dP₀ = ∫_C K θ Aᶜ dΠ ≤ Π C · b`.
3. `lintegral_ratio_on_event_le_test'` — assemble: on `{dlDenom ≥ dbar}` bound `ratio ≤ 1` on `A` and
   `ratio ≤ dlNumer/dbar` on `Aᶜ`, giving `≤ P₀ A + Π C · b / dbar`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). §6 (the
testing/denominator decomposition). Underlying framework: Ghosal–Ghosh–van der Vaart, *Ann.
Statist.* 28 (2000), 500–531 (the test-based posterior-contraction lemma).

**Proof formalization notes.** `lintegral_ratio_split` splits the `lintegral` over the measurable
event `{y | dlDenom θ₀ Π y < dbar}` and bounds the restricted ratio by the measure of the event via
`dlRatio_le_one_ae`. `lintegral_ratio_on_event_le_test` is the pure change-of-measure step: it
rewrites `∫_{Aᶜ} dlNumer θ₀ Π C dP₀` by Tonelli into `∫_C (∫_{Aᶜ} dlLR dP₀) dΠ`, identifies the inner
integral as `K θ Aᶜ` (via `gaussShiftKernel_eq_withDensity` + `withDensity_apply`), and bounds it by
`b`. `lintegral_ratio_on_event_le_test'` combines the two: on `{dlDenom ≥ dbar}`, `dlNumer/dlDenom ≤`
`𝟙_A + (dlNumer/dbar)·𝟙_{Aᶜ}` pointwise (using `dlDenom ≥ dbar` and `ENNReal.div_le_div_left`), integrate,
then pull the constant `dbar⁻¹` out with `lintegral_mul_const`.
*Deviation D4:* the test `A` and its error bound `b` are supplied by the two-parameter midpoint tests
of `GaussianTests` (C8) with `b ≤ e^{−(d−ρ)²/8}`; this file is agnostic to their construction.

**Bibliographic comments.** Splitting off the small-denominator event and controlling the remainder
with a test is the measure-theoretic heart of Bayesian posterior-consistency theory; the "evidence
lower bound" `dbar = e^{−r²}·Π(B_r)` that instantiates `dbar` downstream is the Kullback–Leibler
prior-mass quantity of Ghosal–Ghosh–van der Vaart (2000) and Castillo–van der Vaart (*Ann. Statist.*
40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Denominator-event split.** The truth-averaged posterior ratio is bounded by the mass of the
small-denominator event `{dlDenom < dbar}` (where the ratio is `≤ 1`) plus the ratio integral on the
good event `{dlDenom ≥ dbar}`. -/
theorem lintegral_ratio_split (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) (dbar : ℝ≥0∞) :
    ∫⁻ y, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ (gaussShiftKernel ι θ₀) {y | dlDenom θ₀ π y < dbar}
        + ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
            dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀) := by
  sorry

/-- **Change-of-measure core of the testing lemma** (BPPD §6, via C6 Fubini): for a measurable test
region `A` whose Type-II error `K θ Aᶜ` is uniformly `≤ b` over `θ ∈ C`, the truth-integral of the
un-normalized numerator on the acceptance region `Aᶜ` is at most `Π C · b`. -/
theorem lintegral_ratio_on_event_le_test (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] {C A : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target and test regions measurable (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) {b : ℝ≥0∞}
    -- USER-INPUT: `A` has uniform Type-II error `≤ b` over `C`; the test property, BPPD §6 / C8
    (hb : ∀ θ ∈ C, gaussShiftKernel ι θ Aᶜ ≤ b) :
    ∫⁻ y in Aᶜ, dlNumer θ₀ π C y ∂(gaussShiftKernel ι θ₀) ≤ π C * b := by
  sorry

/-- **Testing lemma, on-event form** (BPPD §6): on the good denominator event `{dlDenom ≥ dbar}` the
truth-averaged posterior ratio of `C` is at most the Type-I error `P₀ A` of the test plus
`Π C · b / dbar`, where `b` bounds the Type-II error of the test over `C`. -/
theorem lintegral_ratio_on_event_le_test' (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [SFinite π] {C A : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target and test regions measurable (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) {dbar : ℝ≥0∞}
    -- USER-INPUT: positive evidence threshold dbar (instantiated as e^{−r²}·Π(B_r) downstream)
    (hdbar : dbar ≠ 0) {b : ℝ≥0∞}
    -- USER-INPUT: `A` has uniform Type-II error `≤ b` over `C`; the test property, BPPD §6 / C8
    (hb : ∀ θ ∈ C, gaussShiftKernel ι θ Aᶜ ≤ b) :
    ∫⁻ y in {y | dbar ≤ dlDenom θ₀ π y},
        dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ (gaussShiftKernel ι θ₀) A + π C * b / dbar := by
  sorry

end StatLean.Bayesian
