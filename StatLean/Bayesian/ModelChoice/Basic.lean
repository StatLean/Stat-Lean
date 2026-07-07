import StatLean.Bayesian.ModelChoice.Defs
import StatLean.Bayesian.Dominated.PosteriorDensity

/-!
# Posterior model probabilities and Bayes factors (finite model space)

Bayesian model comparison over a finite family of models: with model prior `ϖ` on a finite index
`M` and per-model marginal data densities `q m` (so the model-indexed experiment is
`Q m = ν.withDensity (q m)`),

* **posterior model probability** (Robert eq. (7.2.2)):
  $$P(M = m \mid x) = \frac{\varpi(m)\,q_m(x)}{\sum_j \varpi(j)\,q_j(x)}
    \qquad \text{predictive-a.e.};$$
* **posterior model odds = prior odds × Bayes factor** (Robert §7.2.2 / Definition 5.2.5).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §7.2.1, eq. (7.2.2), p. 348; §7.2.2 (Bayes factors between
models), p. 350; Definition 5.2.5 and eq. (5.2.2), p. 227.

**Proof formalization notes.** The model index is a new *parameter space*: `2E.1` is the Batch-1
dominated Bayes theorem applied to `Θ := M` (finite discrete — `StandardBorelSpace` comes from
the pinned countable-discrete instance), with the posterior singleton mass computed by
`withDensity_apply` on `{m}` + `lintegral_singleton`, and the predictive density as the finite sum
`∑ j, ϖ{j}·q j x` (`lintegral_fintype`-style). To *instantiate* `q m` as a genuine marginal
likelihood `predictiveDensity (p m) (π m)`, feed Batch-1's
`comp_eq_withDensity_predictiveDensity` for each within-model experiment. The odds form is
`ℝ≥0∞` division algebra on the ratio of two such formulas.

**Bibliographic comments.** Posterior model probabilities go back to Jeffreys's testing calculus
(*Theory of Probability*, 1939); the model-space formulation (7.2.1)–(7.2.3) with model averaging
became central with A. E. Raftery, D. Madigan and J. A. Hoeting ("Bayesian model averaging for
linear regression models," *J. Amer. Statist. Assoc.* 92 (1997), 179–191) and the review of
J. A. Hoeting et al., *Statist. Sci.* 14 (1999), 382–417. Robert Chapter 7 is the
decision-theoretic account followed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 M : Type*} [m𝓧 : MeasurableSpace 𝓧] [mM : MeasurableSpace M]

/-- **Posterior model probabilities** (Robert eq. (7.2.2)): over a finite model space with
marginal densities `q m`, the posterior probability of model `m` is
`ϖ{m}·q m x / ∑ j, ϖ{j}·q j x`, predictive-a.e. (simultaneously in `m`). -/
theorem posteriorModelProb_eq_div [Fintype M] [MeasurableSingletonClass M] [Nonempty M]
    {Q : Kernel M 𝓧} [IsFiniteKernel Q] {ϖ : Measure M} [IsFiniteMeasure ϖ]
    {ν : Measure 𝓧} [SFinite ν] {q : M → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the marginal densities (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: each model's data law has marginal density q m (feed with Batch-1
    -- comp_eq_withDensity_predictiveDensity: q m := predictiveDensity (p m) (π m));
    -- Robert §7.2.1
    (hQ : ∀ m, Q m = ν.withDensity (q m)) :
    ∀ᵐ x ∂(Q ∘ₘ ϖ), ∀ m,
      posteriorModelProb Q ϖ x m = ϖ {m} * q m x / ∑ j, ϖ {j} * q j x := sorry

/-- **Posterior model odds = prior odds × Bayes factor** (Robert §7.2.2; Definition 5.2.5): for
two models `m₀ m₁` in the finite family, predictive-a.e. -/
theorem posteriorModelProb_div_eq_odds_mul [Fintype M] [MeasurableSingletonClass M] [Nonempty M]
    {Q : Kernel M 𝓧} [IsFiniteKernel Q] {ϖ : Measure M} [IsFiniteMeasure ϖ]
    {ν : Measure 𝓧} [SFinite ν] {q : M → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the marginal densities (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: marginal-density representation of each model; Robert §7.2.1
    (hQ : ∀ m, Q m = ν.withDensity (q m)) (m₀ m₁ : M) :
    ∀ᵐ x ∂(Q ∘ₘ ϖ),
      posteriorModelProb Q ϖ x m₀ / posteriorModelProb Q ϖ x m₁
        = (ϖ {m₀} / ϖ {m₁}) * (q m₀ x / q m₁ x) := sorry

end StatLean.Bayesian
