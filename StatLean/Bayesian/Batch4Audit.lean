import StatLean.Bayesian.BernsteinVonMises.Theorem10_1
import StatLean.Bayesian.BernsteinVonMises.EfficientCentering
import StatLean.Bayesian.BernsteinVonMises.ExponentialTests
import StatLean.Bayesian.DoobConsistency.Theorem10_10
import StatLean.Bayesian.BayesEstimators.PosteriorTails
import StatLean.Bayesian.BayesEstimators.UniformApproximation
import StatLean.Bayesian.BayesEstimators.ArgminConsistency

/-!
# TEMPORARY axiom-audit scaffold for Bayesian Batch 4 (vdV Chapter 10)

Not part of the library — delete before merging to `main`. Prints the axiom dependencies of
the batch's headline declarations; a clean result is exactly
`[propext, Classical.choice, Quot.sound]`. Anything else (in particular `sorryAx`) means the
declaration still rests on unproved content, whether directly or transitively.
-/

-- Theorem 10.1 (Bernstein–von Mises) and its expectation form
#print axioms StatLean.Bayesian.bernstein_von_mises
#print axioms StatLean.Bayesian.bernstein_von_mises_lintegral

-- The efficient-centering corollary (vdV p. 144)
#print axioms StatLean.Bayesian.bernstein_von_mises_efficient_centering

-- Lemma 10.3 (exponentially powerful tests)
#print axioms StatLean.Bayesian.exponential_tests

-- Theorem 10.10 (Doob consistency)
#print axioms StatLean.Bayesian.doob_consistency

-- Supporting headline results for Theorem 10.8
#print axioms StatLean.Bayesian.posterior_tail_lintegral_tendsto
#print axioms StatLean.Bayesian.posteriorRisk_shifted_majorant
#print axioms StatLean.Bayesian.argmin_tendsto_of_uniform_approx

-- Step A / Step B of Theorem 10.1
#print axioms StatLean.Bayesian.posterior_mass_compl_ball_tendsto
#print axioms StatLean.Bayesian.mutuallyContiguous_mixture_base
