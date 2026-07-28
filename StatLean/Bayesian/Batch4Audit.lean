import StatLean.Bayesian.BernsteinVonMises.Theorem10_1
import StatLean.Bayesian.BernsteinVonMises.EfficientCentering
import StatLean.Bayesian.BernsteinVonMises.ExponentialTests
import StatLean.Bayesian.BernsteinVonMises.LocalApproximation
import StatLean.Bayesian.DoobConsistency.Theorem10_10
import StatLean.Bayesian.BayesEstimators.Theorem10_8

/-!
# TEMPORARY axiom-audit scaffold for Bayesian Batch 4 (vdV Chapter 10)

Not part of the library — deleted before merging to `main`. A clean result is exactly
`[propext, Classical.choice, Quot.sound]`; any `sorryAx` means the declaration still rests on
unproved content, directly or transitively. Per-file sorry counts do NOT settle this, which is
why this scaffold exists.
-/

-- ## The four Chapter-10 targets

-- Theorem 10.1 (Bernstein–von Mises) and its expectation form
#print axioms StatLean.Bayesian.bernstein_von_mises
#print axioms StatLean.Bayesian.bernstein_von_mises_lintegral

-- Lemma 10.3 (exponentially powerful tests)
#print axioms StatLean.Bayesian.exponential_tests

-- Theorem 10.8 (Bayes point estimators), all parts
#print axioms StatLean.Bayesian.bpe_tight
#print axioms StatLean.Bayesian.bayes_estimator_asymptotics
#print axioms StatLean.Bayesian.bayes_estimator_weakConverges
#print axioms StatLean.Bayesian.bayes_estimator_asymptotics_bowlShaped
#print axioms StatLean.Bayesian.gaussCriterion_argmin_zero_of_bowlShaped

-- Theorem 10.10 (Doob consistency)
#print axioms StatLean.Bayesian.doob_consistency

-- ## The p. 144 corollary
#print axioms StatLean.Bayesian.bernstein_von_mises_efficient_centering

-- ## Load-bearing intermediate results
#print axioms StatLean.Bayesian.posterior_mass_compl_ball_tendsto
#print axioms StatLean.Bayesian.local_tv_tendsto
#print axioms StatLean.Bayesian.mutuallyContiguous_mixture_base
#print axioms StatLean.Bayesian.posterior_tail_lintegral_tendsto
#print axioms StatLean.Bayesian.posteriorRisk_shifted_majorant
#print axioms StatLean.Bayesian.argmin_tendsto_of_uniform_approx
