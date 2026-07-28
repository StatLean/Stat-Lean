
## Run: batch4 (vdV ch. 10 — BvM / Bayes estimators / Doob)

```run
run_id: bayes4-20260727
integration_branch: bay/batch4
stub_branch: bay/batch4
pin: lean4 v4.29.1 / mathlib 5e932f97
launch: LEAN_FASRC_CLAUDE_SRUN=1 LEAN_FASRC_PROJECT=Stat-Lean lean-fasrc-fan-out --prompt "$(cat .claude/prompts/bayes4-<topic>.md)" <branch>
gating: lean-fasrc-build --worktree <branch> <lane targets>; grep exit marker; sorry inventory vs ledger; diff ⊆ touch-set; merge --no-ff into bay/batch4
concurrency_cap: 3  # staggered launches; never exceed 3
waves:
  - w1: [bay/bvm-bricks, bay/bvm-tests, bay/doob-core]
  - w2: [bay/bvm-local, bay/bvm-conc, bay/bpe-aux|bay/doob-final]
  - w3: [bay/bvm-assembly, bay/bpe-approx]
  - w4: [bay/bpe-final]
gate_targets:
  bvm-bricks: [StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity, StatLean.AsymptoticStatistics.ForMathlib.ContiguityIntegralComparison, StatLean.Bayesian.ForMathlib.TVDist, StatLean.Bayesian.ForMathlib.GaussianTV]
  bvm-tests: [StatLean.Bayesian.BernsteinVonMises.ExponentialTests]
  doob-core: [StatLean.Bayesian.ForMathlib.IIDSeqKernel, StatLean.Bayesian.DoobConsistency.PosteriorMartingale, StatLean.Bayesian.DoobConsistency.Accessible]
  bvm-local: [StatLean.Bayesian.BernsteinVonMises.LocalApproximation]
  bvm-conc: [StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration]
  bpe-aux: [StatLean.Bayesian.BayesEstimators.PosteriorTails, StatLean.Bayesian.BayesEstimators.ArgminConsistency]
  doob-final: [StatLean.Bayesian.DoobConsistency.PosteriorConsistency]
  bvm-assembly: [StatLean.Bayesian.BernsteinVonMises.PosteriorNormality, StatLean.Bayesian.BernsteinVonMises.EfficientCentering]
  bpe-approx: [StatLean.Bayesian.BayesEstimators.UniformApproximation]
  bpe-final: [StatLean.Bayesian.BayesEstimators.PointEstimatorLimits]
```

### Progress log (batch4)

- 2026-07-27: Wave 0 stubs (24 files) + umbrellas on bay/batch4; stub gate pending.
