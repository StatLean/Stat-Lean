# ComputationalStatistics — Round 1 outline

**Area:** `StatLean/ComputationalStatistics/` — mathematical correctness of sampling
and resampling algorithms. Namespace `StatLean.ComputationalStatistics`.

**Reference:** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9). Tag: `ECS §X.Y`. Relevant chapters: ch. 2 (Monte Carlo
Methods for Inference), ch. 3 (Randomization and Data Partitioning), ch. 4
(Bootstrap Methods).

> Note: the plan file `comp_plan.md` (outside the repo) assumed Gentle's 2009
> *Computational Statistics*; the actual reference text on disk
> (`ref/CompStat/CompStat.djvu`) is the 2002 *Elements*. All citations here use the
> 2002 numbering.

## Scope decisions — what is DELIBERATELY OUT (already formalized elsewhere)

Per the no-duplication rule, the following comp_plan items are **dropped** because
they exist, 0-sorry, in other areas (cross-checked by survey 2026-08-10):

| Dropped topic | Existing home |
|---|---|
| Metropolis–Hastings, detailed balance ⇒ invariance, Gibbs | `StatLean/Bayesian/MCMC/{Defs,MetropolisHastings,Gibbs}.lean` (`mhKernel`, `isReversible_mhKernel`, `invariant_mhKernel`, `invariant_twoBlockGibbs`, …) |
| MCMC ergodicity / rates | `StatLean/TimeSeries/ForMathlib/Markov/{Chain,GeometricErgodicity,HarrisTheorem}.lean` |
| Permutation / randomization tests, super-uniform p-values | `StatLean/HypothesisTesting/Randomization/` (`randTest_exact_level`, `superUniform_randPValue`) + `StatLean/CausalInference/Randomized/Fisher.lean` (`prob_fisherPValue_le`) |
| Subsampling (SRS without replacement, FPC variance) | `StatLean/ExperimentalDesign/SurveySampling/SimpleRandomSampling.lean` (`srs_sampleMean_unbiased`, `srs_sampleMean_variance`) |
| Bootstrap **consistency/asymptotics** (root CDFs, quantiles, coverage, Edgeworth) | `StatLean/HypothesisTesting/Bootstrap/` (`tendsto_supCDFDist_bootstrap`, `bootstrap_mean_consistent`, …) |
| Inverse-CDF sampling (probability integral transform) | `StatLean/HypothesisTesting/ForMathlib/QuantileFunction.lean` (`(volume.restrict (Icc 0 1)).map (quantile F) = P`) |
| QMC | deferred entirely (needs Hardy–Krause variation; Round ≥ 2 flagship) |

Cross-area imports used (all legally `ForMathlib`-layer): `StatLean.Bayesian.ForMathlib.MultinomialDist`
(`multinomialWeight`, `multinomialKernel`).

## Modules and headline results (statement-first stubs; `sorry` = planned debt)

```
StatLean/ComputationalStatistics/
├── ForMathlib/
│   ├── PiMoments.lean       — E/Var/MSE of coordinate averages over Measure.pi
│   │                          (fills a repo-wide gap: E[X̄]=μ, Var(X̄)=σ²/n were
│   │                          inlined ~8× across areas, never packaged)
│   └── PiMarginal.lean      — Measure.pi marginalization along Fin.succAbove
├── Core/
│   ├── Defs.lean            — empiricalMeasure, weightedMeasure, categorical,
│   │                          mcEstimate (laptop-only, 0-sorry)
│   └── EmpiricalMeasure.lean — integral/apply identities, probability instances
├── MonteCarlo/
│   ├── Estimation.lean      — MC estimator unbiased, Var=σ²/n, MSE, SLLN (ECS §2.2)
│   ├── ImportanceSampling.lean — RN identity, IS estimator moments, optimal
│   │                          importance density (Jensen/CS bound) (ECS §2.6)
│   └── RejectionSampling.lean — acceptance prob = 1/c, accepted law = target (ECS §2.1, Alg. 2.1)
├── Resampling/
│   ├── CategoricalCounts.lean — counts of iid categorical draws = multinomialKernel
│   ├── MultinomialMoments.lean — E/Var/Cov of category counts
│   ├── ParticleResampling.lean — SMC multinomial resampling unbiasedness
│   ├── BootstrapMoments.lean — E*[X̄*]=x̄, Var*(X̄*)=σ̂²/n, squared-mean bias
│   │                          correction, Efron counts ~ Multinomial(n;1/n) (ECS §4.1–4.2)
│   ├── Jackknife.lean       — pseudovalues, J(T)=rT−(r−1)T(•), sample-mean case,
│   │                          jackknife variance = s²/n (ECS §3.3, eqs (3.5)–(3.10))
│   └── JackknifeBias.lean   — two-term bias expansion ⇒ Bias(J(T)) = −a₂/(n(n−1)) (ECS §3.3)
└── Partitioning/
    ├── Holdout.lean         — holdout loss conditionally unbiased for prediction risk (ECS §3.2)
    └── KFold.lean           — K-fold CV estimator; E[CV_K] = E[risk of reduced-size rule]; LOO (ECS §3.2)
```

## Design conventions (frozen at stub time)

- **Sample representation:** canonical product space `Measure.pi (fun _ : Fin n => P)`
  (the StatisticalLearning `sampleLaw` pattern), not abstract-Ω random variables.
  Consistency uses `Measure.infinitePi`.
- **Weights are real** (`w : Fin n → ℝ` + nonnegativity/sum-to-one hypotheses),
  matching `StatLean.Bayesian.multinomialWeight`'s simplex conventions; measures are
  built with `ENNReal.ofReal` (NPMLE idiom).
- **Deletion indexing:** jackknife/LOO delete coordinate `i` of `Fin (n+1)` via
  `Fin.succAbove` (no `n − 1` arithmetic).
- **Rejection sampling accept region** uses the multiplicative form
  `ofReal u * (c * q y) ≤ p y` (junk-free at `q y = 0`; agrees with the book's
  `u ≤ p/(cq)` up to a Q-null set — documented in the file).
- `empiricalMeasure`/`mcEstimate` deliberately coexist with the vdV
  (`AsymptoticStatistics.EmpiricalProcess`), bootstrap (`StatLean.HypothesisTesting`)
  and SSBD (`empRisk`) copies — per-area-reference convention; docstrings
  cross-reference. Promotion to a shared home is deferred.

## Lane plan (cluster fan-out; pairwise disjoint touch-sets)

| Lane | Branch | Files |
|---|---|---|
| A | `comp/r1-core` | ForMathlib/PiMoments, Core/EmpiricalMeasure, MonteCarlo/Estimation |
| B | `comp/r1-measure` | MonteCarlo/ImportanceSampling, MonteCarlo/RejectionSampling |
| C | `comp/r1-resampling` | ForMathlib/PiMarginal, Resampling/{CategoricalCounts,MultinomialMoments,ParticleResampling,BootstrapMoments} |
| D | `comp/r1-partitioning` | Resampling/{Jackknife,JackknifeBias}, Partitioning/{Holdout,KFold} |

Max 3 concurrent (subscription limit); D launches as the first lane frees.
Laptop-only: `Core/Defs.lean`, umbrella, `StatLean.lean`, `notes/`.
