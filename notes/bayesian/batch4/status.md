# Batch 4 status — vdV Ch. 10 (BvM + Bayes estimators + Doob)

Integration branch `bay/batch4` off `main` @ 03c39a9. Pin: lean4 v4.29.1, Mathlib 5e932f97.
Reference: vdV *Asymptotic Statistics* (1998) ch. 10. Tag token: `vdV §10.x`.
Source of truth = `lake build` sorry inventory + the files. Plan:
`~/.claude/plans/plan-for-formalizing-batch-optimized-ripple.md`; outline: `outline.md`.

**Provenance rule.** Statements FROZEN after the stub gate; subagents fill sorry bodies +
same-file `private` helpers only. Statement changes are laptop-only, logged here.

**Environment rule.** All builds on FAS-RC (`LEAN_FASRC_PROJECT=Stat-Lean`); subagents get
`LEAN_FASRC_CLAUDE_SRUN=1`; concurrency cap 3, staggered launches; fan-out preferred.

## State

Wave 0 (laptop): stubs written for 24 files (2 AS/ForMathlib, 3 Bay/ForMathlib,
10 BernsteinVonMises, 5 BayesEstimators, 4 DoobConsistency); umbrellas wired
(`StatLean/Bayesian.lean` +23, `StatLean/AsymptoticStatistics.lean` +2). Stub gate pending.

## Ledger

| item | wave | touch-set | merge-deps | state | named fallback |
|---|---|---|---|---|---|
| bricks-gauss (MultivariateGaussianDensity) | 1 | AS/ForMathlib/MultivariateGaussianDensity | — | STUBBED | per-lemma sorries |
| bricks-contig (ContiguityIntegralComparison) | 1 | AS/ForMathlib/ContiguityIntegralComparison | — | STUBBED | comp_subseq insulated |
| bricks-tv (TVDist, GaussianTV) | 1 | Bay/ForMathlib/{TVDist,GaussianTV} | — | STUBBED | pair-ratio Jensen insulated |
| tests (ScoreTest, TestBoost, ExponentialTests) | 1 | Bay/BernsteinVonMises/{ScoreTest,TestBoost,ExponentialTests} | — | STUBBED | mean-expansion insulated |
| doob-core (IIDSeqKernel, PosteriorMartingale, Accessible) | 1 | Bay/ForMathlib/IIDSeqKernel, Bay/DoobConsistency/{PosteriorMartingale,Accessible,Defs-lemmas} | — | STUBBED | retraction insulated |
| conc (PriorSmallBall, PosteriorConcentration) | 2 | Bay/BernsteinVonMises/{PriorSmallBall,PosteriorConcentration} | bricks-tv | STUBBED | tail-split insulated |
| local (MixtureContiguity, LocalApproximation) | 2 | Bay/BernsteinVonMises/{MixtureContiguity,LocalApproximation} | bricks-* | STUBBED | local_tv_tendsto = headline debt |
| bpe-aux (PosteriorTails, ArgminConsistency) | 2 | Bay/BayesEstimators/{PosteriorTails,ArgminConsistency} | tests-statement | STUBBED | — |
| doob-final (Theorem10_10 + Defs-lemmas closure) | 2/3 | Bay/DoobConsistency/Theorem10_10 | doob-core | STUBBED | — |
| assembly (Theorem10_1, EfficientCentering) | 3 | Bay/BernsteinVonMises/{Theorem10_1,EfficientCentering} | conc, local, tests | STUBBED | lintegral form insulated |
| bpe-approx (UniformApproximation) | 3 | Bay/BayesEstimators/UniformApproximation | assembly | STUBBED | — |
| bpe-final (Theorem10_8) | 4 | Bay/BayesEstimators/Theorem10_8 | bpe-approx, bpe-aux | STUBBED | bowl-shaped corollary insulated |

Laptop-only (no lane may touch): `*/Defs.lean` (all four new `Defs.lean` after gate),
`StatLean/Bayesian.lean`, `StatLean/AsymptoticStatistics.lean`, `StatLean.lean`,
`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`. Concurrent-session
warning: `ht/batch12` (other session) — never touch `StatLean/HypothesisTesting/`.

## Wave schedule

W1: `bay/bvm-bricks` (bricks-gauss + bricks-contig + bricks-tv), `bay/bvm-tests` (tests),
`bay/doob-core` (doob-core). W2: `bay/bvm-local` (local; longest, 2–3h), `bay/bvm-conc`
(conc), `bay/bpe-aux` or `bay/doob-final`. W3: `bay/bvm-assembly`, `bay/bpe-approx`,
doob closure. W4: `bay/bpe-final`; full gates; merge to `main`.

## Headline theorems (six-check audit targets)

`bernstein_von_mises` (+ `_lintegral`), `bernstein_von_mises_efficient_centering`,
`exponential_tests`, `bayes_estimator_asymptotics` (+ `_weakConverges`, `_bowlShaped`),
`doob_consistency`.

## Event log (append-only)

- 2026-07-27: Wave 0 — worktree `bay/batch4` created off main 03c39a9; 24 stub files
  written; umbrellas wired; ledger opened. Stub gate: pending.
