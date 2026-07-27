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
(`StatLean/Bayesian.lean` +25, `StatLean/AsymptoticStatistics.lean` +2). Stub gate GREEN
(round 2, commit 038405e): Build completed successfully (3241 jobs), 79 sorry-uses, 0 errors.
Statements now FROZEN.

## Ledger

| item | wave | touch-set | merge-deps | state | named fallback |
|---|---|---|---|---|---|
| bricks-gauss (MultivariateGaussianDensity) | 1 | AS/ForMathlib/MultivariateGaussianDensity | — | MERGED (1 debt: convolution continuity) | per-lemma sorries |
| bricks-contig (ContiguityIntegralComparison) | 1 | AS/ForMathlib/ContiguityIntegralComparison | — | MERGED 0-sorry | comp_subseq insulated |
| bricks-tv (TVDist, GaussianTV, BvM Basic) | 1 | Bay/ForMathlib/{TVDist,GaussianTV}, Bay/BernsteinVonMises/Basic | — | MERGED 0-sorry (after laptop statement fix) | pair-ratio Jensen insulated |
| tests (ScoreTest, TestBoost, ExponentialTests) | 1 | Bay/BernsteinVonMises/{ScoreTest,TestBoost,ExponentialTests} | — | IN_FLIGHT | mean-expansion insulated |
| doob-core (IIDSeqKernel, PosteriorMartingale, Accessible) | 1 | Bay/ForMathlib/IIDSeqKernel, Bay/DoobConsistency/{Basic,PosteriorMartingale,Accessible,Theorem10_10} | — | **MERGED 0-sorry (incl. Thm 10.10)** | retraction insulated |
| conc (PriorSmallBall, PosteriorConcentration) | 2 | Bay/BernsteinVonMises/{PriorSmallBall,PosteriorConcentration} | bricks-tv | IN_FLIGHT | tail-split insulated |
| local (MixtureContiguity, LocalApproximation) | 2 | Bay/BernsteinVonMises/{MixtureContiguity,LocalApproximation} | bricks-* | IN_FLIGHT | local_tv_tendsto = headline debt |
| bpe-aux (PosteriorTails, ArgminConsistency) | 2 | Bay/BayesEstimators/{PosteriorTails,ArgminConsistency} | tests-statement | STUBBED | — |
| doob-final | — | (absorbed by doob-core; lane not needed) | — | DONE | — |
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
- 2026-07-27: gate round 1 (a306a0d): 2 errors (Defs measurability term proofs; doobJoint
  IsFiniteMeasure instance). Fixed in 038405e (fun_prop; probability instance).
- 2026-07-27: gate round 2 (038405e): GREEN — 3241 jobs, 79 sorries, statements FROZEN.
- 2026-07-27: Wave 1 launched: bay/bvm-bricks (srun 2:30), bay/bvm-tests (srun 2:30) via
  fan-out. bay/doob-core queued — concurrent ht/batch12 session holds 2 cluster-claude
  slots (cap 3); half-created doob-core worktree removed; slot watcher armed.
- 2026-07-27: **STATEMENT DEFECT (lane bvm-bricks)** — `one_sub_lintegral_le_lintegral_one_sub`
  (Bayesian/ForMathlib/TVDist.lean) is FALSE as frozen: without measurability `lintegral` is
  only *super*additive (sup over simple minorants), so only `∫(1−Y) + ∫Y ≥ ∫1` is free.
  Counterexample: `Y := indicator B` for a Bernstein set `B` (both `B`, `Bᶜ` inner measure 0)
  gives LHS `= 1`, RHS `= 0`. Lane correctly STOPPED and left a `private` measurable version.
  LAPTOP FIX at merge: add `(hY : Measurable Y)` tagged
  `-- LEAN-ONLY: measurable integrand (lintegral is only superadditive without it)` and close
  from the lane's private lemma. All consumers (Jensen step in
  `tvDist_normalize_le_double_lintegral`, Step B in `LocalApproximation`) have measurable
  integrands ⇒ no scope change.
- 2026-07-27: wave-2/3/4 prompts written (local, conc, bpe-aux, assembly, bpe-approx,
  bpe-final, doob-final) — 11 prompt files total.
- 2026-07-27: **bvm-bricks GATE GREEN** (54e6d12): 3206 jobs, 2 sorries = the sanctioned
  `gaussian_loss_convolution_continuous` + the defective Jensen statement. Diff audit clean
  (touch-set exact, 0 axioms, no other frozen signature touched). MERGED --no-ff (00adc20).
- 2026-07-27: **statement fix applied** (laptop): `one_sub_lintegral_le_lintegral_one_sub`
  now takes `(hY : Measurable Y)` (LEAN-ONLY tag + counterexample recorded in its docstring);
  proved from the lane's argument; internal call site retargeted. TVDist.lean is 0-sorry.
  Remaining batch debt from wave 1: `gaussian_loss_convolution_continuous` only.
- 2026-07-27: **bay/doob-core GATE GREEN, 0 sorries** (5cb3cb1, 2637 jobs). The lane closed its
  whole scope *and* the Theorem10_10 assembly (prompt-sanctioned early extension), so the
  planned `doob-final` lane is unnecessary. Audit: touch-set exact, 0 axioms, no frozen
  signature touched. MERGED (1f62475). **vdV Theorem 10.10 (Doob consistency) is COMPLETE.**
  Notable: `measurable_infinitePi_const_kernel` (cylinder π-system induction) is a clean
  Mathlib upstream candidate (`Kernel.infinitePi`).
- 2026-07-27: wave 2 launched: bay/bvm-local (Step B, 3h srun), bay/bvm-conc (Step A, 2.5h).
  Still to launch: bpe-aux, then wave 3 (assembly, bpe-approx) and wave 4 (bpe-final).

