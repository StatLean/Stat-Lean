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
| tests (ScoreTest, TestBoost, ExponentialTests) | 1 | Bay/BernsteinVonMises/{ScoreTest,TestBoost,ExponentialTests} | — | **MERGED** (Lemma 10.3 done; 1 debt: truncScore_mean_expansion) | mean-expansion insulated |
| doob-core (IIDSeqKernel, PosteriorMartingale, Accessible) | 1 | Bay/ForMathlib/IIDSeqKernel, Bay/DoobConsistency/{Basic,PosteriorMartingale,Accessible,Theorem10_10} | — | **MERGED 0-sorry (incl. Thm 10.10)** | retraction insulated |
| conc (PriorSmallBall, PosteriorConcentration) | 2 | Bay/BernsteinVonMises/{PriorSmallBall,PosteriorConcentration} | bricks-tv | **MERGED 0-sorry (Step A done)** | tail-split insulated |
| local (MixtureContiguity, LocalApproximation) | 2 | Bay/BernsteinVonMises/{MixtureContiguity,LocalApproximation} | bricks-* | **MERGED** (MixtureContiguity 0-sorry; 1 debt: local_tv_tendsto) | local_tv_tendsto = headline debt |
| bpe-aux (PosteriorTails, ArgminConsistency) | 2 | Bay/BayesEstimators/{PosteriorTails,ArgminConsistency} | tests-statement | **MERGED 0-sorry** | — |
| doob-final | — | (absorbed by doob-core; lane not needed) | — | DONE | — |
| assembly (Theorem10_1, EfficientCentering) | 3 | Bay/BernsteinVonMises/{Theorem10_1,EfficientCentering} | conc, local, tests | **MERGED 0-sorry (THM 10.1 + corollary)** | — |
| bpe-approx (UniformApproximation) | 3 | Bay/BayesEstimators/UniformApproximation | assembly | **MERGED 0-sorry** | — |
| bpe-final (Theorem10_8) | 4 | Bay/BayesEstimators/Theorem10_8 | bpe-approx, bpe-aux | **MERGED 4/5** | — |
| debt-tight (bpe_tight, repaired stmt) | 5 | Bay/BayesEstimators/Theorem10_8 | defs-repair | **MERGED 0-sorry** | — |
| debt-gauss | 4 | AS/ForMathlib/MultivariateGaussianDensity | — | **MERGED 0-sorry** | — |
| debt-score | 4 | Bay/BernsteinVonMises/ScoreTest | — | **MERGED 0-sorry** | — |
| debt-localtv | 4 | Bay/BernsteinVonMises/LocalApproximation | — | **MERGED 0-sorry** | — |

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
- 2026-07-27: **RATE-LIMIT OUTAGE.** All four running lanes died within minutes of each other
  (`"error":"rate_limit"`; the 401/529 counts in the logs were transient retries). Cause:
  5 concurrent cluster-claude sessions across two user sessions — over the safe cap of 3.
  State salvaged from the auto-close commits:
  * bvm-tests: finished its scope BEFORE the outage → gate green (3180 jobs), ExponentialTests
    and TestBoost 0-sorry, ScoreTest 1 sanctioned debt. **MERGED (8691dac). Lemma 10.3 done.**
  * bvm-local: MixtureContiguity 0-sorry (committed, verified by the earlier partial gate);
    LocalApproximation 4 sorries left. Auto-close commit content unverified.
  * bvm-conc: PriorSmallBall 0-sorry BUT the auto-close commit is **RED** — gate failed with
    `invalid ▸ notation` at PriorSmallBall.lean:409 (the classic unverified-auto-close trap).
  * bpe-aux: died at startup, zero commits.
- 2026-07-27: all three unfinished lanes RELAUNCHED (fresh worktrees; resume notes added to
  the local/conc prompts telling them to build-and-fix the red auto-close content first).
- 2026-07-27: **Step A MERGED** (d38f8fd, gate 3180 jobs): PriorSmallBall + PosteriorConcentration
  both 0-sorry. The relaunched lane also repaired the red `prior_tail_split` left by the
  rate-limit auto-close, confirming the gate-before-trust rule.
- 2026-07-27: **Step B MERGED** (175e84d, gate 3190 jobs): MixtureContiguity 0-sorry (incl. the
  support-free `mutuallyContiguous_local_alternative`, which the repo's pre-existing
  `contiguous_local_alternatives` could NOT supply — it needs a per-n common-support
  hypothesis vdV does not grant); LocalApproximation 3/4 with `local_tv_tendsto` as the single
  sanctioned debt.
- 2026-07-27: wave 3 launched: bay/bvm-assembly (Theorem 10.1 + EfficientCentering, 3h).
  bay/bpe-aux still running (ArgminConsistency 0-sorry on-branch; PosteriorTails in progress).
  Batch sorry inventory at this point: 17 across 9 files (3 sanctioned/known debts, the rest
  are not-yet-started wave-3/4 targets).
- 2026-07-27: **display (10.9) + ArgminConsistency MERGED** (1896345, gate 3183 jobs), both
  0-sorry.
- 2026-07-27: **vdV THEOREM 10.1 (BERNSTEIN-VON MISES) MERGED 0-SORRY** (a7bc5cc, gate 3226
  jobs), together with the p.144 **efficient-centering corollary**. The assembly resolves the
  Step-A (`Mₙ → ∞`) vs Step-B (fixed radius) tension by a diagonal extraction of a slowly
  diverging `Mseq`, then runs the three-way conditioned triangle inequality.
- 2026-07-27: **UniformApproximation MERGED 0-sorry** (e50542e, gate 3204 jobs) — the
  majorant (ℓ^∞(K)-free) form of Thm 10.8 Part 3.
- 2026-07-27: **Batch state: 8 sorries left, ALL with a lane in flight** — Theorem10_8 (5,
  bpe-final), local_tv_tendsto (debt-localtv), truncScore_mean_expansion (debt-score),
  gaussian_loss_convolution_continuous (debt-gauss). Three of the four chapter targets
  (Thm 10.1, Lemma 10.3, Thm 10.10) plus the corollary are COMPLETE.
- 2026-07-27: **AXIOM AUDIT (Tier-0, on batch4 @ 3a0797d)** — `#print axioms` via a temporary
  scaffold. CLEAN (`[propext, Classical.choice, Quot.sound]`): `doob_consistency`,
  `posterior_mass_compl_ball_tendsto` (Step A), `mutuallyContiguous_mixture_base`,
  `posterior_tail_lintegral_tendsto` (10.9), `argmin_tendsto_of_uniform_approx`.
  Still carrying `sorryAx` **transitively**: `bernstein_von_mises`(+`_lintegral`),
  `bernstein_von_mises_efficient_centering`, `exponential_tests`,
  `posteriorRisk_shifted_majorant`.
  Cause: the two open debts live in OTHER files — `local_tv_tendsto` (LocalApproximation)
  feeds Thm 10.1 and everything downstream; `truncScore_mean_expansion` (ScoreTest) feeds
  `exists_moderate_tests` → `exponential_tests` → Thm 10.1.
  **Lesson (already in CLAUDE.md, re-confirmed): a 0-sorry FILE is not an axiom-clean
  THEOREM.** Per-file sorry counts must never be reported as completion; only `#print axioms`
  settles it. Re-run the scaffold after every debt merge.

## STATE: all Chapter-10 targets closed, ZERO SORRIES in the batch (2026-07-27)

- **STATEMENT DEFECT #2 (lane bpe-final).** `SeparatedLoss.strict` as originally frozen —
  "∃ one pair with `ℓ x < ℓ y`" — makes `bpe_tight` **FALSE**. The lane supplied a
  machine-checked witness: the `0-1` loss satisfies the weak form, has zero sup–inf gap at
  every scale, so against an atomless posterior its risk is constant, every point minimises,
  and a selection escaping to infinity breaks tightness. vdV p.147 means the *sup–inf* gap is
  strict (he uses `η := ℓ̲(2δ) − ℓ̄(δ) > 0` on p.148), and his own sufficient condition
  ("`ℓ₀` nondecreasing, not constant on `(0,∞)`") excludes the `0-1` loss.
  **LAPTOP REPAIR:** `strict : ∃ M > 0, ∃ c, (∀ x, ‖x‖ ≤ M → ℓ x ≤ c) ∧ ∀ y, 2M ≤ ‖y‖ → c < ℓ y`
  (explicit separating threshold, equivalent to vdV's sup–inf form, avoids `sSup`/`sInf` in
  `ℝ≥0∞`). All four already-closed Thm 10.8 proofs still compile ⇒ none of them had leaned on
  the weak form. `debt-tight` then closed `bpe_tight` against the repaired definition.
- **OPERATIONAL ERROR (mine).** I ran a `--worktree` gate on `bay/debt-localtv` while its lane
  was still live; the wrapper's worktree-sync can clobber a running session. No damage this
  time (HEAD and the 0-sorry working tree survived), and the "sorry at line 516" it reported
  was just the stale pre-push tip — fan-out lanes push only at session end.
  **RULE: never gate a branch whose lane is still in `squeue`.**
- Merges: debt-gauss (3a0797d), debt-score (32275b7), bpe-final (c3eb561), SeparatedLoss
  repair + helper restore, debt-localtv, debt-tight (6c0f1d6).
- **Batch sorry inventory: 0.** Final verification in flight: full-library build +
  `#print axioms` over all 16 headline/load-bearing declarations.

