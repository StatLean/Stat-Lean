<!-- ORCHESTRATOR LEDGER — laptop-only, machine-edited every /loop reconcile pass.
     This file, NOT model memory, is the single source of truth across iterations.
     Subagents must never touch it (it is under notes/, a forbidden surface). -->

# Batch-1 closure ledger

```
run_id:           2026-06-12-batch1-closure
concurrency_cap:  4        # raise to 6 after two consecutive first-try gate passes; never exceed 6
max_attempts:     3
total_spawns:     4        # cluster-claude proof sessions launched; hard-stop if > 50
run_budget_usd:   0.0      # hard-stop at 600.0  (update from each session's reported cost)
cap_routine_usd:  12
cap_hard_usd:     25
```

`state ∈ {BLOCKED, READY, STUBBED, IN_FLIGHT, GATING, MERGED, GATE_FAILED, ESCALATED, ACCEPTED_DEBT}`.
`mode`: A = cluster-claude via run_in_background; B = fan-out (long/hard, resilient); L = laptop-authored (Defs/structure, no proof session).
Target prefix: `StatLean.ConcentrationInequalities.*` (CI) / `StatLean.HighDimensionalStatistics.*` (HD).

## ConcentrationInequalities (Lu ch2–4)

| item                | file (touch-set, under StatLean/ConcentrationInequalities/) | deps                                  | state   | mode | branch                         | attempt | last_rc | named_debt                  |
|---------------------|------------------------------------------------------------|---------------------------------------|---------|------|--------------------------------|---------|---------|-----------------------------|
| sg-defs             | SubGaussian/Defs.lean                                      | —                                     | MERGED  | L    | (merged)                       | 0       | 0       | —                           |
| classical-limits    | ClassicalLimits.lean                                       | —                                     | MERGED  | A    | conc/classical-limits (merged) | 2       | 0       | LLN(in prob)+CLT wrappers gated green 2888 jobs 0 sorry; umbrella wired |
| sg-bounded          | SubGaussian/Bounded.lean                                   | sg-defs                               | MERGED  | L    | (merged)                       | 1       | 0       | — (first-try pass #1)       |
| sg-chernoff         | SubGaussian/Chernoff.lean                                  | sg-defs                               | MERGED  | A    | (merged)                       | 2       | 0       | — (gated green 0 sorry)     |
| sg-tailbounds       | SubGaussian/TailBounds.lean                               | sg-defs                               | MERGED  | A    | (merged)                       | 1       | 0       | — (gated green, 0 sorry)    |
| sg-hoeffding        | SubGaussian/Hoeffding.lean                                 | sg-defs                               | MERGED  | A    | (merged)                       | 1       | 0       | laptop-fixed stray ring (§7.10); gated green 2850 jobs |
| subexp-defs         | SubExponential/Defs.lean                                   | —                                     | MERGED  | L    | (on main)                      | 0       | 0       | — (gated green 0 sorry)     |
| subexp-tail         | SubExponential/TailBounds.lean                            | subexp-defs                           | MERGED  | A    | conc/subexp-tail-r1 (merged) | 3 | 0 | two-regime tail gated green 2850 jobs 0 sorry (fixed 6 errs) |
| subexp-mean         | SubExponential/SampleMean.lean                            | subexp-tail                           | MERGED  | A    | conc/subexp-mean-r1 (merged+wired) | 1 | 0 | two-regime sample-mean conc gated green 2850 jobs 0 sorry (session committed just before session-limit cutoff) |
| bernstein-defs      | Bernstein/Defs.lean                                        | —                                     | MERGED  | L    | (on main)                      | 0       | 0       | — (gated green 0 sorry)     |
| bernstein-mgf       | Bernstein/MGFBound.lean                                    | bernstein-defs                        | MERGED-PARTIAL | A | conc/bernstein-mgf-r2 (merged,UNWIRED) | 3 | 1 | main thm PROVEN; bernstein_key OPEN SORRY. ESCALATION RESOLVED: bernstein_key was FALSE bc Defs.moment_le used Bochner ∫ (junk-0 heavy tails) — LAPTOP FIXED Defs to ∫⁻ + added Measurable X hyp. MGFBound now stale vs new Defs (unwired, no build break). Re-closer (3rd) queued w/ updated prompt (lintegral_tsum path). Constant 2(√σ2∨b). |
| bernstein-ineq      | Bernstein/Bernstein.lean                                   | bernstein-mgf                         | BLOCKED | A    | conc/bernstein-ineq            | 0       | —       | —                           |
| max-covnum          | Maximal/CoveringNumbers.lean                              | —                                     | MERGED  | A    | conc/max-covnum-r1 (merged)    | 2       | 0       | reused Mathlib Metric.coveringNumber; gated green 1653 jobs 0 sorry |
| max-finmax          | Maximal/FiniteMaximal.lean                                | sg-tailbounds                         | MERGED  | A    | conc/finmax-expectation (merged+wired) | 4 | 0 | tail_max_le + expectation_max_le BOTH proven 0-sorry (gated 2854 jobs); wired into umbrella. Unblocks max-l2. |
| max-covball         | Maximal/CoveringBall.lean                                 | max-covnum                            | MERGED  | A    | conc/max-covball-r1 (merged) | 1 | 0 | (1+2/ε)^d proven incl card_le_of_isSeparated_ball — HARD LEMMA #2 CLOSED. gated green 2426 jobs |
| max-l2              | Maximal/L2Maximal.lean                                    | max-finmax, max-covball               | MERGED  | A    | conc/l2-tail-r2 (merged+wired) | 2 | 0 | thm:l2 E‖X‖≤4σ√d + high-prob bound BOTH proven 0-sorry (l2_max_tail closed); wired. Maximal chapter COMPLETE. |
| mcd-condhoeff       | McDiarmid/CondHoeffding.lean                              | sg-defs                               | MERGED  | B    | (merged)                       | 1       | 0       | condExp_hoeffding_mgf PROVEN 0-sorry (audited: not laundered, derives HasCondSubgaussianMGF via condExpKernel). HARD LEMMA #1 CLOSED. |
| mcd-doob            | McDiarmid/DoobDecomposition.lean                         | mcd-condhoeff                         | MERGED-PARTIAL | B | conc/mcd-doob-r2 (merged,UNWIRED) | 2 | 1 | Doob martingale+telescope+mgf_sub_expectation_le PROVEN; increment_hasCondSubgaussianMGF CLOSED via condExp_hoeffding_mgf. REMAINING sorry: increment_bounded_of_bounded_differences (line 193) — needs 'iIndepFun ⇒ condDistrib(Xₖ|Fₖ₋₁)=μ.map Xₖ', possible Mathlib gap, ESCALATE-candidate. |
| mcd-mcdiarmid       | McDiarmid/McDiarmid.lean                                  | mcd-doob                              | MERGED  | A    | conc/mcd-mcdiarmid-r1 (merged,UNWIRED) | 1 | 0(new) | McDiarmid bounded-diff inequality PROVEN 0-NEW-sorry (Chernoff on Doob MGF); UNWIRED pending increment_bounded. |

## HighDimensionalStatistics (Lu ch5, ch8)

| item                | file (touch-set, under StatLean/HighDimensionalStatistics/) | deps                                  | state   | mode | branch                         | attempt | last_rc | named_debt                       |
|---------------------|-------------------------------------------------------------|---------------------------------------|---------|------|--------------------------------|---------|---------|----------------------------------|
| hd-vecnorms         | ForMathlib/VecNorms.lean                                   | —                                     | MERGED  | A    | hds/vecnorms-r2 (merged+wired) | 3       | 0       | full ℓ¹/ℓ∞ API gated green 2318 jobs; HDS umbrella CREATED + wired into StatLean.lean. API: l1Norm, linfNorm, Hölder, restrict, √s bound (l1Norm_restrict_le_sqrt_card_mul_norm). |
| hd-linmodel-defs    | LinearModel/Defs.lean                                      | hd-vecnorms                           | MERGED  | L    | (on main, wired) | 1 | 0 | designMap/mse/IsOLSEstimator/columnSpace/designRank via toEuclideanLin; gated green 0 sorry |
| hd-ols-exp          | OLS/MSEExpectation.lean                                    | hd-linmodel-defs, sg-hoeffding        | BLOCKED | A    | hds/ols-mseexpectation         | 0       | —       | —                                |
| hd-ols-hp           | OLS/MSEHighProb.lean                                       | hd-ols-exp, max-l2                    | BLOCKED | A    | hds/ols-msehighprob            | 0       | —       | subGaussian_coords_of_orthonormal |
| hd-lasso-defs       | Lasso/Defs.lean                                            | hd-vecnorms                           | MERGED  | L    | (on main, wired) | 1 | 0 | reCone/RestrictedEigenvalue/lassoObjective/IsLassoEstimator; gated green 2324 jobs 0 sorry |
| hd-lasso-det        | Lasso/DeterministicRate.lean                              | hd-lasso-defs                         | MERGED  | A    | hds/lasso-det-r1 (merged+wired) | 1 | 0 | thm:re ‖β̂−β*‖≤3√s·λ/κ PROVEN gated green 2338 jobs 0 sorry |
| hd-lasso-rand       | Lasso/RandomNoise.lean                                    | hd-lasso-det, sg-hoeffding, sg-tailbounds | MERGED | A | hds/lasso-rand-r2 (merged+wired) | 3 | 0 | cor:lasso-rate O_P(√(s log d/n)) PROVEN gated green 2861 jobs 0 sorry. Lasso chapter COMPLETE. |

## Closure = all items MERGED/ACCEPTED_DEBT AND fresh full `lean-fasrc-build` on main rc==0 AND sorry count == exactly these 3 named debts:
- `condExp_hoeffding_mgf` (mcd-condhoeff)
- `card_le_of_isSeparated_ball` (max-covball)
- `subGaussian_coords_of_orthonormal` (hd-ols-hp)

## Event log (append each pass)
- 2026-06-12: ledger seeded (~25 items). Frontier: classical-limits, sg-bounded, sg-chernoff, sg-tailbounds, sg-hoeffding, max-covnum, hd-vecnorms, subexp-defs(L), mcd-condhoeff(B). Validating pipeline on sg-bounded solo first.
- 2026-06-12 (overnight autonomous reconcile): user set bar=ZERO-sorry (close all 3 named debts), end=merge-to-fork-main (hold upstream PR), drive=autonomous loop to closure.
  RECONCILE FINDING: ledger's "IN_FLIGHT (4)" was overstated. After `git fetch cannon --prune`, branches classical-limits / subgaussian-chernoff / subgaussian-hoeffding have ZERO diff vs main (empty placeholder worktrees @2233e85, no tmux session alive) → relaunched from scratch. Only conc/subgaussian-tailbounds (@9546a89) has real work: TailBounds.lean +138, no sorry in bodies → gate build launched.
  LAUNCHED (background, SRUN=1, --max-usd 25): gate-build tailbounds; cluster-claude sg-chernoff, sg-hoeffding, classical-limits. Concurrency 3/4 claude sessions.
  GIT-LOCK LESSON: concurrent cluster-claude launches collide on shared .git/config.lock during worktree setup. FIX: launch ONE at a time; confirm prev past setup (job allocated) before next. chernoff lost the first race → rm worktree + relaunched solo (OK).
  PROGRESS pass 2: sg-tailbounds MERGED (gated 2850 jobs, 0 sorry, umbrella wired). subexp-defs (L) authored on main + gated green (0 sorry). bernstein-defs (L) authored + gating. Live cluster: 4 claude sessions [sg-chernoff, sg-hoeffding, classical-limits, hds/vecnorms]. Authored prompts for subexp-tail, max-covnum, max-finmax, mcd-condhoeff (ready to launch when slots free). Integration branch = main (also fast-fwd'd the opt proxObj build-fix onto main).
  PROGRESS pass 3: bernstein-defs MERGED (0 sorry). sg-chernoff MERGED (Markov+Chernoff, gated 0 sorry, umbrella wired). MERGED total = 6 [sg-defs, sg-bounded, sg-tailbounds, sg-chernoff, subexp-defs, bernstein-defs].
  PREEMPTION FINDING: shared-partition srun jobs can die rc=143 (SIGTERM) on shutdown. classical-limits + sg-hoeffding both rc143 BUT committed 0-sorry files (classical = deliberate commit 08aea3b; hoeffding = wrapper auto-commit 28d16cb). Treat rc143 as "inspect the branch", NOT auto-fail — gating both now. Mitigation going forward: acceptable, just gate every branch regardless of rc.
  Live cluster pass 3: 4 claude [subexp-tail, hds/vecnorms, max-covnum, max-finmax] + gate script [classical-limits, hoeffding]. Ready-queue: mcd-condhoeff, bernstein-mgf.
  PROGRESS pass 4: sg-hoeffding MERGED (7 total: +sg-hoeffding). hd-vecnorms gate exposed bad import (Analysis.Real.Sqrt → Data.Real.Sqrt; fixed) + 6 real errors (noncomputable linfNorm, Real.inner_apply nonexistent → RCLike.inner_apply §7.2, etc.) → GATE_FAILED, fix prompt hds-vecnorms-fix.md, awaiting slot. classical-limits GATE_FAILED (4 type-mismatch) → relaunched fresh-with-fix-prompt.
  WRAPPER LESSON: `--resume` is UNUSABLE when worktree exists (the wrapper's "ensure worktree" runs `git worktree add` unconditionally → fatal 128). Recovery pattern for any failed branch: `lean-fasrc-worktree-rm <branch>` THEN fresh `lean-fasrc-cluster-claude --branch <branch> --prompt "<fix instructions; the file already exists on the branch, fix its build errors>"`. The branch commit (file) persists through worktree-rm.
  PREEMPTION is frequent on shared partition (rc143) but work is auto-committed before death → always gate, never auto-fail. subexp-tail rc143 but committed both regime theorems 0-sorry → gating.
  Live cluster pass 4: claude [max-covnum, max-finmax, mcd-condhoeff, classical-limits(fix)] + gate [subexp-tail]. Ready-queue: hds/vecnorms(fix), bernstein-mgf. (1 external zombie job ~4h will self-die.)
  PROGRESS pass 5: mcd-condhoeff MERGED — condExp_hoeffding_mgf PROVEN 0-sorry (HARD LEMMA #1 of 3 CLOSED; audited not-laundered, derives HasCondSubgaussianMGF via condExpKernel + hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero). MERGED TOTAL = 8 [+mcd-condhoeff].
  STATUS-CHECK CAPABILITY (user req): added LEAN_FASRC_CLAUDE_EXTRA_FLAGS hook to wrapper; launch with --verbose --output-format stream-json for live JSON events. Plus no-edit probe: fasrc-run worktree `git diff --numstat` + `find -newermt`. This caught 2 hung jobs (max-covnum, max-finmax: 0 progress in 3:45h) → scancel'd. Also user req: DROP --max-usd (done).
  *** BLOCKER pass 5: cluster `claude` CREDENTIAL EXPIRED mid-run → 401 Invalid authentication credentials. Early sessions (auth valid) succeeded; later ones HUNG when auth lapsed (max-covnum, max-finmax, vecnorms-fix all hung 0-progress; fresh max-finmax-v2 got clean 401). CANNOT launch new proof sessions until USER re-authenticates cluster claude. Build/merge pipeline (lake via sbatch) STILL WORKS. Hung jobs scancel'd. ***
  FAILED/NEEDS-RELAUNCH after auth refresh: vecnorms-fix (hds/vecnorms-fix, 20 uncommitted lines lost-hung), max-covnum (no progress), max-finmax (conc/maximal-finitemaximal-v2, 401), classical-limits (salvage commit, broken), subexp-tail (committed but syntax errors). bernstein-mgf, downstream, HDS chain not started.
  RESUME PLAN once auth back: relaunch with new envelope [no --max-usd; MEM=24G; PARTITION=hsph,sapphire,shared; TIME=1:30:00; EXTRA_FLAGS stream-json]; fresh branch names; gate-before-trust.
  INTEGRATION CHECK pass 5: `lean-fasrc-build StatLean.ConcentrationInequalities` (umbrella, all 8 wired modules) = GREEN, 2857 jobs, 0 sorry. The merged CI area compiles together cleanly. (Build pipeline confirmed working despite claude-auth blocker.)
  AUTH RESTORED pass 6: user provided a `claude setup-token` OAuth token (subscription = Max Pro, NOT per-token API). Installed as CLAUDE_CODE_OAUTH_TOKEN in cluster env.Stat-Lean.sh + `unset ANTHROPIC_API_KEY` (force subscription). Verified: `claude -p` returns READY, no 401. stream-json shows sessions doing real tool calls. See [[cluster-claude-launch-conventions]] for refresh procedure.
  WAVE RELAUNCHED pass 6 (full envelope, no --max-usd, 24G, hsph/sapphire/shared, 1:30 walltime, stream-json): conc/max-finmax-r1, conc/max-covnum-r1, conc/bernstein-mgf-r1, hds/vecnorms-r1 — all 4 confirmed authenticating + working via stream. Next queue: subexp-tail(fix), classical-limits(fix), mcd-doob (dep mcd-condhoeff MERGED), subexp-mean, then downstream max-covball/max-l2/bernstein-ineq + HDS linmodel/lasso/ols chain.

## Overnight checkpoint 2026-06-14 ~00:00 ET
21 modules MERGED 0-sorry + both umbrellas green. Lasso/Maximal/SubExp/SubGaussian/classical chapters COMPLETE. 2/3 hard lemmas done (condExp_hoeffding_mgf, card_le_of_isSeparated_ball).
REMAINING (hard tail, fighting heavy preemption + intermittent subscription session-limit; SSH/Duo also expires):
- bernstein_key (Bernstein MGF power-series core) — 9 attempts, reaches ~170 turns then preempted before commit. Attempt 10 on hsph,sapphire + 3h walltime. The 1 sorry blocking Bernstein/MGFBound; also gates bernstein-ineq.
- increment_bounded_of_bounded_differences (McDiarmid Doob) — NOT a Mathlib gap; lemma = ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt. Re-closer (r3) running 135+ turns. Gates mcd-doob full → mcd-mcdiarmid.
- ols-exp (thm:mse-ols expectation, incl subGaussian_coords) — partial, relaunched.
- ols-hp (thm:mse-ols high-prob, needs subGaussian_coords + max-l2[done]) — not started.
- bernstein-ineq, mcd-mcdiarmid — assembly theorems, blocked on the above closers.
LAUNCH ENVELOPE that survives preemption best: PARTITION=hsph,sapphire (drop shared), TIME=2-3h, no --max-usd, MEM=24G, stream-json. rm-worktree+fresh-branch to relaunch. Gate-before-trust always. Per-item prompts in .claude/prompts/. A 4am routine (trig_01T3ZsnHW9nKH9aEhhcu9rDX) reminds user to re-auth + say "continue".

## 2026-06-14 ~00:30 ET — SWITCHED CLUSTER TO OPUS (xhigh effort)
Sonnet WEEKLY quota exhausted (resets Jun 20). Per user, switched cluster claude to Opus: added to cluster env.Stat-Lean.sh `export ANTHROPIC_MODEL=claude-opus-4-8` + `export MAX_THINKING_TOKENS=31999` (max thinking = xhigh effort). Verified: Opus has quota (test READY; sessions show model=claude-opus-4-8, no Sonnet/Opus limit). Relaunched hard tail on Opus/hsph,sapphire/3h: bernstein-key-r11, mcd-increment-r4, ols-exp-r1. Opus quota on Max is tighter than Sonnet — be efficient.

## increment_bounded — CONFIRMED genuine Mathlib gap (Opus, twice)
The Doob-increment RANGE bound needs the DISTRIBUTION-level fact `IndepFun X Y → condDistrib Y X μ =ᵐ μ.map Y` (condExp/mean version condExp_indep_eq is insufficient for a sup−inf range bound). Genuinely absent from Mathlib. Retargeted closer to PROVE it inline via disintegration uniqueness (joint law factorises under indep; condDistrib is the unique disintegrating kernel; const kernel disintegrates the product; conclude by a.e.-uniqueness). Prompt: mcdiarmid-increment-bounded.md. This is the single hardest residual; if it doesn't close it is the documented Batch-1 debt (a real ForMathlib contribution).
