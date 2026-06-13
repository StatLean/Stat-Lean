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
| classical-limits    | ClassicalLimits.lean                                       | —                                     | GATE_FAILED | A | conc/classical-limits          | 1       | 1       | NEEDS --resume: 4 type-mismatch errs (lines 68,76,77,113), 0 sorry. Worktree kept. |
| sg-bounded          | SubGaussian/Bounded.lean                                   | sg-defs                               | MERGED  | L    | (merged)                       | 1       | 0       | — (first-try pass #1)       |
| sg-chernoff         | SubGaussian/Chernoff.lean                                  | sg-defs                               | MERGED  | A    | (merged)                       | 2       | 0       | — (gated green 0 sorry)     |
| sg-tailbounds       | SubGaussian/TailBounds.lean                               | sg-defs                               | MERGED  | A    | (merged)                       | 1       | 0       | — (gated green, 0 sorry)    |
| sg-hoeffding        | SubGaussian/Hoeffding.lean                                 | sg-defs                               | MERGED  | A    | (merged)                       | 1       | 0       | laptop-fixed stray ring (§7.10); gated green 2850 jobs |
| subexp-defs         | SubExponential/Defs.lean                                   | —                                     | MERGED  | L    | (on main)                      | 0       | 0       | — (gated green 0 sorry)     |
| subexp-tail         | SubExponential/TailBounds.lean                            | subexp-defs                           | IN_FLIGHT | A  | conc/subexp-tailbounds         | 1       | —       | —                           |
| subexp-mean         | SubExponential/SampleMean.lean                            | subexp-tail                           | BLOCKED | A    | conc/subexp-samplemean         | 0       | —       | —                           |
| bernstein-defs      | Bernstein/Defs.lean                                        | —                                     | MERGED  | L    | (on main)                      | 0       | 0       | — (gated green 0 sorry)     |
| bernstein-mgf       | Bernstein/MGFBound.lean                                    | bernstein-defs                        | BLOCKED | A    | conc/bernstein-mgfbound        | 0       | —       | —                           |
| bernstein-ineq      | Bernstein/Bernstein.lean                                   | bernstein-mgf                         | BLOCKED | A    | conc/bernstein-ineq            | 0       | —       | —                           |
| max-covnum          | Maximal/CoveringNumbers.lean                              | —                                     | IN_FLIGHT | A  | conc/maximal-coveringnumbers   | 1       | —       | —                           |
| max-finmax          | Maximal/FiniteMaximal.lean                                | sg-tailbounds                         | IN_FLIGHT | A  | conc/maximal-finitemaximal     | 1       | —       | —                           |
| max-covball         | Maximal/CoveringBall.lean                                 | max-covnum                            | BLOCKED | A    | conc/maximal-coveringball      | 0       | —       | card_le_of_isSeparated_ball |
| max-l2              | Maximal/L2Maximal.lean                                    | max-finmax, max-covball               | BLOCKED | A    | conc/maximal-l2maximal         | 0       | —       | —                           |
| mcd-condhoeff       | McDiarmid/CondHoeffding.lean                              | sg-defs                               | READY   | B    | conc/mcdiarmid-condhoeffding   | 0       | —       | condExp_hoeffding_mgf       |
| mcd-doob            | McDiarmid/DoobDecomposition.lean                         | mcd-condhoeff                         | BLOCKED | B    | conc/mcdiarmid-doob            | 0       | —       | —                           |
| mcd-mcdiarmid       | McDiarmid/McDiarmid.lean                                  | mcd-doob                              | BLOCKED | A    | conc/mcdiarmid-mcdiarmid       | 0       | —       | —                           |

## HighDimensionalStatistics (Lu ch5, ch8)

| item                | file (touch-set, under StatLean/HighDimensionalStatistics/) | deps                                  | state   | mode | branch                         | attempt | last_rc | named_debt                       |
|---------------------|-------------------------------------------------------------|---------------------------------------|---------|------|--------------------------------|---------|---------|----------------------------------|
| hd-vecnorms         | ForMathlib/VecNorms.lean                                   | —                                     | GATE_FAILED | A | hds/vecnorms                   | 1       | 0       | NEEDS --resume: 6 build errs (noncomputable linfNorm, Real.inner_apply, import). On main but broken+unwired. Fix prompt: hds-vecnorms-fix.md |
| hd-linmodel-defs    | LinearModel/Defs.lean                                      | hd-vecnorms                           | BLOCKED | L    | hds/linearmodel-defs           | 0       | —       | —                                |
| hd-ols-exp          | OLS/MSEExpectation.lean                                    | hd-linmodel-defs, sg-hoeffding        | BLOCKED | A    | hds/ols-mseexpectation         | 0       | —       | —                                |
| hd-ols-hp           | OLS/MSEHighProb.lean                                       | hd-ols-exp, max-l2                    | BLOCKED | A    | hds/ols-msehighprob            | 0       | —       | subGaussian_coords_of_orthonormal |
| hd-lasso-defs       | Lasso/Defs.lean                                            | hd-vecnorms                           | BLOCKED | L    | hds/lasso-defs                 | 0       | —       | —                                |
| hd-lasso-det        | Lasso/DeterministicRate.lean                              | hd-lasso-defs                         | BLOCKED | A    | hds/lasso-deterministicrate    | 0       | —       | —                                |
| hd-lasso-rand       | Lasso/RandomNoise.lean                                    | hd-lasso-det, sg-hoeffding, sg-tailbounds | BLOCKED | A | hds/lasso-randomnoise          | 0       | —       | —                                |

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
