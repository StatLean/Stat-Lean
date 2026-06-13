<!-- ORCHESTRATOR LEDGER — laptop-only, machine-edited every /loop reconcile pass.
     This file, NOT model memory, is the single source of truth across iterations.
     Subagents must never touch it (it is under notes/, a forbidden surface). -->

# Batch-1 closure ledger

```
run_id:           2026-06-12-batch1-closure
concurrency_cap:  4        # raise to 6 after two consecutive first-try gate passes; never exceed 6
max_attempts:     3
total_spawns:     0        # hard-stop if > 50 (≈ 2× item count)
run_budget_usd:   0.0      # hard-stop at 600.0
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
| classical-limits    | ClassicalLimits.lean                                       | —                                     | READY   | A    | conc/classical-limits          | 0       | —       | —                           |
| sg-bounded          | SubGaussian/Bounded.lean                                   | sg-defs                               | READY   | A    | conc/subgaussian-bounded       | 0       | —       | —                           |
| sg-chernoff         | SubGaussian/Chernoff.lean                                  | sg-defs                               | READY   | A    | conc/subgaussian-chernoff      | 0       | —       | —                           |
| sg-tailbounds       | SubGaussian/TailBounds.lean                               | sg-defs                               | READY   | A    | conc/subgaussian-tailbounds    | 0       | —       | —                           |
| sg-hoeffding        | SubGaussian/Hoeffding.lean                                 | sg-defs                               | READY   | A    | conc/subgaussian-hoeffding     | 0       | —       | —                           |
| subexp-defs         | SubExponential/Defs.lean                                   | —                                     | READY   | L    | conc/subexp-defs               | 0       | —       | —                           |
| subexp-tail         | SubExponential/TailBounds.lean                            | subexp-defs                           | BLOCKED | A    | conc/subexp-tailbounds         | 0       | —       | —                           |
| subexp-mean         | SubExponential/SampleMean.lean                            | subexp-tail                           | BLOCKED | A    | conc/subexp-samplemean         | 0       | —       | —                           |
| bernstein-defs      | Bernstein/Defs.lean                                        | subexp-defs                           | BLOCKED | L    | conc/bernstein-defs            | 0       | —       | —                           |
| bernstein-mgf       | Bernstein/MGFBound.lean                                    | bernstein-defs                        | BLOCKED | A    | conc/bernstein-mgfbound        | 0       | —       | —                           |
| bernstein-ineq      | Bernstein/Bernstein.lean                                   | bernstein-mgf                         | BLOCKED | A    | conc/bernstein-ineq            | 0       | —       | —                           |
| max-covnum          | Maximal/CoveringNumbers.lean                              | —                                     | READY   | A    | conc/maximal-coveringnumbers   | 0       | —       | —                           |
| max-finmax          | Maximal/FiniteMaximal.lean                                | sg-tailbounds                         | BLOCKED | A    | conc/maximal-finitemaximal     | 0       | —       | —                           |
| max-covball         | Maximal/CoveringBall.lean                                 | max-covnum                            | BLOCKED | A    | conc/maximal-coveringball      | 0       | —       | card_le_of_isSeparated_ball |
| max-l2              | Maximal/L2Maximal.lean                                    | max-finmax, max-covball               | BLOCKED | A    | conc/maximal-l2maximal         | 0       | —       | —                           |
| mcd-condhoeff       | McDiarmid/CondHoeffding.lean                              | sg-defs                               | READY   | B    | conc/mcdiarmid-condhoeffding   | 0       | —       | condExp_hoeffding_mgf       |
| mcd-doob            | McDiarmid/DoobDecomposition.lean                         | mcd-condhoeff                         | BLOCKED | B    | conc/mcdiarmid-doob            | 0       | —       | —                           |
| mcd-mcdiarmid       | McDiarmid/McDiarmid.lean                                  | mcd-doob                              | BLOCKED | A    | conc/mcdiarmid-mcdiarmid       | 0       | —       | —                           |

## HighDimensionalStatistics (Lu ch5, ch8)

| item                | file (touch-set, under StatLean/HighDimensionalStatistics/) | deps                                  | state   | mode | branch                         | attempt | last_rc | named_debt                       |
|---------------------|-------------------------------------------------------------|---------------------------------------|---------|------|--------------------------------|---------|---------|----------------------------------|
| hd-vecnorms         | ForMathlib/VecNorms.lean                                   | —                                     | READY   | A    | hds/vecnorms                   | 0       | —       | —                                |
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
