# MultipleTesting area — status

## STATUS: Wave 0 (scaffold) — statement-first stubs written, stub-gate pending.

Branch: `mt/area` (worktree `../Stat-Lean-mt`). Wave branches base off `mt/area`.

| Decl | File | State |
|---|---|---|
| `orderStat`, `orderStat_monotone` | ForMathlib/OrderStatistics | stub (1 sorry) |
| `supermartingale_expected_stoppedValue_antitone` | ForMathlib/OptionalStopping | stub (1 sorry) |
| `supermartingale_integral_stoppedValue_le` | ForMathlib/OptionalStopping | stub (1 sorry) |
| `numRejections`/`numFalseRejections`/`FDP`/`FDR`/`FWER` | FDP/Defs | defs (real) |
| `SuperUniform` | PValues/Defs | def (real) |
| `sgnReal`, `KnockoffScore` | Knockoff/Defs | defs (real) |
| `bhRejects` | BenjaminiHochberg | def (real) |
| `bh_count_eq_leaveOneOut` | BenjaminiHochberg | stub (1 sorry) |
| `bh_claim` | BenjaminiHochberg | stub (1 sorry) |
| `benjamini_hochberg_fdr_le` | BenjaminiHochberg | stub (1 sorry) |
| `holmCount`/`holmRejects`/`bonferroniRejects` | HolmBonferroni | defs (real) |
| `holm_rejects_true_null_imp` | HolmBonferroni | stub (1 sorry) |
| `holm_fwer_le` | HolmBonferroni | stub (1 sorry) |
| `bonferroni_fwer_le` | HolmBonferroni | stub (1 sorry) |
| `Splus`/`Sminus`/`Vplus`/`Vminus`/`FDPhat`/`tStar`/`knockoffRejects` | Knockoff | defs (real) |
| `knockoff_fdp_le` | Knockoff | stub (1 sorry) |
| `knockoff_ratio_stopped_le_one` | Knockoff | stub (1 sorry) |
| `knockoff_fdr_le` | Knockoff | stub (1 sorry) |

## Expected sorry inventory (per file) — for the verification gate

OrderStatistics 1 · OptionalStopping 2 · BenjaminiHochberg 3 · HolmBonferroni 3 · Knockoff 3.
**Total at scaffold: 12.**

Target after all waves: **0** (knockoff full-proof attempt). If the supermartingale core
(`knockoff_ratio_stopped_le_one`) overruns its time-box it remains the single residual named
debt — flag explicitly, do not hide.

## Wave plan

* Wave 1 `mt/foundations`: OrderStatistics + OptionalStopping (+ any FDP/FWER algebra). → 0 sorry there.
* Waves 2–4 **concurrent cluster subagents** off `mt/area` after Wave 1 merges:
  `mt/bh` (BenjaminiHochberg.lean), `mt/holm` (HolmBonferroni.lean), `mt/knockoff` (Knockoff.lean).
  Touch-sets file-disjoint.
* Final gate: merge → full build → `mt/area → main`.
