# MultipleTesting area — roadmap

Plan: `~/.claude/plans/plan-for-formalization-of-serene-parnas.md` (TODO.md Batch 3).
Reference: Lu, *Big Data Analysis* ch. 18 (`chapter18.tex`, BH), ch. 19 (`chapter19.tex`,
knock-off + optimal stopping); Holm–Bonferroni from Holm (1979) — **not in the book**.

## Targets

| Result | Decl | File | Source |
|---|---|---|---|
| Benjamini–Hochberg FDR control | `benjamini_hochberg_fdr_le` | `BenjaminiHochberg.lean` | Lu-BDA §18 `\label{BH}` |
| Holm–Bonferroni FWER control | `holm_fwer_le` | `HolmBonferroni.lean` | Holm (1979) |
| Bonferroni FWER control | `bonferroni_fwer_le` | `HolmBonferroni.lean` | Lu-BDA §17 |
| Knock-off FDR control | `knockoff_fdr_le` | `Knockoff.lean` | Lu-BDA §19 `thm:knockoff` |
| Optimal stopping (bridge) | `supermartingale_integral_stoppedValue_le` | `ForMathlib/OptionalStopping.lean` | Lu-BDA §19 `thm:optstop` |

## Layers (DAG: ForMathlib → concept Defs → assembly)

```
ForMathlib/OrderStatistics.lean   orderStat, orderStat_monotone            (Tuple.sort)
ForMathlib/OptionalStopping.lean  supermartingale_expected_stoppedValue_antitone,
                                  supermartingale_integral_stoppedValue_le (Mathlib bridge)
FDP/Defs.lean        numRejections, numFalseRejections, FDP, FDR, FWER
PValues/Defs.lean    SuperUniform
Knockoff/Defs.lean   sgnReal, KnockoffScore (3 constitutive fields = Def kos cond. 3)
BenjaminiHochberg.lean  bhRejects; bh_count_eq_leaveOneOut; bh_claim; benjamini_hochberg_fdr_le
HolmBonferroni.lean     holmCount/holmRejects/bonferroniRejects; holm_rejects_true_null_imp;
                        holm_fwer_le; bonferroni_fwer_le
Knockoff.lean           Splus/Sminus/Vplus/Vminus/FDPhat/tStar/knockoffRejects;
                        knockoff_fdp_le; knockoff_ratio_stopped_le_one; knockoff_fdr_le
```

## Dependency tree (proof-level)

* BH: `benjamini_hochberg_fdr_le` ← `bh_claim` ← `bh_count_eq_leaveOneOut` (+ tower property,
  `iIndepFun`, `SuperUniform`). No martingales, no PRDS (book BH is the independent case).
* Holm: `holm_fwer_le` ← `holm_rejects_true_null_imp` (+ union bound, `SuperUniform`).
  `bonferroni_fwer_le` is the §17 corollary.
* Knock-off: `knockoff_fdr_le` ← `knockoff_fdp_le` (deterministic) + `knockoff_ratio_stopped_le_one`
  (the hard core) ← `supermartingale_integral_stoppedValue_le` (`thm:optstop` bridge) + the
  conditional-`Ber(½)` sign field (`KnockoffScore.signs_*`).

## Book vs Lean deviations (record in docstrings)

* BH: book states equality `FDR = (N₀/N)α` for exactly-uniform nulls; we prove `≤` under
  `SuperUniform` (honest, charter §1 constants note).
* Holm: sourced to Holm (1979); the book has only Bonferroni (§17).
* Knock-off `t*`/`knockoffRejects`: degenerate "no valid threshold" case rejects nothing
  (FDP = 0); documented in the defs.
