# Compressed sensing — status

Integration branch: `hds/compressed-sensing` (off `main`). **COMPLETE — all 6 units merged, 0-sorry.**
Stub gate green; each unit verified independently (fresh build, 0-sorry touch-set, diff ⊆ touch-set,
signatures vs stub, no hypothesis laundering) before `--no-ff` merge.

## Theorem / unit ledger — ALL REAL (0-sorry)

| Unit | Branch | File(s) | Decls | Status |
|---|---|---|---|---|
| U1 base | `hds/cs-base` | VecNorms(+5), BasisPursuit | 5 bricks + A1 + A2 | ✅ real |
| U2 topk | `hds/cs-topk-r1` | TopK | orderedBlocks + 6 interface | ✅ real |
| U3 chisq | `hds/cs-chisq` | GaussianChiSquared | chiSq1 (α=4) + fixed-β tail (/32) | ✅ real |
| U4 cone | `hds/cs-cone` | ConeTheorem | A3 + **T1** | ✅ real |
| U5 rip | `hds/cs-rip` | RIPRecovery | rip_cone_trivial + **T2** | ✅ real |
| U6 random | `hds/cs-random` | RandomRIP | net/union + **T3** | ✅ real |

Main theorems:
* **T1** `basisPursuit_unique_iff_cone_inter_ker` (ConeTheorem) — Lu §6 `thm:cone`.
* **T2** `basisPursuit_recovers_of_rip` (RIPRecovery) — Lu §7 `thm:rip`.
* **T3** `prob_rip_of_iid_gaussian` (RandomRIP) — Lu §7 `thm:3s-rip`.
Plus the bricks `chiSq1_centered_isSubExponential`, `gaussian_quadratic_form_tail`, `orderedBlocks`
interface, `deviation_mem_cone_of_basisPursuit`, `unique_basisPursuit_of_cone_trivial`, 5 VecNorms lemmas.

## Parallelization outcome (3 concurrent / 2 waves)
Wave 1 (U1/U2/U3) → Wave 2 (U4/U5/U6), staggered launches to dodge the `.git/config.lock` race
(one early cs-topk retry on a fresh branch `cs-topk-r1`). Each Wave-2 unit consumed only merged,
verified Wave-1 output. No hypothesis laundering in any unit (signatures match stubs).

## Book-vs-Lean constants (final, provable)
| Result | Book | Lean (proved) | Note |
|---|---|---|---|
| T2 RIP threshold | `δ_{3s} < 1/3` | `δ < 1/3` | exact / tight (`3δ<1`) |
| χ²₁ sub-exp param | `α = 2` (sharp) | `α = 4` | range `\|λ\|≤1/4`; clean MGF bound |
| fixed-β tail | `2·exp(−nδ²/8)` | `2·exp(−nδ²/32)` | from `α=4` (`2α²=32`) |
| T3 sample size | `n ≥ (96/δ²)s·log(18d/ε)` | `n ≥ (384/δ²)s·log(18d/ε)` | `384 = 4·96`; order `O(s log(d/ε))` unchanged |

All deviations documented in the respective module docstrings (per CLAUDE.md §1).

## Axioms
`#print axioms` on T1/T2/T3 → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); confirmed
by the full-library build (0 sorry in the new modules).
