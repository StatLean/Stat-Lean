# Compressed sensing — status

Integration branch: `hds/compressed-sensing` (off `main`). Stub commit `ad054f5`.
Stub gate: **GREEN** (`lake build` of the 3 assembly modules + deps, 0 errors, 19 expected sorries).

## Sub-lemma / theorem ledger

| Unit | Branch | File(s) | Decls | Status |
|---|---|---|---|---|
| U1 base | `hds/cs-base` | VecNorms(+5), BasisPursuit | 5 bricks + A1 + A2 | stub |
| U2 topk | `hds/cs-topk` | TopK | orderedBlocks + 6 interface | stub |
| U3 chisq | `hds/cs-chisq` | GaussianChiSquared | chiSq1 sub-exp + fixed-β tail | stub |
| U4 cone | `hds/cs-cone` | ConeTheorem | A3 + T1 | stub |
| U5 rip | `hds/cs-rip` | RIPRecovery | rip_cone_trivial + T2 | stub |
| U6 random | `hds/cs-random` | RandomRIP | net/union + T3 | stub |

Legend: stub = statement-only (`sorry`); real = proved & merged 0-sorry.

## Wave plan
- Wave 1: U1, U2, U3 (concurrent). Wave 2: U4, U5, U6 (concurrent), after Wave-1 merges.
- Per unit: dispatch `lean-fasrc-cluster-claude --branch hds/cs-X --base hds/compressed-sensing
  --prompt-file .claude/prompts/cs-X.md` → verification gate (fresh build, 0-sorry in touch-set,
  diff ⊆ touch-set, tags present) → `git merge --no-ff cannon/hds/cs-X`.

## Book-vs-Lean constants (fill provable values as units land)
| Result | Book | Lean (provable) |
|---|---|---|
| T2 RIP threshold | `δ_{3s} < 1/3` | `δ < 1/3` (exact) |
| χ²₁ sub-exp param | `α = 2` (sharp) | `α = 4` (TBD by U3) |
| fixed-β tail | `2·exp(−nδ²/8)` | `2·exp(−nδ²/C)`, C TBD (U3) |
| T3 sample size | `n ≥ (96/δ²)s·log(18d/ε)` | TBD (U6, matched to C) |

## Next step
Dispatch Wave 1 (U1/U2/U3).
