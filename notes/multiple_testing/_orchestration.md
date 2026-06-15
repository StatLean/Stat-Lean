# MultipleTesting — orchestration ledger (laptop-only)

Mirrors the Optimization-area model: MultipleTesting is developed in a dedicated worktree
`../Stat-Lean-mt` on branch **`mt/area`** (based on `main` @ 8f7c6eb) so the primary working copy
stays free for Batch-1 on `main`. Cluster wrappers run from the worktree with
`LEAN_FASRC_PROJECT=Stat-Lean`. Wave branches base off `mt/area`, merge back into `mt/area`;
`mt/area → main` only at the final area gate.

## Invariants (parallel-with-Batch-1)

* MultipleTesting writes only `StatLean/MultipleTesting/**`, `StatLean/MultipleTesting.lean`,
  `notes/multiple_testing/**`, and the single shared line in `StatLean/StatLean.lean` (laptop-only).
* Branch namespace `mt/*`. Never touch `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`,
  other areas' umbrellas/Defs.
* Laptop-only surfaces in this area: `FDP/Defs.lean`, `PValues/Defs.lean`, `Knockoff/Defs.lean`,
  `MultipleTesting.lean`, `StatLean.lean`, `notes/`. Cluster subagents may edit only their one
  assembly file.

## Ledger

| Wave | Branch | Touch-set | State |
|---|---|---|---|
| 0 scaffold | `mt/area` | all of `StatLean/MultipleTesting/**` + umbrella + `StatLean.lean` + notes | stubs written; stub-gate pending |
| 1 foundations | `mt/foundations` | ForMathlib/OrderStatistics.lean, ForMathlib/OptionalStopping.lean | pending |
| 2 BH | `mt/bh` | BenjaminiHochberg.lean | pending (concurrent) |
| 3 Holm | `mt/holm` | HolmBonferroni.lean | pending (concurrent) |
| 4 knock-off | `mt/knockoff` | Knockoff.lean | pending (concurrent) |
| final | `mt/area`→`main` | umbrella confirm + sync | pending |

## Protocol per wave (CLAUDE.md §10)

frame → stubs (laptop) → stub-gate `lean-fasrc-build --worktree <branch> StatLean.MultipleTesting`
→ proof closure `LEAN_FASRC_CLAUDE_SRUN=1 lean-fasrc-cluster-claude --branch <branch> --prompt-file
.claude/prompts/<topic>.md` → verification gate (laptop: fresh build + sorry inventory +
`git diff` review, six-check audit) → `git merge --no-ff cannon/<branch>` into `mt/area`.

Waves 2–4 launch as **3 concurrent cluster subagents** (user-directed) after Wave 1 merges into
`mt/area`; their touch-sets are file-disjoint so they cannot collide.

## Event log

* (init) Wave 0 scaffold authored on `mt/area`: 8 modules + umbrella + `StatLean.lean` import +
  notes. Expected 12 sorries. Next: commit + stub-gate build.
