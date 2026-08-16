# chaining-sup — status

Branch `conc/chaining-sup` off local main `bb84b0b2`. See `outline.md` for
the tree/constants; plan at `~/.claude/plans/i-want-to-fix-eager-snail.md`.

## Stub inventory (54 decls = 53 sorries + 1 def; stub gate GREEN 2912 jobs, 0 errors, 53 sorry-uses)

| file | decls | wave | fallback slot |
|---|---|---|---|
| Chaining/CountableSupLift.lean | 9 | 1 | `toReal_biSup_ofReal` |
| Chaining/SeparableProcess.lean | 8 (1 def + 7 thms) | 1 | `biSup_real_comp_eq_of_forall_mem_closure` |
| Chaining/DudleySup.lean | 12 | 2a | `dudley_inequality_abs_pair_separable` |
| Chaining/GenericChainingSup.lean | 10 | 2a | `generic_chaining_of_admissible_countable_subset` |
| Chaining/DudleyTailSup.lean | 5 | 2b | `dudley_tail_threshold_le` |
| Chaining/DiscreteDudleySup.lean | 7 | 2b | `discrete_dudley_anchored` |
| Chaining/DudleyConsumers.lean (append) | 3 | 2c | `dudleyLIntegral_le_of_cov_le_exp_div` |

## Gates

- [x] Stub gate (cluster): green, 2912 jobs, 0 errors, 53 sorry-uses (2026-08-15)
- [x] Wave 1 closure: lift 9/9 (0d495b9f) ‖ sep 7/7 (b5cc4ac5) — both 0-sorry
      fresh-verified, diffs ⊆ touch-set, statements byte-identical, ZERO fallbacks
- [x] Wave 2a closure: dudley 12/12 (9f8f6d9f) ‖ generic 10/10 (c2fb3000) —
      both 0-sorry fresh-verified, ZERO fallbacks (pair transport + γ₂
      integrability both closed)
- [x] Wave 2b closure: tail 5/5 (96d553f8) ‖ discrete 7/7 (f3967c21) — both
      0-sorry fresh-verified, ZERO fallbacks
- [x] Wave 2c closure: consumers 3/3 (35e598e3) — diff clean
- [x] Full verification gate: consumers fresh build 0-sorry; umbrella imports
      (fc845319); full-library build on branch GREEN — **9198 jobs, 0 errors,
      0 sorries**; axiom audit **54/54 = {propext, Classical.choice,
      Quot.sound}**, 0 sorryAx (srun `lake env lean AxiomAudit.lean`)
- [x] Merged to local main **fa3fbb61** (2026-08-16); merge tree IDENTICAL to
      the gated branch tip fc845319, so the full-lib gate carries over verbatim.
      NOT pushed to origin/statlean (per user decision: local main only)
- [x] lean-fasrc-sync (cannon/main updated), 8 cluster worktrees removed,
      memory written

Ops notes: laptop wrapper processes were killed mid-run repeatedly — every
cluster session survived as an orphan and was harvested per
[[lean-fasrc-fanout-init-failure-modes]] (fetch-from-clone + laptop push).
New skill patch this batch: the worktree-reuse check's `grep -Fxq` SIGPIPE
race under `pipefail` (init-fan-worktree.sh) — killer #4, now fixed.

## Excluded (recorded, not stubbed)

Real Bochner display of the pair form (needs pair Bochner bridges;
marginal value); `IsSeparableProcess.mono_ae`; fused
`of_continuousOn_of_cov` sugar; literal-8.5.2 mean-zero γ₂ wrapper with
`hint`/`hmean` (the strengthened `generic_chaining_separable` subsumes it).

Website: UPDATED (web/chaining-sup merged to local main daea431d,
2026-08-16): the five chaining entries display the *_separable headliners
(discrete/integral/abs Dudley, three-term tail, generic chaining) with
rewritten informal statements + hypothesis maps; new Separable Process
definition page (conc-separable-process) linked from all five; van Handel
reference added; graphs regenerated via cluster `lake exe deps` (5 roots
moved + 1 new; other 445 byte-identical); validator 451/451/451 green;
vite build + playwright page-render check passed. NOT pushed to
origin/statlean — GitHub Pages deploy deferred until the user publishes.

GitHub reconciliation: DONE (merge 26a9cdb9, 2026-08-16) — statlean/main
(10 commits: PR#13 cross-listing, four-area public release 7c751aab,
website revisions + precomputed layout pipeline) merged into local main.
Lean tree byte-identical to pre-merge main (gate carries over); website =
their 651-entry base + the chaining-sup upgrade replayed (652 results,
validator 652/652/652, layout assets regenerated, build+render checked).
Local main now strictly contains GitHub main (658 ahead / 0 behind) — the
eventual origin push is a clean fast-forward.

## Log

- 2026-08-15: plan approved (separable design / full symmetry / local main
  only); worktree created; 54 stubs written; notes seeded.
