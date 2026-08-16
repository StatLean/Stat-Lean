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
- [ ] Full verification gate: consumers fresh build; umbrella imports; full-lib
      build on branch; `#print axioms` on all 54 decls
- [ ] Merge to local main + full-lib gate on main
- [ ] lean-fasrc-sync, worktree cleanup, memory write

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

Website: chaining entries now stale-but-correct (per-F forms still true);
publication batch deferred until requested.

## Log

- 2026-08-15: plan approved (separable design / full symmetry / local main
  only); worktree created; 54 stubs written; notes seeded.
