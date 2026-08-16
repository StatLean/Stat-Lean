# chaining-sup — status

Branch `conc/chaining-sup` off local main `bb84b0b2`. See `outline.md` for
the tree/constants; plan at `~/.claude/plans/i-want-to-fix-eager-snail.md`.

## Stub inventory (54 sorries, all named top-level decls)

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

- [ ] Stub gate (cluster): all 6 new modules + DudleyConsumers green-with-54-sorries
- [ ] Wave 1 closure (CountableSupLift ‖ SeparableProcess)
- [ ] Wave 2a closure (DudleySup ‖ GenericChainingSup)
- [ ] Wave 2b closure (DudleyTailSup ‖ DiscreteDudleySup)
- [ ] Wave 2c closure (DudleyConsumers)
- [ ] Verification gate (laptop): fresh branch-tip build, 0 stray sorries,
      diff ⊆ touch-set, tags present, existing decls byte-identical,
      `#print axioms` on all 54 decls
- [ ] Merge to local main + umbrella imports (6 new modules) + full-lib gate
- [ ] lean-fasrc-sync, worktree cleanup, memory write

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
