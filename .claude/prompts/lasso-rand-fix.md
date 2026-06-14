Read CLAUDE.md (repo root) first — §2, §6, §7. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build` and ITERATE until 0 errors.

# CONTEXT
`StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean` is MOSTLY written (the cor:lasso-rate
proof — union bound over `2d` sub-Gaussian `⟨X_j,ε⟩`, then apply the merged deterministic
`lasso_l2_rate`) but a preemption left it BROKEN. Fix ALL errors to ZERO-error, ZERO-sorry. Do NOT
weaken the statement. (Read the original spec in `.claude/prompts/lasso-randomnoise.md` for the math.)

# CURRENT ERRORS (latest gate):
- 113:41 and 163:4: `No goals to be solved` — drop the stray trailing tactics (§7.10).
- 285:7: `unknown tactic` — fix/replace the malformed tactic.
- 282:42: `Application type mismatch` — wrong argument arity/order; inspect the lemma call.
- 275:76 and 260:75: `unsolved goals` — finish those proof steps.

Re-read the file, fix each, rebuild, repeat until clean. The key pieces (each `⟨X_j,ε⟩` sub-Gaussian
proxy `σ²‖X_j‖²≤σ²n` via `hoeffding`; union bound `2d·exp(−t²/2σ²n)`; tuning `λ` solve; apply
`lasso_l2_rate`) are already there — this is a finish/cleanup pass, not a rewrite. Keep the corrected
provable `λ` constant + its docstring note.

# TOUCH-SET: ONLY `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean`.
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.RandomNoise
# DONE = build exits 0; ZERO sorries; commit (`hds(lasso): fix cor:lasso-rate build (Lu-BDA §8)`).
# Report build + sorry count (must be 0) + the λ constant.
