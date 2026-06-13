Read CLAUDE.md (repo root) first and obey it — especially §2 (hypothesis-discipline tags),
§6 (search tools), §7 (Lean gotchas), §9, §10. Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`,
`./tools/check.sh '<fully.qualified.name>'`.

# TASK
Create `StatLean/ConcentrationInequalities/ClassicalLimits.lean`
(namespace `StatLean.ConcentrationInequalities`) — book-faithful statements of the two
classical limit theorems of Lu *Big Data Analysis* §2.1, each PROVED by delegating to Mathlib:

1. **Law of Large Numbers** (in probability): for i.i.d. integrable `X i`, the sample mean
   `(1/n) ∑_{i<n} X i` converges **in probability** to `μ = E[X 0]`.
2. **Central Limit Theorem**: for i.i.d. `X i` with mean `μ` and variance `σ² > 0`,
   `√n · ((X̄ₙ − μ)/σ)` converges **in distribution** to the standard Gaussian `N(0,1)`.

These are wrappers — do NOT re-prove. Find and delegate to the Mathlib results:
- LLN a.s.: `ProbabilityTheory.strong_law_ae` (gives a.e. convergence; derive in-probability from
  a.e. via the appropriate Mathlib lemma, e.g. `MeasureTheory.tendstoInMeasure_of_tendsto_ae` or
  `TendstoInMeasure`/`tendstoInMeasure_of_…` — check names). State the conclusion as convergence
  in probability (`TendstoInMeasure` or the `∀ ε>0, Tendsto (fun n => μ{|X̄ₙ − μ| ≥ ε}) atTop (𝓝 0)`
  form), which is the book's claim and is implied by the a.e. result.
- CLT: `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` (this is the i.i.d. CLT).
  **First run `./tools/check.sh 'ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub'`**
  and mirror its exact hypotheses (i.i.d. encoding via `iIndepFun` + `IdentDistrib`, the variance/
  `MemLp 2` conditions, the `gaussianReal`/standard-normal target). State the book theorem to match
  that lemma's hypotheses exactly, then close by applying it.

Use the SAME i.i.d. encoding Mathlib uses (`ProbabilityTheory.iIndepFun` + `IdentDistrib`/`MemLp`).
Book hypotheses (i.i.d., finite mean/variance) get `-- USER-INPUT: …; Lu-BDA §2.1`; any Mathlib-
required regularity not in the book gets `-- LEAN-ONLY: …`. If the book drops a hypothesis that
Mathlib's lemma needs (e.g. `MemLp 2`), KEEP the Mathlib hypothesis and note the strengthening in
the docstring — do not state an unprovable theorem.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/ClassicalLimits.lean`. Do NOT touch any
`Defs.lean`, the umbrella `StatLean/ConcentrationInequalities.lean`, `StatLean.lean`,
`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`. Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.ConcentrationInequalities.ClassicalLimits

# DONE = build exits 0; ZERO sorries; §2 tags on new hypotheses; small commits
(`conc(classical): LLN (in prob) + CLT wrappers (Lu-BDA §2.1)`). Finish by printing the declaration
names, build status, and any book→Lean hypothesis strengthening (and why). Independently re-verified.
