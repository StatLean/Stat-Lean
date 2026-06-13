Read CLAUDE.md (repo root) first and obey it — §2 (hypothesis tags), §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`.

# TASK
Create `StatLean/ConcentrationInequalities/SubGaussian/Chernoff.lean`
(namespace `StatLean.ConcentrationInequalities`) formalizing two results of Lu *Big Data Analysis* §2.2:

1. **Markov inequality** (label `Markov`): for a nonnegative random variable `X` and `t > 0`,
   `P(X > t) ≤ E[X] / t`. Delegate to Mathlib — check
   `./tools/check.sh 'MeasureTheory.mul_meas_ge_le_integral_of_nonneg'` (and nearby
   `meas_ge_le_…` lemmas) and mirror its measure/ENNReal shape. State faithfully (nonneg `X`,
   `t > 0`, integrable `X`).

2. **Chernoff bound** (label `thm:chernoff`): with the log-MGF (cumulant generating function)
   `ψ(λ) = log E[exp(λ(X − E X))]` and its Legendre dual `ψ*(t) = ⨆_{λ ≥ 0} (λ t − ψ(λ))`,
   `P(X − E X > t) ≤ exp(−ψ*(t))` for `t ≥ 0`.
   Use Mathlib's `ProbabilityTheory.cgf` for `ψ` and `ProbabilityTheory.measure_ge_le_exp_mul_mgf`
   (or `measure_ge_le_exp_cgf`-style) as the engine. Check those signatures first.
   The Legendre dual `⨆_{λ ≥ 0} (λ t − ψ(λ))` over reals can hit junk values when the set is
   unbounded above; if you need `BddAbove {λ t − ψ λ | λ ≥ 0}` (or an integrability/MGF-finiteness
   hypothesis) to make the `iSup` meaningful, ADD it with a `-- LEAN-ONLY: <why>` tag rather than
   stating something false. The MGF-finiteness / `t ≥ 0` / nonneg hypotheses get
   `-- USER-INPUT: …; Lu-BDA §2.2`.

You may use our `IsSubGaussian` (in `…/SubGaussian/Defs.lean`) if helpful, but these two are general
(not sub-Gaussian-specific). Prefer Mathlib's `mgf`/`cgf` API directly.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/SubGaussian/Chernoff.lean`. Do NOT touch any
`Defs.lean`, the umbrella, `StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`,
`notes/`. Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.ConcentrationInequalities.SubGaussian.Chernoff

# DONE = build exits 0; ZERO sorries; §2 tags; small commits
(`conc(subgaussian): Markov + Chernoff (Lu-BDA §2.2 Markov, thm:chernoff)`). Finish by printing
declaration names, build status, and any added LEAN-ONLY side conditions (and why). Independently re-verified;
a weakened or vacuous statement (e.g. a trivial `ψ*` that makes the bound meaningless) will be rejected.
