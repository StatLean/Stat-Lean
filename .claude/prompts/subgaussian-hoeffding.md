Read CLAUDE.md (repo root) first and obey it — §2 (hypothesis tags), §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`.

# TASK
Create `StatLean/ConcentrationInequalities/SubGaussian/Hoeffding.lean`
(namespace `StatLean.ConcentrationInequalities`) formalizing Lu *Big Data Analysis* §2.2,
Theorem "Hoeffding Inequality" (label `thm:hoefdding`):

  If `X 0, …, X (n−1)` are **independent** and each is sub-Gaussian with variance proxy `σ²`,
  then for `t > 0`:
      P( (1/n) ∑_{i<n} X i  −  (1/n) ∑_{i<n} E[X i]  >  t )  ≤  exp(−n t² / (2σ²)).
  (Equivalently, the centered sum `∑_{i<n} (X i − E[X i])` exceeds `n t` with the same bound.)

Engine: Mathlib `ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`
— **check its exact signature first** (`./tools/check.sh`), it gives precisely a sub-Gaussian
sum tail. Our predicate `IsSubGaussian (X i) σ² μ` (in `…/SubGaussian/Defs.lean`) unfolds to
`HasSubgaussianMGF (fun ω => X i ω − ∫ x, X i x ∂μ) σ² μ`, i.e. the centered variable — feed those
to the Mathlib lemma. Encode independence with the SAME structure the Mathlib lemma wants
(`ProbabilityTheory.iIndepFun`).

Then add the **weighted-sum lemma** (used later by OLS/Lasso): if `X` is sub-Gaussian with proxy
`σ²` and `c : ℝ`, then `c • X` (i.e. `fun ω => c * X ω`) is sub-Gaussian with proxy `c² σ²` —
delegate to `ProbabilityTheory.HasSubgaussianMGF.const_mul` (check its signature; mind the proxy
scaling `(c² : ℝ≥0)` and centering). State it in terms of our `IsSubGaussian`.

Independence + sub-Gaussian + `t > 0` hypotheses get `-- USER-INPUT: …; Lu-BDA §2.2`; any Mathlib-
required regularity (probability measure, measurability) gets `-- LEAN-ONLY: …`. Keep the conclusion
faithful (the `exp(−n t²/(2σ²))` rate; do not weaken to a non-quantitative bound).

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/SubGaussian/Hoeffding.lean`. Do NOT touch any
`Defs.lean`, the umbrella, `StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`,
`notes/`. Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.ConcentrationInequalities.SubGaussian.Hoeffding

# DONE = build exits 0; ZERO sorries; §2 tags; small commits
(`conc(subgaussian): Hoeffding sample-mean inequality + weighted-sum (Lu-BDA §2.2 thm:hoefdding)`).
Finish by printing declaration names, build status, and any book→Lean deviations. Independently re-verified.
