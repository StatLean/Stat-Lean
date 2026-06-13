Read CLAUDE.md (repo root) first and obey it — especially §2 (hypothesis-discipline tags),
§6 (search tools), §7 (Lean gotchas), §9 (what not to do), §10. Use the search tools
`./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<fully.qualified.name>'`.

# TASK
Create the file `StatLean/ConcentrationInequalities/SubGaussian/TailBounds.lean`
(namespace `StatLean.ConcentrationInequalities`) formalizing, from Lu *Big Data Analysis*
§2.2 (Theorem "Two-Sided Tail Probability", label `thm:two-sided`):

  If `X` is sub-Gaussian with variance proxy `σ²`, then for all `t > 0`,
      P(|X − E X| > t)  ≤  2 · exp(−t² / (2σ²)).

Also provide the one-sided form used in its proof:
      P(X − E X > t)  ≤  exp(−t² / (2σ²)).

Write the FAITHFUL Lean statements — do NOT weaken hypotheses or conclusions. The
sub-Gaussian hypothesis is our predicate `IsSubGaussian X σ² μ` (defined in
`StatLean/ConcentrationInequalities/SubGaussian/Defs.lean` as
`HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ² μ`). Use measure language
`μ {ω | t < |X ω - ∫ x, X x ∂μ|} ≤ …` (ENNReal RHS via `ENNReal.ofReal`), matching how
Mathlib's `HasSubgaussianMGF.measure_ge_le` states its conclusion — check that lemma's exact
signature first with `./tools/check.sh 'ProbabilityTheory.HasSubgaussianMGF.measure_ge_le'`
and mirror its shape (it gives the one-sided bound for the centered variable directly).

Then PROVE both. Proof sketch (book): one-sided is `HasSubgaussianMGF.measure_ge_le` applied to
the centered variable (which is exactly `IsSubGaussian` unfolded); the left tail comes from the
same applied to `-X` (use `HasSubgaussianMGF.neg`); two-sided is the union bound over the two
one-sided events (`measure_union_le` / `Set.abs_lt`-style splitting), then `2 *` the bound.

Mathlib bricks to verify-then-use: `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`,
`ProbabilityTheory.HasSubgaussianMGF.neg`, `measure_union_le`, ENNReal arithmetic. Any
non-book regularity hypothesis you must add (e.g. an integrability or `0 ≤ t`) gets a
`-- LEAN-ONLY: <why>` tag; the sub-Gaussian and `t > 0` hypotheses get `-- USER-INPUT: …; Lu-BDA §2.2`.

# TOUCH-SET
You may create/modify ONLY `StatLean/ConcentrationInequalities/SubGaussian/TailBounds.lean`.
Do NOT touch any `Defs.lean`, the area umbrella `StatLean/ConcentrationInequalities.lean`,
`StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, or `notes/`.
Never run `lake update`.

# BUILD to verify (you are inside the cluster worktree)
  lake build StatLean.ConcentrationInequalities.SubGaussian.TailBounds
(if you are already inside an srun allocation, just `lake build StatLean.ConcentrationInequalities.SubGaussian.TailBounds`).

# DEFINITION OF DONE (all required)
1. `lake build StatLean.ConcentrationInequalities.SubGaussian.TailBounds` exits 0.
2. ZERO sorries (this item has no sanctioned named debt).
3. Every new hypothesis carries a `-- USER-INPUT:`/`-- LEAN-ONLY:` tag (§2).
4. Small commits, message like `conc(subgaussian): two-sided tail (Lu-BDA §2.2 thm:two-sided)`.
Finish by printing: the declaration names you added, the final build status, and any
deviation from the book statement (and why). Your work will be INDEPENDENTLY re-verified by a
fresh build + statement audit — a weakened statement that merely compiles will be rejected.
