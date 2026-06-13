Your previous session on `StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean` was
preempted (SIGTERM) before you verified the build. A fresh `lake build
StatLean.HighDimensionalStatistics.ForMathlib.VecNorms` now FAILS with these errors. Fix ALL of
them to a clean ZERO-error, ZERO-sorry build. Re-read CLAUDE.md §7 (Lean gotchas), especially §7.2
(real inner product `⟪·,·⟫_ℝ`).

ERRORS (current file):
1. line ~3: `import Mathlib.Analysis.Real.Sqrt` does NOT exist — use `import Mathlib.Data.Real.Sqrt`.
2. line ~46: `linfNorm` "failed to compile definition, consider marking it as 'noncomputable'
   because it depends on 'Real.instSupSet'" — mark `noncomputable def linfNorm`. (The `⨆` over a
   `Real` is noncomputable. Alternatively switch `linfNorm` to `Finset.univ.sup' …` over `|x.ofLp i|`
   which IS computable and is often EASIER to prove the Hölder bound with — your choice, but it must
   build.)
3. line ~54: Type mismatch — fix following from the `linfNorm` change.
4. line ~62: `rewrite` failed (pattern not found) — re-derive; do not force a `rw` that doesn't match.
5. lines ~72, ~93: `Unknown constant 'Real.inner_apply'` — there is NO `Real.inner_apply`. For the
   real inner product use `RCLike.inner_apply` (note: it gives `⟪a,b⟫_ℝ = b * a`, the OPPOSITE order —
   see §7.2), OR, when both arguments are plain `ℝ`/coordinate sums, use the §7.2 trick
   `change a * b = b * a; ring` (holds by defeq), OR `PiLp.inner_apply` / `EuclideanSpace.inner_eq_star_dotProduct`
   for the `EuclideanSpace` inner as a sum `∑ i, x i * y i`. Search with
   `./tools/loogle.sh '"inner_apply"'` and `./tools/check.sh 'PiLp.inner_apply'` to pick the one that
   matches your goal shape.
6. line ~130: "typeclass instance problem is stuck" — usually a missing `Fintype`/`DecidableEq`
   instance annotation or an `EuclideanSpace`-vs-`PiLp` coercion; make the instance explicit.

Keep the SAME public API names you already chose (`l1Norm`, `linfNorm`,
`abs_inner_le_l1Norm_mul_linfNorm`, `restrict`, `norm_restrict_le_norm`, etc.) so downstream Lasso
files can rely on them. Do NOT weaken any statement (the √s support bound and Hölder must keep their
exact constants). Keep all docstrings.

# TOUCH-SET: ONLY `StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean`.
# BUILD: lake build StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
# DONE = build exits 0, ZERO sorries. Commit (`hds(vecnorms): fix build — noncomputable linfNorm,
#   real inner_apply, import (Lu-BDA ch8)`). Print final declaration names + build status.
