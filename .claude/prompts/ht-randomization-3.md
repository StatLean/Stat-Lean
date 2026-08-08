# Close Randomization/{Asymptotics,SignChange,SlutskyRandomization,TwoSamplePermutation,Studentized,MultivariateQuadratic}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** those six `Randomization` files. Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — six such reports have been acted on this campaign; each unblocked real closures next pass.
- Commit after each lemma compiles.

## The blocker is gone: the Lindeberg CLT is now proved

`ForMathlib.LindebergCLT` is closed down to its statement layer — **`tendsto_prod_charFun_lindeberg` (the swapping estimate) and the uniform third-order remainder bound for `exp(iy)` are both proved**, so `lindeberg_clt`, `lindeberg_clt_of_bounded`, `weighted_iid_clt` and `triangular_wlln_of_L1` are available. These are the engines for everything below. (Mathlib has no triangular-array CLT; this was built for exactly this purpose.)

## Per file

- `Asymptotics` (3): the randomization distribution converges in probability at continuity points, and its quantile converges. `ForMathlib.QuantileFunction` is closed — `tendsto_quantile_of_tendsto` and `tendstoInMeasure_quantile` are the tools. The triangular-array indexing uses explicit type families; keep it.
- `SignChange` (4): sign-change group on `(Fin n → ℝ)`, consuming `lindeberg_clt_of_bounded` / `weighted_iid_clt`. **Do not add `E[ψ(X)] = 0`** — it is forced by "ψ odd" + "P symmetric" + square-integrability, so assuming it would be laundering; `0 < τ` is the explicit nondegeneracy.
- `SlutskyRandomization`: `cdf_map_affine` is closed and is stated for `0 < a` **because the source's own "a ≠ 0" parenthetical is false for negative scaling** — keep the positivity. Finish `randDist_affine_tendstoInProb`.
- `TwoSamplePermutation` (Thm 17.3.1): the source's route is conditioning on the permutation weights, then the **weighted-iid CLT** plus Cramér–Wold — *not* a combinatorial CLT. `ForMathlib.HypergeometricMoments` is closed and supplies `E Wᵢ`, `E WᵢWⱼ`, the covariance and the `O(1/m)` variance bound. Transcribe τ² exactly: permutation `τ² = λσ²(P_Y) + σ²(P_Z)` versus unconditional `σ²(P_Y) + λσ²(P_Z)` — the asymmetry is deliberate and both scalars are named in the file.
- `Studentized` (Thm 17.3.3): the studentized statistic is algebraically the **Welch** t-statistic (`studentizedTwoSample_eq_welch`), which is why the level result transfers without equal variances. The file deliberately does *not* claim equivalence with the pooled t-test — don't add it.
- `MultivariateQuadratic` (Lems 17.4.1–17.4.3): these use the **sign-change** group, not permutations. The χ² pair limit cites `StatLean.MultipleTesting.chiSquared`.

## Closed, axiom-clean — black boxes

`Randomization.{ExactLevel, OrbitConditional}` (exact finite-sample level Thm 17.2.1, orbit-conditional law Thm 17.2.2, p-value super-uniformity); `ForMathlib.{LindebergCLT, HypergeometricMoments, QuantileFunction, GroupAverageMeasure, CriticalFunction}`; `Tests.{PValue, Confidence}`; `NeymanPearson.Lemma.*`; `Invariance.UMPInvariantFinite.*`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms randDist_tendstoInProb_cdf`, and for anything left open the precise obstruction.
