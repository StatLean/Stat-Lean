# Close Bootstrap/*.lean (Ch 18.1–18.5 — bootstrap consistency)

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session. Work the files sequentially, committing each as it compiles.

## Hard constraints

- **Only edit** `StatLean/HypothesisTesting/Bootstrap/{Consistency,ParametricLocal,NonparametricMean,Multivariate,Edgeworth,Testing}.lean`.
- Signatures FROZEN. Add `import Mathlib.*`, closed modules, `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors** except the Edgeworth deferrals. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely — ten such reports have been acted on this campaign, five of them false statements caught with counterexamples. That is the highest-value output.
- Commit after each lemma compiles.

## Sanctioned deferrals — do NOT attempt

`Edgeworth.{edgeworth_studentized, edgeworth_uniform}` (Thms 18.4.1/18.4.2) and their Cornish–Fisher corollary are **proofless in the source** (Hall 1992); statement-plus-deferral by prior agreement. Leave them with their notes.

## Design reminders (these are deliberate, do not "fix" them)

- The bootstrap is formalized in the **sequence-class `C_P` register**, not with a metric on measures: weak convergence is pointwise CDF convergence, and membership of the empirical sequence in `C_P` is the only stochastic ingredient. The sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` and `C_P` are theorem-level data supplied with their defining properties — no measurability in the measure argument.
- Thm 18.3.2 uses the **uniform-over-compact-h subsequence** route in place of Skorokhod representation, and needs **tightness** of `√n(θ̂ₙ − θ)`, not mere consistency (consistency alone never activates a compact-`h` hypothesis). These are in the frozen signatures.
- Thm 18.5.1 carries **strict increase at the quantile**, not just continuity of the limit CDF (a flat stretch at height `1 − α` leaves the quantile undetermined).

## Order of attack

1. `Consistency` (Thm 18.3.1 + Lem 18.3.1): the three conclusions — a.s. sup-convergence (via `ForMathlib.PolyaUniformCDF`, closed), quantile consistency (via `cdfPseudoInverse` + strict increase), asymptotic coverage. `triangular_wlln_of_L1` from the closed `ForMathlib.LindebergCLT` is the Lem 18.3.1 engine.
2. `NonparametricMean` (Thms 18.3.3/18.3.4): `C_F` = sequences with weak + mean + variance convergence; `mean_root_cdf_tendsto` via `ForMathlib.LindebergCLT` (closed), `empirical_mem_CF` via Mathlib's SLLN (`strongLawOfLargeNumbers`-family) + a Glivenko–Cantelli-flavored step, then the headline consistency. The studentized version ⇒ N(0,1).
3. `Multivariate` (Thms 18.3.5/18.3.6): covariance-matrix convergence + Cramér–Wold, then the delta-method for smooth functions of means.
4. `ParametricLocal` (Thm 18.3.2 + Cor 18.3.1) and `Testing` (Thm 18.5.1): the local-uniformity and null-restricted-estimator arguments.

## Closed, axiom-clean — black boxes

`ForMathlib.{LindebergCLT, PolyaUniformCDF, QuantileFunction, CriticalFunction}`; `Bootstrap/Defs` (`empiricalMeasure`, `supCDFDist`, `cdfPseudoInverse`); Mathlib `strongLawOfLargeNumbers`, `multivariateGaussian`, `charFun`; the repo's `MultivariateCLT`/`CramerWold`; `MultipleTesting.ForMathlib.EmpiricalCDF`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms bootstrap_mean_consistent`, and for anything left open the precise obstruction.
