Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`. Build with plain `lake build`. `private` helpers IN THIS FILE; never fabricate.

# CONTEXT — FINISH a NON-BUILDING faithful-#18 draft
File: `StatLean/Minimaxity/Examples/LipschitzDensity.lean`. A prior session wrote the FAITHFUL #18
(`quadratic_functional_two_point_rate`: `minimaxRiskDist id`, real `θfunc i = ∫ x in Icc 0 1, (deriv (f i) x)^2`,
rate `n^{-1/2}`) reusing #17's bump/Hellinger machinery, BUT IT DOES NOT COMPILE. `lake build
StatLean.Minimaxity.Examples.LipschitzDensity` currently errors:
- `Unknown identifier 'deriv'` / `'HasDerivAt'` / `'hasDerivAt_id'` / `'measurable_deriv'` (≈ lines 734–878) —
  **missing imports** for the derivative API.
- cascading `Type mismatch` (≈598), `unsolved goals ⊢ a^2*δ ≤ ∫ sorry^2` (≈748), `rewrite failed` (≈887) —
  all downstream of `deriv` being unknown; they should resolve once the derivative API is imported and the
  derivative computations go through.

# TASK — make it BUILD to 0 errors / 0 sorries, keeping #17 untouched.
1. Add the derivative-API imports at the top: `import Mathlib.Analysis.Calculus.Deriv.Basic`,
   `Mathlib.Analysis.Calculus.Deriv.Add`, `Mathlib.Analysis.Calculus.Deriv.Mul`,
   `Mathlib.Analysis.Calculus.Deriv.Comp`, and `Mathlib.Analysis.Calculus.Deriv.Pow` as needed
   (search `./tools/explore.sh "deriv of composition"` / `"HasDerivAt const mul"`).
2. `measurable_deriv` does NOT exist in general. For the functional integrand `(deriv (f i) x)^2`: either
   (a) prove the density `f i` is `C¹` on `(0,1)` and use `Continuous.measurable` of the explicit derivative,
   or (b) replace `deriv (f i)` in the *proof* with an explicit `f' i` you define (`HasDerivAt (f i) (f' i x) x`)
   and rewrite `θfunc i = ∫ (f' i)^2` via `MeasureTheory.integral_congr_ae` + the a.e. equality
   `deriv (f i) =ᵐ f' i`. Keep `θfunc i = ∫ (deriv (f i))^2` in the STATEMENT (faithful), but compute through `f' i`.
3. Fix the cascading `598/748/887` goals once the derivative value is known: the gap `θfunc(true) − θfunc(false)
   = ∫(g')² − 0 = C²b₁/m² ≍ n^{-1/2}`; feed it to `minimax_functional_modulus` (Φ=id) exactly as the draft intends.
4. If the draft's bump is the piecewise hat (deriv is `±slope`, a step function): `deriv (hat) =ᵐ` an explicit
   step function; `∫(step)² = ∑ slope²·length`. Use `intervalIntegral`/`Set.indicator` and a.e. equality.

VERIFY: run `lake build StatLean.Minimaxity.Examples.LipschitzDensity` and confirm it EXITS 0 with NO errors
and NO sorry, AND that `lipschitz_density_pointwise_rate` (#17, `(·²)`, `n^{-2/3}`) is unchanged and still builds.
Do NOT report done until the build is green.

# REQUIREMENTS / TOUCH-SET
ZERO sorry, ZERO errors. Touch ONLY `StatLean/Minimaxity/Examples/LipschitzDensity.lean` (+ the new imports).
Do NOT change #17. No edits to umbrella/lakefile/toolchain/manifest/Defs/Fano/LeCam/other Examples.
BUILD: `lake build StatLean.Minimaxity.Examples.LipschitzDensity`. DONE = exit 0, no error, no sorry, #17 intact.
Commit: `mmx(#18): faithful quadratic two-point builds — real ∫(f')², abs loss, n^{-1/2} (Ex 15.8)`.
Report: build status (MUST be green), sorry count, what imports/fixes were needed, confirmation #17 intact.
