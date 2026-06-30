Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries in the target file. Lift sub-steps to `private` helpers IN THIS FILE; never `sorry`.

# CONTEXT
File: `StatLean/Minimaxity/Examples/LinearRegression.lean` (namespace `StatLean.Minimaxity`,
`open MeasureTheory ProbabilityTheory Matrix`, `open scoped ENNReal NNReal`). One `sorry`, the EXISTENTIAL
crux `linreg_local_packing_data` (Wainwright Ex 15.14, fixed-design Gaussian regression, prediction
seminorm). The public `linear_regression_minimax_rate` already assembles it through `minimax_local_packing`
(`Fano/LocalPacking.lean`). The crux must produce `∃ M θfam hθ c, IsSeparatedFamily g θfam δ ∧ (KL bound
15.35a) ∧ (cardinality 15.35b)` with `δ = √(v·r/(64n))`, `r = rank A`. READ the current crux signature in
the file — match it exactly.

# AUTHORIZED FIXES (both pre-approved: minimal forced hypothesis + loose constant — CLAUDE.md §1)
A prior pass proved the local-packing condition (15.35b) `2(c²nδ² + log2) ≤ log M` is UNSATISFIABLE with the
ORIGINAL fixed `δ² = v·r/(64n)` and the available packing `log M ≥ r/10` (the KL clause forces `c² ≥ 32/v`
while 15.35b needs `c² ≤ 3.2/v` — a factor-10 gap). APPLY both fixes:
* **Loosen the separation/rate constant.** Replace `64` in `δ² = v·r/(64n)` by a larger `C` (e.g. `C = 1280`)
  in BOTH `linreg_local_packing_data` and the rate in `linear_regression_minimax_rate` (which becomes
  `v·r/(2C·n)` ≈ `v·r/2560n`). Then `c²nδ² = c²vr/C`; with `c² = 32/v` (the KL clause), 15.35b reads
  `2(32r/C + log2) ≤ r/10`, i.e. `64/C ≤ 1/10 − 2log2/r`, satisfiable for `C ≥ 1280` and `r ≥ r₀`.
  Tag: `-- USER-INPUT: separation/rate constant loosened (book 128⁻¹) to fit the n/10 sphere-packing brick; Wainwright Ex 15.14, CLAUDE.md §1.`
* **Add `(hr0 : r₀ ≤ r)`** (the concrete threshold from the arithmetic, e.g. `r ≥ 40`), tagged
  `-- LEAN-ONLY: r ≥ r₀ — the local-packing/Fano condition (15.35b) needs Ω(r) hypotheses; small-rank is degenerate.`
  (Handle `r = 0` trivially if it remains in range: `δ = 0`, all `Pθ` equal, `klDiv = 0`, `M ≥ 4` constant family.)

# REUSE
* **Reroute to the CLOSED sphere packing** (more faithful to Ex 15.14, which packs `range(A)`):
  `exists_sphere_packing (r : ℕ) : ∃ T : Finset (EuclideanSpace ℝ (Fin r)), (r/10 : ℝ) ≤ Real.log T.card ∧
    (∀ v ∈ T, ‖v‖ = 1) ∧ ∀ u v ∈ T, u ≠ v → (1/2 : ℝ) ≤ ‖u - v‖` — `ForMathlib/Packing/SpherePacking.lean`.
  (Do NOT use `exists_sparse_packing` — replace that import. Loose log-constant `r/10` is fine.)
* **Equal-covariance multivariate Gaussian KL** (PUBLIC, in `ForMathlib/GaussianKLMulti.lean`, just merged):
  `klDiv_multivariateGaussian_smul_one (μ ν : EuclideanSpace ℝ (Fin d)) (c : ℝ≥0) (hc : c ≠ 0) :`
  `klDiv (multivariateGaussian μ (c • 1)) (multivariateGaussian ν (c • 1)) = ENNReal.ofReal (‖μ - ν‖^2 / (2*c))`.
  `import StatLean.Minimaxity.ForMathlib.GaussianKLMulti` and use it directly (the design matrix noise is
  `(v:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)`, so `c = v`). Confirm the exact signature with
  `./tools/api.sh StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean`.

# CONSTRUCTION (Ex 15.14)
`r := Module.finrank ℝ (LinearMap.range A)`. Take a linear ISOMETRY `e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] (LinearMap.range A)`
(both are `r`-dim inner-product spaces; `LinearIsometryEquiv` exists). For the sphere packing `S ⊆ ℝ^r`,
set `γ_s := (4δ√n) • (e s : EuclideanSpace ℝ (Fin n))` ∈ `range A`; choose `θ_s` with `A θ_s = γ_s`
(`LinearMap.mem_range`). Then `‖A(θ_s − θ_t)‖ = 4δ√n · ‖e s − e t‖ = 4δ√n·‖s−t‖ ∈ [2δ√n, 8δ√n]`
(isometry + packing `‖s−t‖∈[1/2,2]`; unit-norm ⇒ `≤2`). So `g`-separation `‖A(θ_s−θ_t)‖/√n ∈ [2δ,8δ]` ✓
(`IsSeparatedFamily g θfam δ`). KL: `D(P_{θ_s} ‖ P_{θ_t}) = ‖A(θ_s−θ_t)‖²/(2v) ≤ (8δ√n)²/(2v) = 32nδ²/v`,
matching the `c²·n·δ²` form with the crux's `c`. Cardinality `log M ≥ r/10`, and `15.35b`
`2(c²nδ² + log2) ≤ log M` holds for the chosen `δ² = v·r/(64n)` for `r` large (loose constants OK; pick the
provable `c`). Index `θfam : Fin M → ℝ^d` via `S`'s `Finset.equivFin`.

# REQUIREMENTS
ZERO sorry. Public name/conclusion unchanged. Helpers `private`, THIS file only. Swap the `SparsePacking`
import for `SpherePacking`; add `GaussianKLMulti` import. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`,
`lean-toolchain`, `lake-manifest.json`, `Defs.lean`, `Fano/`, other `Examples/`, `GaussianKLMulti.lean`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/LinearRegression.lean
# BUILD: lake build StatLean.Minimaxity.Examples.LinearRegression
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#22): close linreg_local_packing_data via range sphere-packing + multivariate Gaussian KL (Wainwright Ex 15.14)`.
  Report: build status, sorry count, packing reroute, which Gaussian-KL export you used, helpers, edge handling.
