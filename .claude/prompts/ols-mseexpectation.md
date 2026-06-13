Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §9, §10. Use the search tools.
Never `lake update`. You are ALREADY inside an srun allocation — build with plain `lake build`, ITERATE.

# CONTEXT (do NOT modify; READ them)
`LinearModel/Defs.lean`: `designMap X : E^d →ₗ E^n`, `mse X β βstar = (1/n)‖designMap X β − designMap X βstar‖²`,
  `IsOLSEstimator X Y βhat := ∀ β, ‖Y − designMap X βhat‖² ≤ ‖Y − designMap X β‖²`,
  `columnSpace X := LinearMap.range (designMap X)`, `designRank X := X.rank`.
`SubGaussian/{Defs,Hoeffding}.lean`: `IsSubGaussian`, `hoeffding` (linear-combo of indep sub-Gaussians).

# TASK
Create `StatLean/HighDimensionalStatistics/OLS/MSEExpectation.lean`
(namespace `StatLean.HighDimensionalStatistics`) proving the EXPECTATION half of Lu *Big Data
Analysis* §5 **MSE of least squares** (`thm:mse-ols`): for `Y = designMap X βstar + ε` with `ε`
independent coordinates each sub-Gaussian proxy `σ²` (mean 0), `r = designRank X`, and `βhat` any
`IsOLSEstimator X Y`, the expected prediction MSE satisfies
  `∫ ω, mse X (βhat ω) βstar ∂μ ≤ σ² · r / n`   (state the explicit constant; book uses `≲`).

# PROOF (Lu §5)
1. **OLS prediction = orthogonal projection**: `IsOLSEstimator` ⇒ `designMap X βhat` minimises
   `‖Y − v‖²` over `v ∈ columnSpace X`, so `designMap X βhat = orthogonalProjection (columnSpace X) Y`
   (Mathlib: `orthogonalProjection` is THE minimiser — `orthogonalProjection_minimal` /
   `norm_sub_orthogonalProjection_le`; `columnSpace X` is finite-dim hence complete, so
   `[CompleteSpace …]`/`HasOrthogonalProjection` holds — get the instance).
2. **Prediction error = projected noise**: since `designMap X βstar ∈ columnSpace X`,
   `designMap X βhat − designMap X βstar = P_C Y − designMap X βstar = P_C(designMap X βstar + ε) −
   designMap X βstar = P_C ε`. So `mse = (1/n)‖P_C ε‖²`.
3. **`E‖P_C ε‖² ≤ σ²·r`**: take an `OrthonormalBasis (Fin r)` of `columnSpace X` (dim `r`); then
   `‖P_C ε‖² = ∑_{k<r} ⟨eₖ, ε⟩²` (Parseval, `OrthonormalBasis.sum_inner_mul_inner`/`norm_sq_eq_sum`).
   Each `⟨eₖ, ε⟩ = ∑ᵢ (eₖ)ᵢ εᵢ` is sub-Gaussian proxy `σ²‖eₖ‖² = σ²` (orthonormal ⇒ `‖eₖ‖=1`), by
   `hoeffding`/independence — THIS is the `subGaussian_coords_of_orthonormal` step; prove it. A
   mean-0 sub-Gaussian proxy `σ²` has `E[Z²] = Var ≤ σ²` (search
   `./tools/loogle.sh '"HasSubgaussianMGF"' '"variance"'` / `'"variance_le"'`; the variance bound is
   standard — if Mathlib lacks it, derive from the MGF: `E[Z²] = ψ''(0) ≤ σ²`). Sum over `k<r` ⇒ `σ²r`.
4. Combine: `E[mse] = (1/n)·E‖P_Cε‖² ≤ σ²r/n`.

# ZERO sorry is the bar. The hard sub-lemma is step 3 (orthonormal coords sub-Gaussian + variance
bound) — the roadmap's `subGaussian_coords_of_orthonormal`; prove it in-file. If a TRULY irreducible
Mathlib gap remains, isolate ONE named sorry + ESCALATE note. Independence + sub-Gaussian σ² +
`Y=Xβ*+ε` + `IsOLSEstimator` are `-- USER-INPUT: …; Lu-BDA §5 (thm:mse-ols)`.

# TOUCH-SET: ONLY `StatLean/HighDimensionalStatistics/OLS/MSEExpectation.lean`.
# BUILD: lake build StatLean.HighDimensionalStatistics.OLS.MSEExpectation
# DONE = build exits 0; ZERO sorries (or 1 named + ESCALATE); §2 tags; commit
(`hds(ols): E[MSE] ≤ σ²r/n (Lu-BDA §5 thm:mse-ols, expectation half)`). Report build + sorry status + constant.
