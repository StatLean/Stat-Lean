# HighDimensionalStatistics — roadmap

Area reference: Lu, *Big Data Analysis*, ch. 5 and ch. 8. Tag with `Lu-BDA §X.Y`. Scope (Batch 1) is exactly three results:

- ch5 `thm:mse-ols` — MSE of least squares: fixed design `X` rank `r`, i.i.d. sub-Gaussian noise (proxy `σ²`) ⇒ `E[MSE(X β̂)] ≲ σ²r/n`, and w.p. `1-δ` also `+ σ² log(1/δ)/n`.
- ch8 `thm:re` — deterministic Lasso rate: under `RE(κ,3)` and `λ ≥ (2/n)‖Xᵀε‖∞`, `‖β̂ − β*‖₂ ≤ 3√s·λ/κ`.
- ch8 `cor:lasso-rate` — sub-Gaussian noise + normalized columns + explicit `λ` ⇒ `‖β̂ − β*‖₂ = O_P(√(s log d / n))`.

> Constants: the book's `λ` in `cor:lasso-rate` is ~4× too small to satisfy `λ ≥ (2/n)‖Xᵀε‖∞` under the stated tail bound — state the corrected `λ` and document. OLS: state the explicit constant where provable instead of `≲`.

## Milestones

| Milestone dir | Owns |
|---|---|
| `ols_mse/` | ch5 `thm:mse-ols` (expectation + high-prob halves) |
| `lasso_rate/` | ch8 `thm:re` (deterministic) + `cor:lasso-rate` (random noise) |

## Layout (`StatLean/HighDimensionalStatistics/`, namespace `StatLean.HighDimensionalStatistics`)

```
HighDimensionalStatistics/
├── ForMathlib/VecNorms.lean        -- ℓ¹/ℓ∞ defs, Hölder |⟨x,y⟩| ≤ ‖x‖₁‖y‖∞, ‖Δ_S‖₁ ≤ √s‖Δ‖₂, support restriction
├── LinearModel/Defs.lean           -- fixed design (Matrix (Fin n) (Fin d) ℝ), mse, IsOLSEstimator (minimizer predicate), columnSpace via LinearMap.range
├── OLS/{MSEExpectation,MSEHighProb}.lean
└── Lasso/{Defs,DeterministicRate,RandomNoise}.lean
```

Key design decisions:
- **No Moore-Penrose pseudoinverse** (not usable in the pin). State OLS predictions via **orthogonal projection onto the column space** `LinearMap.range X.mulVecLin`; `IsOLSEstimator` is a zero-order-minimizer predicate, not a closed-form.
- Vectors = `EuclideanSpace ℝ (Fin n)` (ℓ² + inner product); `l1Norm`/`linfNorm` as explicit defs (do not stack `PiLp` instances on one type).
- Cross-area: imports `StatLean.ConcentrationInequalities.SubGaussian.{Defs,Hoeffding,TailBounds}` (noise bounds) and `…Maximal.L2Maximal` (`thm:l2`, for the OLS high-prob half over the r-dim column space). DAG: `ConcentrationInequalities → HighDimensionalStatistics`.

## Hardest item (time-box + named-sorry fallback)
- `OLS/MSEHighProb` orthonormal-basis-of-submodule glue (`EuclideanSpace ℝ (Fin r)` coordinates of the projected noise, each sub-Gaussian). Fallback sorry: `subGaussian_coords_of_orthonormal`; the projection inequality and `thm:l2` application close independently.

DAG within area: `VecNorms → {LinearModel → OLS, Lasso/Defs → Lasso/DeterministicRate → Lasso/RandomNoise}`.
