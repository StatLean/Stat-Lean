Read CLAUDE.md (repo root) first — §2, §6, §7, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE.

# CONTEXT (do NOT modify; READ for the approach)
`OLS/MSEExpectation.lean` (imported) proves `mse_ols_expectation_le` (E[MSE] ≤ σ²r/n) and contains
(as PRIVATE lemmas you may re-derive) the facts: OLS prediction `designMap X βhat = orthogonalProjection (columnSpace X) Y`;
prediction error `designMap X βhat − designMap X βstar = P_C ε`; Parseval over an ONB of the r-dim
column space; and that each ONB coordinate `⟪eₖ, ε⟫` is sub-Gaussian with proxy `σ²` (the
`subGaussian_coords` fact). `LinearModel/Defs.lean`: `designMap`, `mse`, `IsOLSEstimator`, `columnSpace`,
`designRank`. `Maximal/L2Maximal.lean` (imported): `l2_max_expectation` and `l2_max_tail`
(`thm:l2`): for a sub-Gaussian random vector `Z : Ω → EuclideanSpace ℝ (Fin r)` (`⟪u,Z⟫` sub-Gaussian
proxy `σ²‖u‖²`), `μ{4σ√r + 2σ√(2 log(1/δ)) < ‖Z‖} ≤ ENNReal.ofReal δ`.

# TASK
Create `StatLean/HighDimensionalStatistics/OLS/MSEHighProb.lean`
(namespace `StatLean.HighDimensionalStatistics`) proving the HIGH-PROBABILITY half of Lu *Big Data
Analysis* §5 `thm:mse-ols`: for `Y = designMap X βstar + ε`, `ε` independent sub-Gaussian proxy `σ²`,
`r = designRank X`, `βhat` an `IsOLSEstimator X Y`, and `δ ∈ (0,1)`, with probability `≥ 1−δ`:
  `mse X (βhat ω) βstar ≤ C·σ²·r/n + C'·(σ²/n)·log(1/δ)`  (state the explicit provable constants; book uses `≲`).

# PROOF
`mse = (1/n)‖P_C ε‖²` (re-derive the projection identity as in MSEExpectation, OR if cleaner, make the
needed MSEExpectation lemmas non-private — but PREFER keeping touch-set to ONLY this file and
re-deriving). The projected noise `P_C ε`, written in an ONB `{eₖ}_{k<r}` of `columnSpace X`, is a
sub-Gaussian random vector in `EuclideanSpace ℝ (Fin r)` with proxy `σ²` (each coord `⟪eₖ,ε⟫`
sub-Gaussian σ² by the linear-combination/`hoeffding` argument — re-derive the `subGaussian_coords`
fact). Apply `l2_max_tail` (thm:l2) to this r-dim sub-Gaussian vector: w.p. `≥ 1−δ`,
`‖P_C ε‖ ≤ 4σ√r + 2σ√(2 log(1/δ))`. Square and divide by `n`:
`mse = ‖P_Cε‖²/n ≤ (4σ√r + 2σ√(2log(1/δ)))²/n ≤ (use (a+b)² ≤ 2a²+2b²) ≤ 32σ²r/n + 16σ²log(1/δ)/n`.
So `C = 32, C' = 16` (or tighter — state what you prove). Bridge the `ENNReal.ofReal δ` measure form
to "probability ≥ 1−δ" via complement.

ZERO sorry. Independence, sub-Gaussian σ², `Y=Xβ*+ε`, `IsOLSEstimator`, `δ∈(0,1)` are
`-- USER-INPUT: …; Lu-BDA §5 (thm:mse-ols)`. If re-deriving the projection/coords becomes huge, you
MAY change the relevant MSEExpectation.lean lemmas from `private` to public (add that file to the
touch-set) and reuse them — but then re-gate both files.

# TOUCH-SET: prefer ONLY `StatLean/HighDimensionalStatistics/OLS/MSEHighProb.lean` (may also touch
#   MSEExpectation.lean ONLY to un-`private` reused lemmas, if needed).
# BUILD: lake build StatLean.HighDimensionalStatistics.OLS.MSEHighProb
# DONE = build exits 0; ZERO sorries; §2 tags; commit
(`hds(ols): high-prob MSE bound σ²r/n + σ²log(1/δ)/n (Lu-BDA §5 thm:mse-ols)`). Report build + sorry + constants.
