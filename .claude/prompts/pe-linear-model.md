# Close the sorries in PointEstimation/LinearModel/{Canonical,LeastSquares,GaussMarkov,Equivariant,RandomDesign}.lean

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (Note: the repo `CLAUDE.md` is gitignored and is NOT present in this worktree — everything you need is below. Project rules that matter here: never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

You are ON the cluster. Iterate with plain foreground `lake build StatLean.PointEstimation.LinearModel.Canonical`, then `.LeastSquares`, `.Equivariant`, `.GaussMarkov`, `.RandomDesign`. **Never** background a build, never nest `srun`/`sbatch`, never poll with `until pgrep`.

## Hard constraints

- **Only edit** those five files under `StatLean/PointEstimation/LinearModel/`. Touch nothing else — in particular NOT `LinearModel/Defs.lean` (frozen, laptop-only).
- **Signatures, hypothesis tags, docstrings FROZEN.** You may add `import Mathlib.*`, import already-closed project modules, and add `private` helpers. Lines ≤ 100 characters.
- Goal: **0 sorries, 0 errors**, except the one sanctioned deferral below. Escape hatch elsewhere: at most one lifted `private` sorry per file with a precise `-- TODO:`; report each.
- **Do not weaken any statement.** If one looks false, STOP, leave it sorried, report the counterexample.
- Commit after each lemma compiles.
- After green: `#print axioms gauss_markov`, `#print axioms isUMVU_lse_functional` — expect only `propext, Classical.choice, Quot.sound`.

## Sanctioned deferral

`RandomDesign.not_exists_blue_of_known_design_moment` is marked **DEFERRAL-ELIGIBLE**. It also carries a nondegeneracy hypothesis beyond the printed source statement, because **the universal form as printed is false**: for an a.s. constant design the fixed-design theorem does supply a BLUE. Do not remove that hypothesis. Close it if you can; otherwise leave it sorried with a `-- TODO:` and report.

## Already closed, treat as black boxes (import them)

- `Completeness.ExpFamily.isCompleteStat_of_interior_nonempty` — exponential-family completeness (Thm 6.22), axiom-clean. The canonical normal model's `(Y₁..Y_s, S²)` is an exponential family; this is how `canonicalStat_isCompleteStat` should be discharged.
- `Sufficiency.Factorization.*` (Fisher–Neyman, both directions) and `Sufficiency.RegularConditional.hasSufficientKernel_of_isSufficient_dominated`.
- `UMVU.LehmannScheffe.*` and `UMVU.RaoBlackwell.*` (may still be landing in a sibling session — if an import fails, state your UMVU conclusions via `IsUMVU` directly and note it).
- `ExponentialFamily.{Basic,MGF,NaturalStatistic}`.
- Elsewhere in the repo: `AsymptoticStatistics.ForMathlib.PiGaussian` (`pi_gaussianReal_eq_withDensity`) for the joint normal density, and `MultipleTesting.ForMathlib.ChiSquared` (`chiSquared`, `map_sum_sq_eq_chiSquared`, moments) for the `S²` law and the `residualScaleConst` moment ratio.

## Notes on specific targets

- **`Canonical`**: the model is `canonicalNormal` on `Fin (s+m) → ℝ` with the mean supported on the first `s` coordinates. `canonicalStat_hasSufficientKernel` and `canonicalStat_isCompleteStat` are the exponential-family route: write the joint density via `pi_gaussianReal_eq_withDensity`, recognise the `(s+1)`-parameter canonical family with natural statistic `(Y₁,…,Y_s, Σ_{j>s} Y_j²)`, then apply the imported completeness and factorization results. Thm 4.3(a) (`isUMVU_coord`, `isUMVU_linear_combination`, `isUMVU_residual_variance`) then follows from Lehmann–Scheffé. `S²/(n−s)` unbiasedness for `σ²` uses the χ² mean.
- **`LeastSquares`**: `inner_lse_eq_inner_starProjection` is self-adjointness of the orthogonal projection (`Submodule.starProjection` is `IsStarProjection`); for `γ ∈ W`, `⟪γ, lse W y⟫ = ⟪γ, y⟫`. The UMVU statements reduce to the canonical case after an orthonormal change of basis adapted to `W` — `stdGaussian_eq_map_pi_orthonormalBasis` is the intended transport. `Module.finrank ℝ W` is the `s`.
- **`Equivariant`**: equivariance is stated as explicit functional equations on competitors (deliberately lightweight — no `MulAction` framework here). Clause (c) uses the location-**scale** group, and the multiplier is `residualScaleConst = E[V^r]/E[V^{2r}]` for `V ∼ χ²_m` — the classical `r = 1` display is `S²/(m+2)`, and `residualScaleConst_one` should reproduce it from χ² moments.
- **`GaussMarkov`**: moments-only, no Gaussianity. The unbiasedness constraint `∀ ξ ∈ W, ⟪c, ξ⟫ = ⟪γ, ξ⟫` says `c − P_W γ ⊥ W`; then `var⟪c, ·⟫ = σ²‖c‖²` splits orthogonally as `σ²(‖P_W γ‖² + ‖c − P_W γ‖²) ≥ σ²‖P_W γ‖²`. `blue_lse` is the equality case, giving `c = P_W γ` as vectors. This should be short and purely geometric.
- **`RandomDesign`**: `θ̂ = (A Aᵀ)⁻¹ A y`; full row rank makes `designMean` injective and `A Aᵀ` invertible (Mathlib's matrix inverse is total, junk `0` when singular — the rank hypothesis is what excludes that). (a) is `isUMVU_linear_functional_of_mean` instantiated; (b) is the covariance computation `σ²(A Aᵀ)⁻¹`.

## Report

Final `lake build` status per module, per-file sorry counts, both `#print axioms` outputs, whether the sanctioned deferral was closed or left, and any statement you believe is false (with the counterexample).
