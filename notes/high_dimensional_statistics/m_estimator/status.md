# Regularized M-estimators (Wainwright Ch. 9) — status

Integration branch: `hds/m-estimator` (off `main`). **COMPLETE — all units merged, 0-sorry.**
Source: Wainwright, *High-Dimensional Statistics*, ch. 9 (`ref/Wainwright/Wainwright_M-estimator.pdf`),
pp. 259–289. Decomposable regularizers + restricted strong convexity ⇒ estimation-error bounds, with
GLM Lasso `ℓ₂`/`ℓ₁`/`ℓ∞` rates as the payoff. Each file stub-gated then proof-closed on the cluster
(or laptop), verified independently (fresh build, 0-sorry, diff ⊆ touch-set, signature vs stub, no
hypothesis laundering) before `--no-ff` merge. Full-library build green; `#print axioms` clean.

## Theorem / unit ledger — ALL REAL (0-sorry)

| Layer | File | Key decls | Status |
|---|---|---|---|
| ForMathlib | `ForMathlib/PsiTaylor` | `psi_taylor_upper` (ψ-quadratic upper bound, `\|ψ''\|≤B²`) | ✅ real |
| concept | `MEstimator/Defs` | `DecomposableReg`, `RSC`, `subspaceLip`, `errorCone`, `epsilonSq`, `dualCurvature`, `GoodEvent` | ✅ real |
| concept | `MEstimator/GLMDefs` | `GLMExpFamily` (constitutive `hmgf`), `scoreVec`/`scoreCoord`, `glmCost`, `IsColumnNormalized` | ✅ real |
| concept | `MEstimator/L1Decomposable` | `l1DecomposableReg` instance (ℓ₁/ℓ∞ dual pair, `suppSubmodule`, decomp) | ✅ real |
| assembly | `MEstimator/Deviation` | `reg_deviation_lower` (9.32), `cost_deviation_lower` (9.33), `error_mem_cone` (**Prop 9.13**) | ✅ real |
| assembly | `MEstimator/SubspaceLip` | `seminorm_le_const_mul_norm`, `subspaceLip_le` (Φ ≤ C‖·‖ on a subspace) | ✅ real |
| assembly | `MEstimator/Bound` | `norm_error_le_of_pos_on_sphere` (**Lemma 9.21**), `mestimator_l2_bound`/`_reg_bound` (**Thm 9.19**), `cor_l2_bound_of_mem`/`cor_reg_bound_of_mem` (**Cor 9.20**) | ✅ real |
| assembly | `MEstimator/DualBound` | `exists_stationary_subgradient` (hand-built), `reg_le_dual_of_mem` (**Lemma 9.25**), `mestimator_dual_bound` (**Thm 9.24**) | ✅ real |
| GLM | `MEstimator/ScoreSubGaussian` | `score_term_hasSubgaussianMGF`, `score_coord_isSubGaussian` (proxy `B²C²/n`) | ✅ real |
| GLM | `MEstimator/GoodEvent` | `score_linfNorm_tail` (union bound), `good_event_highProb` | ✅ real |
| GLM | `MEstimator/GLMCorollaries` | `subspaceLip_l1_suppSubmodule` (Ψ=√s), `glmCost_convexOn`/`_differentiable`/`_gradient_eq_scoreVec`, `glm_lasso_l2_l1_rate` (**Cor 9.26**), `glm_lasso_linf_rate` (**Cor 9.27**) | ✅ real |

Main theorems:
* **Thm 9.19(b)** `mestimator_l2_bound` — general RSC + decomposability ⇒ `‖θ̂−θ*‖² ≤ εₙ²`.
* **Cor 9.20** `cor_l2_bound_of_mem` / `cor_reg_bound_of_mem` — `θ*∈M` ⇒ `‖Δ̂‖² ≤ 144(λ/κ)²Ψ²`, `Φ(Δ̂) ≤ 48(λ/κ)Ψ²`.
* **Thm 9.24** `mestimator_dual_bound` — Φ*-curvature ⇒ `Φ*(θ̂−θ*) ≤ 3λ/κ`.
* **Cor 9.26** `glm_lasso_l2_l1_rate` — GLM Lasso `‖θ̂−θ*‖₂² ≤ 144 s λ²/κ²`, `‖·‖₁ ≤ 48 s λ/κ`, w.p. `≥1−2e^{−2nδ²}`.
* **Cor 9.27** `glm_lasso_linf_rate` — GLM Lasso `‖θ̂−θ*‖∞ ≤ 3λ/κ`, same probability.

## Honesty: what is DERIVED (not laundered through hypotheses)
* **Prop 9.13** cone membership — derived from the deviation inequalities (9.32/9.33), not assumed.
* **Thm 9.24 stationarity** `−∇Lₙ(θ̂)/λ ∈ ∂Φ(θ̂)` — **hand-built** (`exists_stationary_subgradient`) via a
  directional-derivative `t→0⁺` argument (`HasDerivAt` + `hasDerivAt_iff_tendsto_slope` +
  `ge_of_tendsto` on `𝓝[>] 0`); Mathlib has no subdifferential sum-rule. No fallback sorry.
* **GLM score sub-Gaussianity** — derived from the constitutive MGF `hmgf` + `psi_taylor_upper` +
  `HasSubgaussianMGF.sum_of_iIndepFun` + (G1), not assumed.
* **Good event high probability** — derived from the coordinate sub-Gaussian tail + union bound.
* **Gradient identity** `gradient (glmCost M ω) θ* = scoreVec M ω` — full `HasFDerivAt` chain over the
  summands (`glmSummand_hasFDerivAt`, `InnerProductSpace.toDual`), coordinatewise to `scoreCoord`. No fallback sorry.

Genuine USER-INPUT (book inputs, tagged): `Lₙ` convex; the `Φ`/`Φ*` dual-pair data; decomposability (A2);
the RSC condition (A1, and the GLM RSC 9.62 — the book itself defers it to Thm 9.36); the GLM `ℓ∞`-curvature
(9.64); `θ̂` optimal; (G1) column-normalization; (G2) the GLM exp-family with `0≤ψ''≤B²`.

## Book-vs-Lean constants (final, provable)
| Result | Book | Lean (proved) | Note |
|---|---|---|---|
| Thm 9.19 `εₙ²` leading (θ*∈M) | `9(λ/κ)²Ψ²` | `144(λ/κ)²Ψ²` | `√144 = 12`; provable sphere-positivity constant (κ/4 split) |
| Cor 9.20 `ℓ₂` | `(9/4)sλ²/κ²` | `144 s λ²/κ²` | same `s·λ²/κ²` rate |
| Cor 9.20 `ℓ₁` | `(6/κ)sλ` | `48 s λ/κ` | same `s·λ/κ` rate |
| Thm 9.19 RSC slack | `τ² Ψ² ≤ κ/64` (implied) | `τ² Ψ² ≤ κ/128` | `c ≥ κ/4` margin needed for ℱ-positivity |
| Thm 9.24 slack | `τ Ψ² < κ/32` | `τ Ψ² < κ/32` | matches |
| Cor 9.26/9.27 `λ` | `4BC{√(log d/n)+δ}` | `4BC{√(log d/n)+δ}` | matches; `Cor 9.27` reuses the SAME λ (good-event prob needs `≥4BC`, not 2BC) |
| Good-event prob | `1 − 2e^{−2nδ²}` | `1 − 2e^{−2nδ²}` | matches (the `2/d ≤ 2` collapse) |

All deviations documented in the respective module docstrings (per CLAUDE.md §1).

## Axioms
`#print axioms` on `mestimator_l2_bound`, `mestimator_dual_bound`, `glm_lasso_l2_l1_rate`,
`glm_lasso_linf_rate`, `glmCost_gradient_eq_scoreVec` → `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`). Confirmed by the full-library build (`lake build OK`, 0 sorry).

## Parallelization outcome
Cluster fan-out via `lean-on-fasrc`, ≤2 concurrent, file-disjoint touch-sets, laptop scheduling. Notable
recoveries: ScoreSubGaussian (nested-loop **stall** at 28 min → salvaged 0-sorry work, then an NNReal
`⟨_,_⟩`-coercion gap fixed by a 2nd subagent via `refine`/`exact` + `NNReal.coe_sum`/`coe_injective`);
GoodEvent (transient **API drop** → recovered 2/3, last lemma via focused relaunch); GLMCorollaries
(cluster-claude **401 token expiry** → user refreshed token → relaunch; 401-turbulent run produced 299
lines 0-sorry but 4 latent build errors, laptop-fixed: β-reduce image-set goal, `not_mem`→`notMem`
renames, 2 redundant tactics). Lesson reinforced: **build salvaged worktrees before merging** (0 sorries ≠ compiles).
