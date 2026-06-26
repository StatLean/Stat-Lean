# Regularized M-estimators (Wainwright Ch. 9) — outline

## Dependency tree (one-way: ForMathlib → concept → assembly → GLM)

```
Optimization.{Convex/Subgradient, ForMathlib/FirstOrderConvex}     (cross-area, below HDS)
ConcentrationInequalities.SubGaussian.{Defs,Hoeffding,TailBounds}  (cross-area)
HighDimensionalStatistics/ForMathlib/{VecNorms, PsiTaylor}
        │
   MEstimator/Defs ───────────────┐   MEstimator/GLMDefs
        │                         │        │
   Deviation (Prop 9.13)          │   L1Decomposable (ℓ₁/ℓ∞ instance)
        │                         │        │
   SubspaceLip                    │   ScoreSubGaussian  (← PsiTaylor, GLMDefs, ConcIneq)
        │                         │        │
   Bound (Thm 9.19, Cor 9.20)     │   GoodEvent         (← ScoreSubGaussian, VecNorms)
   DualBound (Lemma 9.25, Thm 9.24)        │
        └──────────────┬──────────────────┘
                 GLMCorollaries (Cor 9.26, Cor 9.27)
```

## The two deterministic theorems (general `M ⊆ M̄`, inner-product space `E`)

* **Thm 9.19** (`Bound`): on the good event `𝔾(λ) = {Φ*(∇Lₙ(θ*)) ≤ λ/2}`, under RSC (A1) +
  decomposability (A2), `‖θ̂−θ*‖² ≤ εₙ²`. Proof = Lemma 9.21 (star-shaped cone + the function
  `ℱ(Δ) = ⟨∇Lₙ(θ*),Δ⟩ + λ(Φ(θ*+Δ)−Φ(θ*))` is positive off a ball) + the RSC quadratic-form chain
  (`ℱ(Δ) ≥ (κ/4)‖Δ‖² − (3λ/2)Ψ‖Δ‖ − …`). `Cor 9.20` = the `θ*∈M` specialization (`Φ(θ*_{Mᗮ})=0`).
* **Thm 9.24** (`DualBound`): under the Φ*-curvature condition (Def 9.22), `Φ*(θ̂−θ*) ≤ 3λ/κ`. Proof =
  the hand-built stationarity `−∇Lₙ(θ̂)/λ ∈ ∂Φ(θ̂)` (⇒ `Φ*(∇Lₙ(θ̂)−∇Lₙ(θ*)) ≤ 3λ/2`) + curvature +
  Lemma 9.25 (`Φ(Δ) ≤ 16Ψ²Φ*(Δ)`).

## Design choices (see CLAUDE.md + the plan)
* Orthogonal projections via `Submodule.starProjection` (E-valued). `M ≤ M̄ ⟹ M̄ᗮ ≤ Mᗮ`.
* Regularizer `Φ : Seminorm ℝ E`; dual norm `Φ* : Seminorm ℝ E` carried as a **bundled parameter** with
  `holder` (`⟨u,v⟩ ≤ Φu·Φ*v`) + `tight` (variational) — Mathlib has no dual-norm-of-a-seminorm construction.
* `DecomposableReg E` structure bundles `M ≤ M̄`, `Φ`, `Φ*`, `holder`, `tight`, `decomp` (Def 9.9).
* GLM: fixed design `X : Matrix (Fin n) (Fin d) ℝ`, responses `y_i : Ω → ℝ` independent; the exponential
  family encoded by the **constitutive** MGF identity `hmgf i s = exp(ψ(ηᵢ+s)−ψ(ηᵢ))`. The score is a
  function of `y_i` only (no conditional-expectation machinery).

## GLM instantiation (`M = M̄ = M(S) = suppSubmodule S`)
`l1DecomposableReg S`: `Φ = ℓ₁`, `Φ* = ℓ∞`, decomposability from `M(S)ᗮ = M(Sᶜ)`. `Ψ(M(S)) = √s`
(`subspaceLip_l1_suppSubmodule`, via `l1Norm_restrict_le_sqrt_card_mul_norm` + the indicator achiever).
Cor 9.26/9.27 = the good-event/bad-event split (mirrors `Lasso/RandomNoise.lean` `lasso_random_rate`):
`{ω | bound}` ⊇ `{ω | ‖scoreVec‖∞ ≤ λ/2}`, and `good_event_highProb` lower-bounds the latter's measure.

## Out of scope (book §9.7–9.8, beyond Cor 9.27)
Matrix/nuclear-norm estimation, the RSC-verification proofs (Thm 9.36), exercises.

## Reuse ledger (did not rebuild)
`Optimization`: subgradient API, `inner_gradient_le_sub_of_convexOn`. `ConcentrationInequalities.SubGaussian`:
`HasSubgaussianMGF(.sum_of_iIndepFun)`, `IsSubGaussian.measure_abs_sub_integral_lt_le`. `ForMathlib/VecNorms`:
`l1Norm`, `linfNorm`, `restrict`, `abs_inner_le_l1Norm_mul_linfNorm`, `l1Norm_restrict_le_sqrt_card_mul_norm`.
`Lasso/RandomNoise`: structural template for the GLM concentration files.
