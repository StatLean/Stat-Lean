Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §9, §10. Use the search tools.
Never `lake update`. You are ALREADY inside an srun allocation — build with plain `lake build`.

# CONTEXT (do NOT modify; READ them)
`ForMathlib/VecNorms.lean`: `l1Norm`, `linfNorm`, `restrict S`, Hölder
  `abs_inner_le_l1Norm_mul_linfNorm` (`|⟨x,y⟩| ≤ ‖x‖₁‖y‖∞`), and
  `l1Norm_restrict_le_sqrt_card_mul_norm` (`‖x|_S‖₁ ≤ √|S|·‖x‖₂`), `l1Norm_restrict_eq_sum`.
`LinearModel/Defs.lean`: `designMap X : E^d →ₗ E^n`.
`Lasso/Defs.lean`: `reCone S α`, `RestrictedEigenvalue X S κ α`, `lassoObjective X Y lam`,
  `IsLassoEstimator X Y lam βhat` (= `∀ β, lassoObjective … βhat ≤ lassoObjective … β`).

# TASK
Create `StatLean/HighDimensionalStatistics/Lasso/DeterministicRate.lean`
(namespace `StatLean.HighDimensionalStatistics`) proving Lu *Big Data Analysis* §8 **Rate of Lasso**
(`thm:re`) — fully DETERMINISTIC (no probability):

  theorem `lasso_l2_rate` : let `S` = support of `βstar` with `|S| = s`, `Y = designMap X βstar + ε`,
  `βhat` an `IsLassoEstimator X Y lam`, `RestrictedEigenvalue X S κ 3` (κ > 0), and the tuning
  condition `lam ≥ (2/n)·linfNorm (Xᵀ ε)` (i.e. `(2/n)‖Xᵀε‖∞`). Then
  `‖βhat − βstar‖ ≤ (3/κ)·√s·lam`.

(`Xᵀε` as a vector in `E^d`: `designMap Xᵀ ε` or `(toEuclideanLin Xᵀ) ε`; equivalently the adjoint
`(designMap X).adjoint ε` — use whichever makes `⟨ε, designMap X Δ⟩ = ⟨Xᵀε, Δ⟩` clean.)

# PROOF (standard Lasso basic-inequality argument, Lu §8)
Let `Δ = βhat − βstar`. From `IsLassoEstimator` at `β = βstar` (basic inequality), with `Y = Xβstar+ε`:
  `(1/2n)‖X Δ‖² ≤ (1/n)⟨ε, X Δ⟩ + lam(‖βstar‖₁ − ‖βhat‖₁)`.
Bound the noise term by Hölder + the tuning condition:
  `(1/n)⟨ε,XΔ⟩ = (1/n)⟨Xᵀε,Δ⟩ ≤ (1/n)‖Xᵀε‖∞‖Δ‖₁ ≤ (lam/2)‖Δ‖₁`.
Bound the ℓ¹ term by the support decomposition (`‖βstar‖₁−‖βhat‖₁ ≤ ‖Δ_S‖₁ − ‖Δ_{Sᶜ}‖₁`, since
`βstar` is supported on `S`; triangle ineq on each coordinate). Combine ⇒
  `0 ≤ (1/2n)‖XΔ‖² ≤ (lam/2)(‖Δ_S‖₁+‖Δ_{Sᶜ}‖₁) + lam(‖Δ_S‖₁−‖Δ_{Sᶜ}‖₁)`
  ⇒ `‖Δ_{Sᶜ}‖₁ ≤ 3‖Δ_S‖₁`, i.e. **Δ ∈ reCone S 3**. Now apply `RestrictedEigenvalue`:
  `κ‖Δ‖² ≤ (1/n)‖XΔ‖²`. Also from the basic inequality `(1/2n)‖XΔ‖² ≤ (3λ/2)‖Δ_S‖₁` and
  `‖Δ_S‖₁ ≤ √s‖Δ‖₂`. Chain: `κ‖Δ‖² ≤ (1/n)‖XΔ‖² ≤ 3λ‖Δ_S‖₁ ≤ 3λ√s‖Δ‖` ⇒ `‖Δ‖ ≤ (3/κ)√s λ`.

ZERO sorry. Hypotheses (`κ>0`, RE, tuning `lam ≥ (2/n)‖Xᵀε‖∞`, `Y=Xβ*+ε`, `S = support βstar`,
`IsLassoEstimator`) are `-- USER-INPUT: …; Lu-BDA §8 (thm:re)`. `n > 0` where needed is USER-INPUT.

# TOUCH-SET: ONLY `StatLean/HighDimensionalStatistics/Lasso/DeterministicRate.lean`.
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.DeterministicRate
# DONE = build exits 0; ZERO sorries; §2 tags; commit
(`hds(lasso): deterministic ℓ² rate ‖β̂−β*‖ ≤ 3√s·λ/κ (Lu-BDA §8 thm:re)`). Report build + sorry
status. If a sub-step needs a named helper lemma (e.g. the support decomposition), prove it in-file.
Independently re-verified; a vacuous/weakened bound is rejected.
