# Close the 6 sorries in MEstimator/GLMCorollaries.lean (Wainwright Cor 9.26, 9.27)

Lean 4 / Mathlib on `StatLean` (read `CLAUDE.md`). Pin `v4.29.1`. ON the cluster. This is the FINAL file
of the milestone — the GLM Lasso rates.

## CRITICAL discipline
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.GLMCorollaries`,
  read output directly. **NEVER** background a build, `until pgrep`/`sleep`/poll loops, nested `srun`, or
  leave `trace_state`/`#print`/`set_option` in the file. 0 errors + 0 sorries ⇒ STOP.
- **Commit-bank as you go**: when a lemma compiles, the auto-commit captures it; if one resists, lift its
  hard sub-step to a `private lemma … sorry` with `-- TODO(me):` and move on (don't lose the rest).

## Available API (all proven)
- `l1DecomposableReg S : DecomposableReg (EuclideanSpace ℝ (Fin d))` with `.M = .Mbar = suppSubmodule S`,
  `.Φ = l1Seminorm d`, `.Φstar = linfSeminorm d`. Coercions: `l1Seminorm d u = l1Norm u`,
  `linfSeminorm d v = linfNorm v` (by `rfl`/`simp [l1Seminorm, linfSeminorm]`).
- Deterministic (in `Bound.lean`/`DualBound.lean`): `cor_l2_bound_of_mem`, `cor_reg_bound_of_mem`,
  `mestimator_dual_bound` — all take `(dr L hL hdiff θstar θhat lam κ R τSq …) (hmem : θstar ∈ dr.M)`.
- `good_event_highProb M C hC hn hd δ hδ_pos hδ_lt hB hCpos lam hlam :
   ENNReal.ofReal (1 − 2 exp(−2nδ²)) ≤ μ {ω | linfNorm (scoreVec M ω) ≤ lam/2}`.
- `score_coord_isSubGaussian`, `scoreVec`, `glmCost`, `linPred`, `suppSubmodule`, `subspaceLip`,
  `RSC`, `dualCurvature`, `GoodEvent` (all in scope). `l1Norm_restrict_le_sqrt_card_mul_norm` (VecNorms).
- Convexity: `Seminorm.convexOn`, `ConvexOn.comp_linearMap`/`.comp_affineMap`, `ConvexOn.add`,
  `ConvexOn.smul`, `convexOn_of_deriv2_nonneg`/from monotone `ψ'`. `gradient` calculus:
  `gradient_const_smul`, `Gradient`/`fderiv` lemmas, `gradient` of a `Finset.sum`.

## The 6 lemmas

### `glmCost_convexOn` — `ConvexOn ℝ univ (glmCost M ω)`
`glmCost M ω θ = (1/n)·∑ᵢ (M.ψ (linPred M.X θ i) − M.y i ω · linPred M.X θ i)`. `linPred M.X · i` is a
**linear map** `θ ↦ ∑ⱼ Xᵢⱼ θⱼ` (build it as `(LinearMap …)` or note `linPred = ⟪row i, ·⟫`). `M.ψ` is convex
(`ConvexOn ℝ univ M.ψ` from `M.hψ''_nonneg` via `convexOn_of_deriv2_nonneg` / monotone `M.ψ'` — use
`M.hψ'`, `M.hψ''`). Then each summand `ψ∘linPredᵢ − yᵢ·linPredᵢ` is convex (`ConvexOn.comp_linearMap` for
the `ψ∘` part; subtract the linear `yᵢ·linPredᵢ` which is affine, so still convex via `ConvexOn.add` with
the negation as a `LinearMap`). `Finset.sum` of convex (`convexOn_sum`/induction) then `ConvexOn.smul (by positivity)`.

### `glmCost_differentiable` — `Differentiable ℝ (glmCost M ω)`
Sum/products of differentiable: `linPred` is linear (`Differentiable`), `M.ψ` differentiable
(`(M.hψ' _).differentiableAt`), so `M.ψ ∘ linPredᵢ` differentiable (`.comp`); the product `yᵢ·linPredᵢ`
differentiable; `Finset.sum` + `const_smul`.

### `glmCost_gradient_eq_scoreVec` — `gradient (glmCost M ω) M.θstar = scoreVec M ω`  (HARDEST)
`gradient` is `ℝ`-linear and commutes with finite sums and `const_smul`. For each `i`:
`gradient (fun θ => M.ψ (linPred M.X θ i)) θ* = M.ψ' (ηᵢ) • (gradient (fun θ => linPred M.X θ i) θ*)`
(chain rule: `linPred M.X · i = ⟪rowᵢ, ·⟫`, whose gradient is `rowᵢ`; combine with `HasDerivAt`/`HasGradientAt`
of `ψ`). `gradient (fun θ => M.y i ω · linPred M.X θ i) θ* = M.y i ω • rowᵢ`. Sum + `(1/n)•`:
`gradient (glmCost M ω) θ* = (1/n)∑ᵢ (M.ψ' ηᵢ − M.y i ω) • rowᵢ`, whose `j`-th coordinate is
`(1/n)∑ᵢ (M.ψ' ηᵢ − M.y i ω)·Xᵢⱼ = scoreCoord M j ω = (scoreVec M ω).ofLp j`. Finish by `EuclideanSpace.ext`/
coordinate equality (`scoreVec_ofLp` from `GoodEvent.lean`). If the `gradient`-of-inner / chain-rule plumbing
resists, lift `glmCost_gradient_eq_scoreVec` itself to a named `sorry` (it is a standard calculus fact —
acceptable single debt) and proceed so the corollaries still assemble.

### `subspaceLip_l1_suppSubmodule` — `subspaceLip (l1Seminorm d) (suppSubmodule S) = √|S|`
`Ψ = sSup {l1Norm u/‖u‖ : u∈M(S), u≠0}`. **≤ √s:** for `u∈suppSubmodule S`, `u = restrict S u` (off-`S` coords 0),
so `l1Norm u = l1Norm (restrict S u) ≤ √|S|·‖u‖` (`l1Norm_restrict_le_sqrt_card_mul_norm`), giving
`l1Norm u/‖u‖ ≤ √s`; `Real.sSup_le`. **≥ √s (achiever):** take `u = ∑_{j∈S} eⱼ` (indicator of `S`): `u∈M(S)`,
`l1Norm u = |S|`, `‖u‖ = √|S|`, ratio `= √|S|`; so `√s ≤ sSup` via `le_csSup` (BddAbove from the ≤ bound).
(If `S = ∅`: both sides `0`.)

### `glm_lasso_l2_l1_rate` (Cor 9.26) — the good-event split
Set `dr := l1DecomposableReg S`. Key bridges: `Ψ²(dr.Mbar) = (√s)² = s` (`subspaceLip_l1_suppSubmodule` +
`Real.sq_sqrt`); `dr.Φstar (gradient (glmCost M ω) M.θstar) = linfNorm (scoreVec M ω)`
(`glmCost_gradient_eq_scoreVec` + `linfSeminorm` coercion); `dr.Φ = l1Norm` (coercion).
- `G := {ω | linfNorm (scoreVec M ω) ≤ lam/2}` — exactly `{ω | GoodEvent dr.Φstar (gradient (glmCost M ω) M.θstar) lam}`.
- Show `G ⊆ {ω | ℓ₂ bound ∧ ℓ₁ bound}`: `intro ω hω`. On the good event,
  `cor_l2_bound_of_mem dr (glmCost M ω) (glmCost_convexOn M ω) (glmCost_differentiable M ω) M.θstar (θhat ω)
   lam κ R τSq hlam? hκ hR (hRSC ω) (hopt ω) hω' (by rw[…]; exact hslack) (by rw[…]; exact hεR) hsparse`
  gives `‖θhat ω − M.θstar‖² ≤ 144(lam²/κ²)·(subspaceLip …)² = 144(lam²/κ²)·s`; similarly `cor_reg_bound_of_mem`
  gives the `ℓ₁` bound `≤ 48(lam/κ)·s`. (Rewrite `(subspaceLip …)² → s` and `dr.Φ → l1Norm` as needed.)
  Note `lam > 0` from `hlam` (`B,C,δ>0`).
- Conclude: `good_event_highProb M C hC hn hd δ hδ_pos hδ_lt hB hCpos lam (le_of_eq hlam.symm)` gives
  `ofReal(1−2e^{−2nδ²}) ≤ μ G ≤ μ {ℓ₂∧ℓ₁}` (`measure_mono` on `G ⊆ …`).

### `glm_lasso_linf_rate` (Cor 9.27) — same split with `mestimator_dual_bound`
`G ⊆ {ω | linfNorm (θhat ω − M.θstar) ≤ 3lam/κ}`: on `G`, `mestimator_dual_bound dr (glmCost M ω) … M.θstar
(θhat ω) lam κ τ R … hsparse (hcurv ω) (hopt ω) hω' (by …; exact hslack) (hRloc ω)` gives
`dr.Φstar (θhat ω − M.θstar) = linfNorm (θhat ω − M.θstar) ≤ 3lam/κ`. Then `good_event_highProb` + `measure_mono`.

Report the final `lake build` line (0 sorries ideally; note any single lifted `glmCost_gradient_eq_scoreVec` debt).
