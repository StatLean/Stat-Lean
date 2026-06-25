# Close the 3 sorries in MEstimator/DualBound.lean (Wainwright Thm 9.24, Lemma 9.25, stationarity)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. ON the cluster —
iterate with plain `lake build StatLean.HighDimensionalStatistics.MEstimator.DualBound`.

## Hard constraints
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/DualBound.lean`. Nothing else.
- Goal **0 sorries** if achievable. Keep signatures/tags/docstrings. Lines ≤ 100.
- The first lemma (`exists_stationary_subgradient`) is genuinely hard (Mathlib has NO subdifferential
  calculus). **Attempt the full proof.** If the directional-derivative limit step resists after honest
  effort, lift JUST that step to a `private lemma directional_deriv_bound … := … sorry` with a clear
  `-- TODO(me):` and build the rest of `exists_stationary_subgradient` on it (so only one named debt).
- After green: `#print axioms mestimator_dual_bound`.

## Available API
- `error_mem_cone …`, `reg_le_dual_of_mem` (this file, prove it), `subspaceLip_le`, `subspaceLip_nonneg`.
- `IsSubgradient (f : E→ℝ) (x g : E) : Prop := ∀ y, ⟪g, y - x⟫_ℝ ≤ f y - f x` (`open StatLean.Optimization`).
- `inner_gradient_le_sub_of_convexOn hL hdiff x y : f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y` — and read
  `StatLean/Optimization/ForMathlib/FirstOrderConvex.lean` for the `AffineMap.lineMap` + `HasDerivAt` +
  `ConvexOn.le_slope_of_hasDerivAt` pattern; you will mirror it for the composite objective.
- `dr.holder u v : ⟪u,v⟫_ℝ ≤ dr.Φ u * dr.Φstar v`; `dr.tight v c : (∀ u, dr.Φ u ≤ 1 → ⟪u,v⟫_ℝ ≤ c) → dr.Φstar v ≤ c`.
- Seminorm: `map_add_le_add`, `map_smul_eq_mul`, `map_neg_eq_map`, `apply_nonneg`. `GoodEvent dr.Φstar g lam = dr.Φstar g ≤ lam/2`.
- `real_inner_self_eq_norm_sq x : ⟪x,x⟫_ℝ = ‖x‖^2` (or `_norm_mul_norm`).

## Proofs

### 1. `exists_stationary_subgradient` — `∃ z, IsSubgradient (fun x => dr.Φ x) θhat z ∧ gradient L θhat + lam • z = 0`
Set `g := gradient L θhat`, `z := (-(1/lam)) • g`. Then `gradient L θhat + lam • z = g + lam•(-(1/lam)•g) = g - g = 0`
(`smul_smul`, `mul_inv_cancel₀ (ne_of_gt hlam)`, `module`/`abel`). Remains `IsSubgradient (fun x => dr.Φ x) θhat z`:
`intro y`. Goal `⟪z, y - θhat⟫_ℝ ≤ dr.Φ y - dr.Φ θhat`. With `z = -(1/lam)•g`, `inner_smul_left`,
this is `-(1/lam) * ⟪g, y-θhat⟫_ℝ ≤ dr.Φ y - dr.Φ θhat`, i.e. (×`lam>0`)
`⟪g, θhat - y⟫_ℝ ≤ lam * (dr.Φ y - dr.Φ θhat)`  (use `⟪g, θhat-y⟫ = -⟪g, y-θhat⟫`, `inner_sub_right`/`neg`).

Prove this last inequality (`key`). Let `w := y - θhat`.
- For `s ∈ (0,1]`: optimality `hopt (θhat + s•w)` gives
  `L θhat + lam*dr.Φ θhat ≤ L (θhat + s•w) + lam*dr.Φ (θhat + s•w)`.
- Convexity of `dr.Φ`: `θhat + s•w = (1-s)•θhat + s•y`, so `dr.Φ (θhat+s•w) ≤ (1-s)*dr.Φ θhat + s*dr.Φ y`
  (`dr.Φ.convexOn.2 (mem_univ _) (mem_univ _) (by linarith) hs.le (by ring)` after rewriting the point;
  or directly `map_add_le_add` + `map_smul_eq_mul`). Hence
  `lam*(dr.Φ (θhat+s•w) - dr.Φ θhat) ≤ lam*s*(dr.Φ y - dr.Φ θhat)`.
- Combine: `L (θhat+s•w) - L θhat ≥ -lam*s*(dr.Φ y - dr.Φ θhat)`, so the slope
  `(L (θhat+s•w) - L θhat)/s ≥ -lam*(dr.Φ y - dr.Φ θhat)` for `s ∈ (0,1]`.
- The slope tends to the directional derivative `⟪g, w⟫_ℝ` as `s → 0⁺`: build `HasDerivAt (fun s => L (θhat + s•w)) ⟪g,w⟫_ℝ 0`
  via `(hdiff θhat).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt of s ↦ θhat+s•w = lineMap θhat y at 0 with deriv w)`
  + `inner_gradient_left`. The slope `s ↦ (L(θhat+s•w)-L θhat)/s` is `slope (fun s => L(θhat+s•w)) 0 s`;
  its limit at `𝓝[>] 0` is the derivative (`HasDerivAt … |>.tendsto_slope` / `hasDerivAt_iff_tendsto_slope`).
  Then `ge_of_tendsto'` (the slope is `≥ -lam*(…)` eventually on `𝓝[>] 0`) gives `⟪g,w⟫_ℝ ≥ -lam*(dr.Φ y - dr.Φ θhat)`.
  ⟹ `⟪g, θhat - y⟫_ℝ = -⟪g, w⟫_ℝ ≤ lam*(dr.Φ y - dr.Φ θhat)`. □
  (This limit step is the hard part — mirror `FirstOrderConvex.lean`. If it resists, isolate it as the
  named `private lemma` debt described above.)

### 2. `reg_le_dual_of_mem` (Lemma 9.25): `θ*∈M`, `Δ∈ℂ` ⟹ `Φ(Δ) ≤ 16*Ψ²*Φ*(Δ)`
Set `Ψ := subspaceLip dr.Φ dr.Mbar`. `θ*∈M ⟹ (dr.M)ᗮ.starProjection θstar = 0` (find via `exact?`:
`v∈K → Kᗮ.starProjection v = 0`), so `Φ₀ = 0` and `Δ∈ℂ` gives `Φ(Δ_{M̄ᗮ}) ≤ 3Φ(Δ_{M̄})`.
- `Φ(Δ) ≤ 4*Φ(Δ_{M̄}) ≤ 4*Ψ*‖Δ‖` (triangle on `Δ=Δ_{M̄}+Δ_{M̄ᗮ}`, cone, `subspaceLip_le`, `norm_starProjection_apply_le`).
- `‖Δ‖^2 = ⟪Δ,Δ⟫_ℝ ≤ Φ(Δ)*Φ*(Δ) ≤ 4Ψ‖Δ‖*Φ*(Δ)` (`real_inner_self_eq_norm_sq`, `dr.holder Δ Δ`).
- `by_cases ‖Δ‖ = 0` (⟹ `Δ=0`, both sides 0 via `map_zero`); else `‖Δ‖>0`, divide: `‖Δ‖ ≤ 4Ψ*Φ*(Δ)`,
  then `Φ(Δ) ≤ 4Ψ‖Δ‖ ≤ 16Ψ²*Φ*(Δ)`. `nlinarith [subspaceLip_nonneg, apply_nonneg dr.Φstar Δ, norm_nonneg Δ]`.

### 3. `mestimator_dual_bound` (Thm 9.24): `Φ*(θ̂-θ*) ≤ 3λ/κ`
Set `Δ̂ := θhat-θstar`, `g0 := gradient L θstar`, `ĝ := gradient L θhat`, `Ψ := subspaceLip dr.Φ dr.Mbar`.
- `⟨z, hz, hstat⟩ := exists_stationary_subgradient dr L hL hdiff θhat lam hlam hopt`. So `ĝ = -lam•z` (from `hstat`, `eq_neg_of_add_eq_zero_left` + `smul`).
- `Φ*(z) ≤ 1`: `dr.tight z 1`; `intro u hu` (`dr.Φ u ≤ 1`); `hz (θhat+u)` gives `⟪z,u⟫_ℝ ≤ dr.Φ (θhat+u) - dr.Φ θhat ≤ dr.Φ u ≤ 1`
  (`map_add_le_add` ⟹ `dr.Φ (θhat+u) ≤ dr.Φ θhat + dr.Φ u`; `add_sub_cancel`/`simp`).
- `Φ*(ĝ - g0) ≤ 3*lam/2`: `ĝ - g0 = -(lam•z + g0)`; `map_neg_eq_map`, `map_add_le_add`, `map_smul_eq_mul` (`‖lam‖=lam`),
  `Φ*(z)≤1`, and `hG : dr.Φstar g0 ≤ lam/2`. `nlinarith`/`linarith`.
- Curvature: `hcurv Δ̂ hRloc` gives `dr.Φstar (gradient L (θstar+Δ̂) - gradient L θstar) ≥ κ*dr.Φstar Δ̂ - τ*dr.Φ Δ̂`;
  rewrite `θstar+Δ̂ = θhat` (`add_sub_cancel`) so LHS `= dr.Φstar (ĝ - g0) ≤ 3lam/2`. Thus `κ*Φ*(Δ̂) - τ*Φ(Δ̂) ≤ 3lam/2`.
- `Φ(Δ̂) ≤ 16Ψ²*Φ*(Δ̂)` via `reg_le_dual_of_mem dr θstar hmem Δ̂ (error_mem_cone …)`.
- Combine: `(κ - 16*τ*Ψ²)*Φ*(Δ̂) ≤ 3lam/2`. From `hτ : τ*Ψ² < κ/32`, `16*τ*Ψ² < κ/2`, so `κ - 16τΨ² > κ/2 > 0`.
  Conclude `Φ*(Δ̂) ≤ 3*lam/κ`: `nlinarith [hτ, hκ, hlam, subspaceLip_nonneg dr.Φ dr.Mbar, apply_nonneg dr.Φstar Δ̂, apply_nonneg dr.Φ Δ̂]`.

Report final `lake build` status + `#print axioms`; note any single lifted `private` sorry in step 1.
