# Close the 3 sorries in MEstimator/Deviation.lean (Wainwright §9.2 — Lemma 9.14 + Prop 9.13)

You are a Lean 4 / Mathlib proof engineer on the `StatLean` project (read the repo `CLAUDE.md` first).
Pin: `leanprover/lean4:v4.29.1`. You are on the cluster — run `lake build <target>` directly to iterate
(Mathlib is cached; only project files recompile).

## Scope (hard constraints)
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/Deviation.lean`. Do NOT touch `Defs.lean`,
  `Bound.lean`, `DualBound.lean`, the umbrella, `lakefile.lean`, `lean-toolchain`, or `lake-manifest.json`.
- Verify with: `lake build StatLean.HighDimensionalStatistics.MEstimator.Deviation`. Goal: **0 sorries**,
  no errors. Keep all existing `-- USER-INPUT:` tags and docstrings. Keep lines ≤ 100 characters.
- If a genuine gap resists, lift it to a `private` top-level lemma in this file with a clear name and a
  single `sorry`, and a `-- TODO(me):` note — do not bury `sorry` inside a `have`.
- After green, run `#print axioms reg_deviation_lower` etc. — expect only `propext, Classical.choice,
  Quot.sound`. Then commit (the wrapper auto-commits, but a clean commit message helps).

## The three theorems (statements already in the file; do not change signatures)
Notation: `dr : DecomposableReg E` bundles `M ≤ Mbar`, seminorms `Φ Φstar`, and fields
`holder : ⟪u,v⟫_ℝ ≤ Φ u * Φstar v`, `tight`, `decomp : ∀ α∈M, ∀ β∈Mbarᗮ, Φ(α+β)=Φ α+Φ β`.
Projections are `Submodule.starProjection` (E-valued). Write `Δ_{M̄ᗮ} := (dr.Mbar)ᗮ.starProjection Δ`,
`Δ_{M̄} := dr.Mbar.starProjection Δ`, `θ*_M := dr.M.starProjection θstar`,
`θ*_{Mᗮ} := (dr.M)ᗮ.starProjection θstar`.

### 1. `reg_deviation_lower` (eq 9.32) — pure geometry, no convexity
`Φ(θ*+Δ) − Φ(θ*) ≥ Φ(Δ_{M̄ᗮ}) − Φ(Δ_{M̄}) − 2·Φ(θ*_{Mᗮ})`.
Proof: set `a := θ*_M`, `a' := θ*_{Mᗮ}`, `b := Δ_{M̄}`, `b' := Δ_{M̄ᗮ}`. Then:
- `θ* = a + a'` and `Δ = b + b'` via `starProjection_add_starProjection_orthogonal` (i.e.
  `K.starProjection x + Kᗮ.starProjection x = x`; you may need `.symm`).
- `a ∈ M` and `b' ∈ Mbarᗮ`: the projection lands in its subspace (find the lemma —
  `apply?`/`exact?`; it is around `Submodule.starProjection` in `…/Projection/Basic.lean`, the value
  `U.starProjection x ∈ U`).
- `Φ(θ*+Δ) ≥ Φ(a+b') − Φ(a'+b)` by the reverse triangle inequality (from `map_add_le_add` applied to
  `(a+b') = (θ*+Δ) + (-(a'+b))` after rewriting `θ*+Δ = (a+b') + (a'+b)`; or use a `Seminorm` sub lemma).
- `Φ(a'+b) ≤ Φ(a') + Φ(b)` (`map_add_le_add`).
- `Φ(a+b') = Φ(a) + Φ(b')` by `dr.decomp a ha b' hb'`.
- `Φ(θ*) = Φ(a+a') ≤ Φ(a)+Φ(a')` (`map_add_le_add`).
- Combine with `linarith`/`nlinarith`. (Seminorm API: `map_add_le_add dr.Φ x y`, `map_neg_eq_map`,
  `apply_nonneg dr.Φ`.)

### 2. `cost_deviation_lower` (eq 9.33) — convexity + Hölder + good event
`L(θ*+Δ) − L(θ*) ≥ −(λ/2)·(Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄}))`.
Proof:
- Convexity gradient inequality (already in project): `open StatLean.Optimization`; use
  `inner_gradient_le_sub_of_convexOn hL hdiff θstar (θstar+Δ)`, giving
  `L θstar + ⟪gradient L θstar, (θstar+Δ)−θstar⟫_ℝ ≤ L (θstar+Δ)`. Simplify `(θstar+Δ)−θstar = Δ`
  (`add_sub_cancel_left`), so `L(θ*+Δ) − L(θ*) ≥ ⟪g, Δ⟫_ℝ` where `g := gradient L θstar`.
- `|⟪g,Δ⟫_ℝ| ≤ Φ(Δ)·Φ*(g)`: note `⟪g,Δ⟫_ℝ = ⟪Δ,g⟫_ℝ` (`real_inner_comm`). `dr.holder Δ g` gives
  `⟪Δ,g⟫ ≤ Φ(Δ)Φ*(g)`; `dr.holder (-Δ) g` with `map_neg_eq_map` and `inner_neg_left` gives
  `−⟪Δ,g⟫ ≤ Φ(Δ)Φ*(g)`. Hence `⟪g,Δ⟫ ≥ −Φ(Δ)Φ*(g)`.
- Good event `hG : GoodEvent dr.Φstar g lam` is `Φ*(g) ≤ lam/2` (unfold `GoodEvent`). With
  `apply_nonneg dr.Φ Δ ≥ 0`, get `−Φ(Δ)Φ*(g) ≥ −Φ(Δ)(lam/2)`, and `λ ≥ 0` follows from
  `apply_nonneg dr.Φstar g` + `hG`.
- `Φ(Δ) ≤ Φ(Δ_{M̄ᗮ}) + Φ(Δ_{M̄})`: rewrite `Δ = Δ_{M̄} + Δ_{M̄ᗮ}` (starProjection sum) then
  `map_add_le_add`. Combine all with `nlinarith`/`linarith` (you may need
  `mul_le_mul_of_nonneg_left`).

### 3. `error_mem_cone` (Prop 9.13) — combine 1 + 2 + optimality
Goal `θhat − θstar ∈ errorCone dr θstar`, i.e. (unfold `errorCone`, `Set.mem_setOf_eq`)
`Φ(Δ̂_{M̄ᗮ}) ≤ 3·Φ(Δ̂_{M̄}) + 4·Φ(θ*_{Mᗮ})` with `Δ̂ := θhat − θstar`.
Proof:
- Let `Δ := θhat − θstar`. Note `θstar + Δ = θhat` (`add_sub_cancel`).
- Optimality `hopt θstar`: `L θhat + lam*Φ θhat ≤ L θstar + lam*Φ θstar`, so
  `(L θhat − L θstar) + lam*(Φ θhat − Φ θstar) ≤ 0`. Rewrite `θhat = θstar+Δ` to get
  `(L(θstar+Δ) − L θstar) + lam*(Φ(θstar+Δ) − Φ θstar) ≤ 0`  (this is `ℱ(Δ) ≤ 0`).
- Apply `reg_deviation_lower dr θstar Δ` and `cost_deviation_lower dr L hL hdiff θstar Δ lam hG`.
- Linear-combine: `0 ≥ ℱ(Δ) ≥ (lam/2)·Φ(Δ̂_{M̄ᗮ}) − (3·lam/2)·Φ(Δ̂_{M̄}) − 2·lam·Φ(θ*_{Mᗮ})`.
  With `hlam : 0 < lam`, divide through (use `nlinarith [hlam, ...]` or
  `le_div_iff`/`mul_le_mul_left`) to conclude `Φ(Δ̂_{M̄ᗮ}) ≤ 3Φ(Δ̂_{M̄}) + 4Φ(θ*_{Mᗮ})`.

## Tips
- `simp only [GoodEvent] at hG` to expose `Φ*(g) ≤ lam/2`.
- For `errorCone`, `show dr.Φ (...) ≤ 3*... + 4*...` after `rw [errorCone, Set.mem_setOf_eq]` (or
  `simp only [errorCone, Set.mem_setOf_eq]`).
- Real inner product over `E`: `⟪x,y⟫_ℝ` needs `open scoped InnerProductSpace` (already open in file).
- Prefer `nlinarith`/`linarith` with explicit hint terms for the final combination.
Report the final `lake build` status and `#print axioms` for the three results.
