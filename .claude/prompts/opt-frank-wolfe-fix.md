Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10.

# CONTEXT
`StatLean/Optimization/FrankWolfe.lean` BUILDS GREEN already, with one remaining `sorry`:
`frankWolfe_base` (the `t = 0` bound `f (x 0) - f xstar ≤ L * D`). The one-step recursion lemma
`frankWolfe_step` is fully PROVEN, and `frankWolfe_rate` is proven by induction modulo
`frankWolfe_base`.

`frankWolfe_base` is NOT cleanly provable for the CONSTRAINED minimizer (it would need a gradient
bound at `x 0`). The correct, standard fix: **the `O(1/t)` rate is meaningful for `t ≥ 1`**, and
the base case `t = 1` follows from `frankWolfe_step` at `t = 0` (where `η₀ = 2/(0+2) = 1`, giving
`Δ₁ ≤ (1-1)·Δ₀ + (L/2)·1²·D = (L/2)·D ≤ 2LD/3 = 2LD/(1+2)`), needing NO bound on `Δ₀`.

# TASK — edit `StatLean/Optimization/FrankWolfe.lean` so it builds with **0 sorry, 0 error**:
1. Add hypothesis `(ht : 1 ≤ t)` to `frankWolfe_rate` (just before `:` / the conclusion).
2. Re-do the induction to start at `t = 1` instead of `t = 0`:
   - Use `Nat.le_induction` (induction starting from a base ≥ 1) on `t` with `ht : 1 ≤ t`.
   - **Base `t = 1`:** apply `frankWolfe_step` at `t = 0` to get
     `Δ₁ ≤ (1 - η₀)Δ₀ + (L/2)η₀²D` with `η₀ = 2/2 = 1`, simplify to `Δ₁ ≤ (L/2)D`, then
     `(L/2)D ≤ 2LD/3` (since `D ≥ 0`, `L > 0`). Note `2LD/(1+2) = 2LD/3`.
   - **Step:** reuse the EXISTING inductive-step algebra (it already proves
     `Δ_{k+1} ≤ 2LD/(k+3)` from `Δ_k ≤ 2LD/(k+2)` via `frankWolfe_step k` and
     `(k+1)(k+3) ≤ (k+2)²`).
3. **Delete `frankWolfe_base`** (the sorry'd lemma) and its docstring once unused.
4. Update the module/theorem docstring to note: "stated for `t ≥ 1`; the `t = 0` case is the
   trivial initial optimality gap, excluded since the `O(1/t)` rate is meaningful for `t ≥ 1`"
   (CLAUDE.md §1 documented deviation).

`D ≥ 0` from `hdiam 0` + `sq_nonneg`. Keep all other hypotheses as-is; `hdiam : ∀ t, ‖y t - x t‖²
≤ D` is sufficient (the induction only ever uses `frankWolfe_step`, which uses `hdiam`).

# TOUCH-SET — modify ONLY `StatLean/Optimization/FrankWolfe.lean`. Never `lake update`.

# BUILD (inside the worktree, repeat until green)
  lake build StatLean.Optimization.FrankWolfe
Commit only a compiling, 0-sorry state.
