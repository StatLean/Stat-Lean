# Close the 3 sorries in MEstimator/SubspaceLip.lean (Wainwright Def 9.18 — Ψ(S) defining inequality)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `leanprover/lean4:v4.29.1`.
You are on the cluster — iterate with plain `lake build StatLean.HighDimensionalStatistics.MEstimator.SubspaceLip`
(NOT `srun … lake build`; you are already inside the allocation). Mathlib is cached.

## Hard constraints
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/SubspaceLip.lean`. Touch nothing else.
- Goal: **0 sorries**, 0 errors. Keep docstrings + signatures unchanged. Lines ≤ 100 chars.
- After green: `#print axioms subspaceLip_le` → expect only `propext, Classical.choice, Quot.sound`.
- If a piece resists, lift to a `private lemma` with one `sorry` + `-- TODO(me):`, never `sorry` in a `have`.

## Context
`subspaceLip Φ S := sSup ((fun u => Φ u / ‖u‖) '' ((S : Set E) \ {0}))` (in `Defs.lean`).
`E` is a finite-dim real inner-product space. `Φ : Seminorm ℝ E`. `open scoped InnerProductSpace`.

## The three lemmas

### 1. `seminorm_le_const_mul_norm` — `∃ C ≥ 0, ∀ x, Φ x ≤ C·‖x‖` (the crux)
Orthonormal-basis argument:
- `let b := stdOrthonormalBasis ℝ E` (an `OrthonormalBasis (Fin (finrank ℝ E)) ℝ E`).
- `x = ∑ i, ⟪b i, x⟫_ℝ • b i` via `b.sum_repr x` (or `OrthonormalBasis.sum_repr`); the `repr`
  coordinate is `b.repr x i = ⟪b i, x⟫_ℝ` (`OrthonormalBasis.repr_apply_apply`).
- `Φ x ≤ ∑ i, Φ (⟪b i,x⟫_ℝ • b i)` — subadditivity over a finset. Find it via `exact?`/`apply?`:
  try `map_sum_le` / `Seminorm` is an `AddGroupSeminormClass`, so `Finset` triangle should exist;
  fallback `Finset.sum` induction with `map_add_le_add`.
- `Φ (⟪b i,x⟫_ℝ • b i) = |⟪b i,x⟫_ℝ| · Φ (b i)` via `map_smul_eq_mul` + `Real.norm_eq_abs`.
- So `Φ x ≤ ∑ i, |⟪b i,x⟫_ℝ| · Φ (b i)`. Cauchy–Schwarz on the finite sum
  (`Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq`):
  `(∑ |⟪b i,x⟫| · Φ(b i)) ≤ √(∑ ⟪b i,x⟫²) · √(∑ Φ(b i)²)`.
- `√(∑ i, ⟪b i,x⟫_ℝ²) = ‖x‖`: Parseval, `b.norm_eq` / `OrthonormalBasis.norm_sq_eq_sum` (or
  `← b.repr.norm_map x` with `EuclideanSpace` norm = `√(∑ ·²)`). Get `∑ ⟪b i,x⟫² = ‖x‖²`.
- Set `C := √(∑ i, Φ (b i) ^ 2) ≥ 0` (`Real.sqrt_nonneg`). Conclude `∀ x, Φ x ≤ C·‖x‖`.
(If Parseval plumbing is painful, an acceptable alternative `C` is `∑ i, Φ (b i)` with the cruder
bound `|⟪b i,x⟫_ℝ| ≤ ‖x‖` from `abs_real_inner_le_norm (b i) x` + `‖b i‖ = 1`, giving
`Φ x ≤ (∑ Φ (b i))·‖x‖` directly — no Cauchy–Schwarz needed. Prefer whichever builds.)

### 2. `subspaceLip_nonneg` — `0 ≤ subspaceLip Φ S`
`unfold subspaceLip`; apply `Real.sSup_nonneg` — every member of the image is `Φ u / ‖u‖ ≥ 0`
(`div_nonneg (apply_nonneg Φ u) (norm_nonneg u)`). Handles the empty (`S = 0`) case automatically
(`sSup ∅ = 0`).

### 3. `subspaceLip_le` — `u ∈ S → Φ u ≤ subspaceLip Φ S · ‖u‖`
- `by_cases hu0 : u = 0`. If `u = 0`: `simp [hu0, map_zero]` (both sides 0).
- Else `‖u‖ > 0` (`norm_pos_iff.mpr hu0`). Show `Φ u / ‖u‖ ≤ subspaceLip Φ S`, then
  `(div_le_iff (norm_pos…)).mp` to get `Φ u ≤ subspaceLip Φ S * ‖u‖`.
- `Φ u / ‖u‖ ≤ subspaceLip Φ S` by `le_csSup`:
  * membership: `Φ u / ‖u‖ ∈ (fun v => Φ v/‖v‖) '' ((S:Set E)\{0})` since `u ∈ S`, `u ≠ 0`.
  * `BddAbove`: from `seminorm_le_const_mul_norm Φ` obtain `⟨C, hC0, hC⟩`; every member
    `Φ v/‖v‖ ≤ C` (for `v ≠ 0`: `div_le_iff` + `hC v`). Provide `C` as the upper bound.

## Tips
- `stdOrthonormalBasis ℝ E : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E` — `import` is via `Defs`
  (Projection.Basic pulls inner-product basis API); if a name is missing, `exact?`/`loogle`.
- For `Real.sSup_nonneg` / `le_csSup` use `Mathlib.Order.ConditionalCompleteLattice` API.
- Report final `lake build` status + `#print axioms` for all three.
