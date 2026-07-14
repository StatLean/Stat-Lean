# Close the 2 sorries in NonparametricStatistics/LocalPolynomial/Quadratic.lean (amended with 0 < h)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.LocalPolynomial.Quadratic` (no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/LocalPolynomial/Quadratic.lean`. Touch nothing
  else. Keep all signatures, tags, docstrings UNCHANGED (the `0 < h` amendment is already in).
- Goal **0 sorries**, 0 errors. You MAY add `private` helper lemmas. Lines ≤ 100. Foreground
  `lake build` only; never background it.
- After green: `#print axioms` on `isLPSolution_iff_normal`, `isLPSolution_inv_mulVec` → only
  `propext, Classical.choice, Quot.sound`.

## Context (all already in the file — reuse)
- `isLPSolution_imp_normal` (→ direction, proved), `lpMatrix_mulVec_apply`,
  `lpObjective_add_single` (coordinate-direction expansion), `linear_coeff_eq_zero`,
  `lpMatrix_posDef`, `isLPSolution_unique`, `lpEstimator_eq_isLPSolution` — study their proofs;
  the completing-the-square pieces are there.

## Proofs
### `isLPSolution_iff_normal` (the remaining `←` direction, now with `hh : 0 < h`)
1. `n ≥ 1` from `hpd`: if `n = 0` then `lpMatrix = ((0:ℝ)*h)⁻¹ • ∑ (empty) = 0` and the zero
   matrix is not PosDef (`hpd.2` at `Pi.single 0 1` gives `0 < 0`). Hence
   `hnh : 0 < (n:ℝ) * h` (`Nat.cast_pos`, `mul_pos`).
2. Key identity (prove as a `private lemma`, or inline): for all `θ θ'` with `Δ := θ' - θ`,
   `lpObjective xdat Y K h ℓ t θ' - lpObjective xdat Y K h ℓ t θ
      = (n:ℝ)*h * (∑ j, Δ j * (lpMatrix xdat K h ℓ t).mulVec Δ j)
        + 2 * ((n:ℝ)*h) * (∑ j, Δ j * ((lpMatrix xdat K h ℓ t).mulVec θ - lpRhs xdat Y K h ℓ t) j)`.
   Route: expand both objectives; per data index `i`,
   `(Yᵢ - ⟨θ', Uᵢ⟩)² - (Yᵢ - ⟨θ, Uᵢ⟩)² = ⟨Δ, Uᵢ⟩² - 2·(Yᵢ - ⟨θ, Uᵢ⟩)·⟨Δ, Uᵢ⟩` (ring), multiply
   by `Kᵢ`, sum over `i`, and match the two matrix-side sums via `lpMatrix_mulVec_apply` and
   the `lpRhs` definition exactly as done inside `isLPSolution_imp_normal` (the `hexp` step
   there is the same bookkeeping — with `mul_inv_cancel_left₀ hnh.ne'`). Sum-swap with
   `Finset.sum_comm`, `Finset.mul_sum`, `ring`.
3. Given `hnorm : B θ = a`, the second term vanishes (`sub_self`, `mul_zero`, sum of zeros);
   the first is `≥ 0`: `hpd.posDef`-quadratic at `Δ` — careful: `hpd.2` gives `0 < ⟨Δ, BΔ⟩`
   only for `Δ ≠ 0`; case `Δ = 0` gives `0 = 0`. Use `Matrix.PosDef` API
   (`hpd.dotProduct_mulVec_nonneg`? if absent, rcases on `Δ = 0`). Mind the bridge between
   `∑ j, Δ j * (B.mulVec Δ) j` and Mathlib's `Δ ⬝ᵥ B *ᵥ Δ` (`dotProduct` unfolds to the sum;
   `simp [dotProduct]` or `rfl`-adjacent `change`).
4. Conclude `∀ θ', obj θ ≤ obj θ'` — `linarith`/`nlinarith` from 2+3 (`mul_nonneg hnh.le …`).

### `isLPSolution_inv_mulVec`
`(isLPSolution_iff_normal hh hpd _).mpr` applied to
`B.mulVec (B⁻¹.mulVec a) = a`: `Matrix.mulVec_mulVec`, `Matrix.mul_nonsing_inv _ hdet`,
`Matrix.one_mulVec`, with `hdet := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit` — exactly
the `hBw` step inside `lpMatrix_inv_mulVec_sq_le`.

Report final `lake build` status + `#print axioms` for both theorems.
