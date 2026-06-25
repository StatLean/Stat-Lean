Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools (`./tools/loogle.sh '"name"'`, `./tools/check.sh 'Matrix.PosDef'`, `./tools/api.sh`, `exact?`, `simp?`). Never `lake update`. You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries. Prove in named pieces.

# CONTEXT (do NOT modify other files)
`StatLean/HighDimensionalStatistics/ForMathlib/GramMatrix.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Matrix`, `open scoped InnerProductSpace`,
`variable {n d : ℕ}`, `↥S = {x // x ∈ S}`) defines:
* `gram X S = (Xsub X S)ᵀ * (Xsub X S) : Matrix ↥S ↥S ℝ`
* `gramInv X S = (gram X S)⁻¹`
* `projPerp X S = 1 - (Xsub X S) * (gramInv X S) * (Xsub X S)ᵀ : Matrix (Fin n) (Fin n) ℝ`
* `matLinftyNorm A = ⨆ i, ∑ j, |A i j|`

The merged `SupportSubmatrix.lean` (import it — it is PROVED) gives: `Xsub`, `designSub`,
`designSub_apply : (designSub X S v).ofLp = (Xsub X S).mulVec v.ofLp`,
`normSq_designSub : ‖designSub X S v‖^2 = ∑ i:↥S, ((Xsub X S)ᵀ.mulVec ((Xsub X S).mulVec v.ofLp)) i * v.ofLp i`.
Several lemmas carry the **coercivity adapter** hyp `hcoer : ∀ v, cmin·‖v‖² ≤ (1/n)·‖designSub X S v‖²`
(= condition (A3) unfolded) plus `hn : 0 < n`, `hcmin : 0 < cmin`.

Mathlib bricks (verify exact names with the search tools): `Matrix.isHermitian_transpose_mul_self`,
`Matrix.PosDef` (check its def with `./tools/check.sh`), `Matrix.PosDef.det_pos` / `isUnit_iff_ne_zero`,
`Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`, `Matrix.mulVec_mulVec` (`A *ᵥ (B *ᵥ v) = (A*B) *ᵥ v`),
`Matrix.IsHermitian.inv`, `Matrix.dotProduct_mulVec`, `Matrix.dotProduct_comm`, `real_inner_le_norm`.

# TASK
Close ALL 10 sorries in `GramMatrix.lean` to 0-sorry. Do NOT change any signature.

# PROOFS
- `gram_quadForm`: `(gram X S).mulVec v.ofLp ⬝ᵥ v.ofLp = ‖designSub X S v‖²`. Rewrite `gram`,
  use `Matrix.mulVec_mulVec` to get `Xₛᵀ *ᵥ (Xₛ *ᵥ v)`, then `normSq_designSub` (its RHS is exactly
  `(Xₛᵀ(Xₛv)) ⬝ᵥ v` written as a sum — `dotProduct` unfolds to that sum).
- `gram_isHermitian`: `Matrix.isHermitian_transpose_mul_self (Xsub X S)` (gram is defeq `Xₛᵀ * Xₛ`).
- `gram_posDef_of_coercive`: `refine ⟨gram_isHermitian X S, ?_⟩; intro x hx`. The goal is
  `0 < star x ⬝ᵥ (gram X S).mulVec x` (check exact shape via `./tools/check.sh 'Matrix.PosDef'`).
  Over ℝ `star x = x`; rewrite to `(gram X S).mulVec x ⬝ᵥ x` (`dotProduct_comm`) then to
  `‖designSub X S (WithLp.toLp 2 x)‖²` via `gram_quadForm` (note `(WithLp.toLp 2 x).ofLp = x`).
  Set `v := (WithLp.toLp 2 x : EuclideanSpace ℝ ↥S)`; `hx : x ≠ 0` gives `0 < ‖v‖` (`WithLp.toLp`
  injective / `norm_pos_iff`), so `hcoer v` plus `hcmin`, `hn` give `0 < (1/n)‖Xₛv‖²` hence `0 < ‖Xₛv‖²`.
- `gram_isUnit_det`: `isUnit_iff_ne_zero.mpr (gram_posDef_of_coercive … ).det_pos.ne'`.
- `gramInv_mulVec_gram`: `rw [gramInv, ← Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (gram_isUnit_det …), Matrix.one_mulVec]`.
- `gramInv_isHermitian`: `(gram_isHermitian X S).inv` (rewrite `gramInv`).
- `norm_gramInv_mulVec_le`: let `w := (gramInv X S).mulVec u.ofLp`. Then `(gram X S).mulVec w = u.ofLp`
  (right inverse: `Matrix.mul_nonsing_inv` + `mulVec_mulVec`). Cauchy–Schwarz `⟨u, toLp w⟩ ≤ ‖u‖‖toLp w‖`
  (`real_inner_le_norm`); `⟨u, toLp w⟩ = (u.ofLp) ⬝ᵥ w = ((gram)·w) ⬝ᵥ w = ‖designSub X S (toLp w)‖²`
  (`gram_quadForm`); by `hcoer (toLp w)` and `hn`, `‖Xₛ(toLp w)‖² ≥ cmin·n·‖toLp w‖²`. Combine:
  `cmin·n·‖toLp w‖² ≤ ‖u‖·‖toLp w‖`, divide by `‖toLp w‖` (case `w = 0` trivial) ⇒
  `‖toLp w‖ ≤ (1/(cmin·n))·‖u‖`. (`EuclideanSpace.inner_eq`/`PiLp.inner_apply` to turn `⟨·,·⟩` into `⬝ᵥ`.)
- `projPerp_idempotent`: write `M := Xₛ * gramInv * Xₛᵀ`; `projPerp = 1 - M`. Show `M * M = M` using
  `Xₛᵀ * Xₛ = gram` and `gramInv * gram = 1` (`nonsing_inv_mul`): `M*M = Xₛ*gramInv*(Xₛᵀ*Xₛ)*gramInv*Xₛᵀ
  = Xₛ*(gramInv*gram*gramInv)*Xₛᵀ = Xₛ*gramInv*Xₛᵀ = M`. Then `(1-M)*(1-M) = 1 - 2M + M*M = 1 - M`.
- `projPerp_apply_norm_le`: `projPerp` is symmetric (`Pᵀ = P`, using `gramInv_isHermitian` and
  `transpose_mul`/`transpose_transpose`) and idempotent (above). For symmetric idempotent `P`:
  `‖toLp(P·u)‖² = ⟨P u, P u⟩ = ⟨P u, u⟩` (idem+symm) `≤ ‖toLp(P u)‖·‖u‖` (Cauchy–Schwarz) ⇒
  `‖toLp(P u)‖ ≤ ‖u‖`.
- `matLinftyNorm_mulVec_le`: `haveI := Fintype.ofFinite p`; `apply ciSup_le; intro i`;
  `|(A.mulVec v) i| = |∑ j, A i j * v j| ≤ ∑ j, |A i j| * |v j| ≤ ∑ j, |A i j| * (⨆ j, |v j|)
  = (∑ j |A i j|)·(⨆|v|) ≤ matLinftyNorm A · (⨆|v|)` (last step `le_ciSup` with
  `Finite.bddAbove_range`; `⨆|v|` nonneg). Use `Finset.abs_sum_le_sum_abs`, `abs_mul`, `Finset.sum_mul`.

# REQUIREMENTS
ZERO sorry. Keep all 10 signatures verbatim (incl. the `hcoer`/`hn`/`hcmin` adapter hyps and their
`-- LEAN-ONLY` tags). You MAY add `private` helper lemmas (e.g. `projPerp_isSymm`, a right-inverse
`gram_mulVec_gramInv`) in THIS file only. Do not touch any other file, the umbrella, `lakefile.lean`,
`lake-manifest.json`, or `lean-toolchain`.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/ForMathlib/GramMatrix.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.ForMathlib.GramMatrix
# DONE = build exits 0; 0 sorries; commit (`sr(gram): Gram posDef/inverse/projection bounds (Wainwright §7.5)`).
  Report: build status, sorry count, helper lemmas added, exact Mathlib names used for PosDef/inverse,
  any signature/constant that needed adjustment (flag if `1/(cmin*n)` had to change).
