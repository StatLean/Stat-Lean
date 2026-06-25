import StatLean.HighDimensionalStatistics.LinearModel.Defs
import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms

/-!
# Support-restricted design matrix `X_S` (ForMathlib)

Theorem-agnostic infrastructure (`ForMathlib` layer) for Lasso **support recovery**
(Wainwright §7.5, Thm 7.21 / Cor 7.22). The primal–dual-witness proof needs the
**column-restricted design** `X_S` — the columns of `X` indexed by the support set
`S` — together with its Gram matrix `XₛᵀXₛ` and inverse. Inverting that Gram block
forces a *square* index type, so `X_S` is re-indexed by the subtype `↥S = {x // x ∈ S}`
(the `Fin d`-selector form `X · diag(𝟙_S)` is singular for `|S| < d` and has no inverse).

This file provides:
* `Xsub X S`    — `X_S : Matrix (Fin n) ↥S ℝ`, the column-restricted design;
* `designSub X S` — the induced map `E^{↥S} → E^n`, `v ↦ X_S v` (analogue of `designMap`);
* `col X j`     — the `j`-th column `X_j : E^n`;
* the `mulVec` bridges relating `X_S` / `X_Sᵀ` to the full design `X` / `Xᵀ`,
  consumed by `GramMatrix.lean` (Gram quadratic form, positive-definiteness) and the
  dual-certificate assembly.

Reuses `designMap` (`LinearModel/Defs.lean`) and the ℓ¹/ℓ∞/`restrict` bricks
(`ForMathlib/VecNorms.lean`). Pure linear algebra — no book hypotheses, hence no
`USER-INPUT`/`LEAN-ONLY` tags (all lemmas are hypothesis-free identities).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Column-restricted design** `X_S`: the submatrix of `X` keeping only the columns
indexed by `S`, re-indexed by the subtype `↥S`. -/
def Xsub (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix (Fin n) {x // x ∈ S} ℝ :=
  X.submatrix id Subtype.val

/-- **Support design map** `E^{↥S} → E^n`, `v ↦ X_S v` — the support-restricted
analogue of `designMap`. -/
noncomputable def designSub (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    EuclideanSpace ℝ {x // x ∈ S} →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin (Xsub X S)

/-- The `j`-th **column** `X_j` of the design matrix, as a vector in `E^n`. -/
def col (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => X i j)

/-- Column selection = full design applied to the zero-extension of `v` to `Fin d`. -/
lemma Xsub_mulVec (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (v : {x // x ∈ S} → ℝ) :
    (Xsub X S).mulVec v
      = X.mulVec (fun j => if h : j ∈ S then v ⟨j, h⟩ else 0) := by
  sorry

/-- Coordinate of `X_Sᵀ u`: the `i`-th entry (`i ∈ S`) is column `i.val` of `X` dotted
with `u`. -/
lemma Xsub_transpose_mulVec_apply (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (u : Fin n → ℝ) (i : {x // x ∈ S}) :
    ((Xsub X S)ᵀ.mulVec u) i = ∑ k : Fin n, X k i.val * u k := by
  sorry

/-- The support design map in coordinates: `(X_S v).ofLp = X_S *ᵥ v.ofLp`. -/
lemma designSub_apply (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (v : EuclideanSpace ℝ {x // x ∈ S}) :
    (designSub X S v).ofLp = (Xsub X S).mulVec v.ofLp := by
  sorry

/-- Squared norm of `X_S v` as the Gram quadratic form `vᵀ (XₛᵀXₛ) v` (coordinate form):
`‖X_S v‖² = ∑_{i∈S} (X_Sᵀ (X_S v))_i · v_i`. -/
lemma normSq_designSub (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (v : EuclideanSpace ℝ {x // x ∈ S}) :
    ‖designSub X S v‖ ^ 2
      = ∑ i : {x // x ∈ S},
          ((Xsub X S)ᵀ.mulVec ((Xsub X S).mulVec v.ofLp)) i * v.ofLp i := by
  sorry

/-- The `j`-th column equals the design map applied to the `j`-th basis vector. -/
lemma col_eq_designMap_single (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    col X j = designMap X (EuclideanSpace.single j (1 : ℝ)) := by
  sorry

end StatLean.HighDimensionalStatistics
