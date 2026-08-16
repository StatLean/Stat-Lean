import StatLean.StatisticalModels.GraphicalModels.Gaussian.Precision

/-!
# Partial regression coefficients — the conditional mean of one coordinate

The third statistical reading of the concentration matrix (Lauritzen §5.1.3, p. 130, the closing
unnumbered displays). Proposition C.5 says that the conditional distribution of `Y_γ` given all
the remaining variables is univariate normal; writing its conditional expectation as

`ξ_γ + ∑_{μ ∈ Γ∖{γ}} β_{γμ ∣ Γ∖{γ}} (y_μ − ξ_μ)`

and "using (C.4) we find the partial regression coefficient as `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`".

* `partialRegressionCoeff S γ μ := −k_{γμ}/k_{γγ}` — Lauritzen's `β_{γμ ∣ Γ∖{γ}}`;
* `condMeanMatrix_eq_neg_mul` — Lauritzen **(C.4)** as a matrix identity on the existing
  `condMeanMatrix`, i.e. the Gaussian regression matrix *is* `−K₂₂⁻¹K₂₁`;
* `condMeanMatrix_apply_eq_neg_precision_div` — its scalar form on a singleton regressed block:
  the `(γ, μ)` regression coefficient is `−k_{γμ}/k_{γγ}`;
* **`gaussianCondKernel_mean_coord` (HEADLINE)** — Lauritzen's regression equation itself: the
  mean of the conditional law delivered by `gaussianCondKernel` is
  `ξ_γ + ∑_{μ} β_{γμ}(y_μ − ξ_μ)`;
* `partialRegressionCoeff_eq_zero_iff` and
  **`condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero`** — the corollary: the
  regression coefficient vanishes iff the concentration entry does iff the two coordinates are
  conditionally independent given the rest.

Gaussian conditioning itself is **not** re-derived here: the conditional law is the repo's
`gaussianCondKernel` and the exact disintegration `compProd_gaussianCondKernel` (G3.4) of
`Gaussian.Conditioning`. This file only reads the mean of that kernel in concentration-matrix
coordinates.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**, §5.1.3, p. 130 (the conditional expectation
display and `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}` — both **unnumbered**), deriving it from
Appendix C, p. 256: Proposition C.5 and the identity (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻`
(`Lauritzen §5.1.3`, `Lauritzen App. C`). Page numbers and item kinds follow
`notes/factor_graphical/books.md`; on the generalized inverse `Σ₂₂⁻` versus `Σ₂₂⁻¹` see the
module docstring of `Gaussian.Precision`.

**Proof formalization notes.**

*Book vs Lean, orientation.* As in `Gaussian.Precision`: Lauritzen conditions on the *second*
block, the repo's `condMeanMatrix S₁₁ S₁₂ = S₁₂ᵀ S₁₁⁻¹` regresses the *second* block on the
*first*. So Lauritzen's (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻¹` is transcribed as
`K₂₂⁻¹K₂₁ = −condMeanMatrix S₁₁ S₁₂`, which is `submatrix_precisionMatrix_fromBlocks_inr_inl`
rearranged by `condCovMatrix_eq_inv_submatrix_precisionMatrix`.

*Book vs Lean, "one coordinate given all others".* Lauritzen regresses a **single** variable
`Y_γ` on the rest, so the regressed block is a singleton. On the sum index that is a second block
`ι₂` with `Subsingleton ι₂` plus a witness — the type-level form of `|{γ}| = 1` — under which
`K₂₂` is a `1 × 1` matrix and `K₂₂⁻¹K₂₁` is the scalar quotient `−k_{γμ}/k_{γγ}`. The
general-block matrix identity is stated too (`condMeanMatrix_eq_neg_mul`) and is what BLUP-style
consumers want.

*Book vs Lean, `Matrix.inv` junk.* `partialRegressionCoeff` is total (`x / 0 = 0`); for singular
`S` the concentration matrix is `0` and the coefficient is `0` vacuously. Every substantive
statement carries `PosDef`.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| the conditional law of a Gaussian block | `gaussianCondKernel`, `gaussianCondKernel_apply`, `compProd_gaussianCondKernel` (G3.4, `Gaussian.Conditioning`) — **never** re-derive Gaussian conditioning |
| (C.4) in block form | `submatrix_precisionMatrix_fromBlocks_inr_inl` (`Gaussian.Precision`) |
| (C.3), to turn `K₂₂⁻¹` into `condCovMatrix` | `condCovMatrix_eq_inv_submatrix_precisionMatrix` (`Gaussian.Precision`) |
| `k_{γγ} > 0`, so the quotient is honest | `precisionMatrix_diag_pos` (`Gaussian.Precision`) |
| coordinates of the matrix action `(A x)_k = ∑_l A_{kl} x_l` | `Matrix.toLpLin_apply` + `Matrix.mulVec`/`dotProduct` unfolding (the same one-line `simp` as `ForMathlib.CovarianceMatrix.toEuclideanLin_coord`) |
| `ρ = 0 ⟺ k_{γμ} = 0 ⟺ CI` | `condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero` — Prop. 5.2 (`Gaussian.Precision`) |

*Not stated here.* The identification of the ambient-index `partialRegressionCoeff S γ μ` with
the sum-index `condMeanMatrix` entry requires transporting `S` along
`Equiv.sumCompl (· ∈ ({γ} : Finset ι)ᶜ)` through `multivariateGaussian_map_reindex` (the only
`Fin`/`Sum` corridor); that bookkeeping belongs to whoever proves the headline of
`Gaussian.Precision`, and the two families of statements are deliberately kept apart so that
neither waits on the other.

**Bibliographic comments.** The reading of `−k_{γμ}/k_{γγ}` as a regression coefficient is
classical (the "normal equations" of least squares applied to the conditional normal); it is the
form in which the Gaussian graphical model is estimated node-by-node in the modern
neighbourhood-selection literature (N. Meinshausen and P. Bühlmann, "High-dimensional graphs and
variable selection with the Lasso," *Ann. Statist.* **34** (2006), 1436–1462), which is exactly
`condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero` used as an estimation
principle.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **partial regression coefficient** `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}` (Lauritzen §5.1.3,
p. 130, closing display): the coefficient of `y_μ − ξ_μ` in the conditional expectation of `Y_γ`
given all the remaining variables.

Edge behaviour: total (`x / 0 = 0`); for singular `S` the concentration matrix is `0` and the
coefficient is `0` vacuously, so substantive statements assume `S.PosDef`. On the diagonal the
formula gives `β_{γγ} = −1`, an artefact of applying it outside its range `μ ≠ γ`. -/
noncomputable def partialRegressionCoeff (S : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  -(precisionMatrix S i j) / precisionMatrix S i i

end Defs

section BlockIdentity

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen (C.4)** (App. C, p. 256), transcribed for the repo's orientation: the Gaussian
regression matrix `condMeanMatrix S₁₁ S₁₂ = S₂₁S₁₁⁻¹` is minus the conditional covariance times
the off-diagonal block of the joint concentration matrix, `−K₂₂⁻¹K₂₁`.

This is `submatrix_precisionMatrix_fromBlocks_inr_inl` solved for `condMeanMatrix`, using
(C.3) to identify `K₂₂⁻¹` with `condCovMatrix`. -/
theorem condMeanMatrix_eq_neg_mul
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.4)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    condMeanMatrix S₁₁ S₁₂
      = -(condCovMatrix S₁₁ S₁₂ S₂₂
            * (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inl) := by
  sorry

/-- **`β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`** (Lauritzen §5.1.3, p. 130): the scalar form of (C.4)
when the regressed block is a single coordinate. -/
theorem condMeanMatrix_apply_eq_neg_precision_div
    -- LEAN-ONLY: Lauritzen regresses one variable `Y_γ` on the rest; `Subsingleton` plus the
    -- witness `a` is the type-level form of `|{γ}| = 1`, under which `K₂₂⁻¹K₂₁` is a quotient
    [Subsingleton ι₂]
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) (a : ι₂) (u : ι₁) :
    condMeanMatrix S₁₁ S₁₂ a u
      = -(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inl u))
          / precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a) := by
  sorry

/-- **HEADLINE — Lauritzen's regression equation** (§5.1.3, p. 130). The conditional law of `Y_γ`
given `Y_{Γ∖{γ}} = y` is, by Proposition C.5, univariate normal; its mean — which the repo's
`gaussianCondKernel` delivers as `ξ_γ + (S₂₁S₁₁⁻¹(y − ξ))_γ`, see `gaussianCondKernel_apply` —
is Lauritzen's

`ξ_γ + ∑_{μ ∈ Γ∖{γ}} β_{γμ ∣ Γ∖{γ}} (y_μ − ξ_μ)`,  with  `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`.

Gaussian conditioning is *consumed*, not re-derived: the left-hand side is literally the mean
parameter appearing in `gaussianCondKernel_apply`, whose disintegration property is G3.4
`compProd_gaussianCondKernel`. -/
theorem gaussianCondKernel_mean_coord
    -- LEAN-ONLY: one regressed variable, as in the book; see `condMeanMatrix_apply_eq_neg_precision_div`
    [Subsingleton ι₂]
    (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef)
    (y : EuclideanSpace ℝ ι₁) (a : ι₂) :
    (m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (y - m₁)) a
      = m₂ a + ∑ u : ι₁,
          (-(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inl u))
              / precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a))
            * (y u - m₁ u) := by
  sorry

end BlockIdentity

section Corollary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- **The regression coefficient vanishes exactly when the concentration entry does.** The
denominator `k_{γγ}` is strictly positive for a regular `Σ`. -/
theorem partialRegressionCoeff_eq_zero_iff
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialRegressionCoeff S i j = 0 ↔ precisionMatrix S i j = 0 := by
  sorry

/-- **Corollary of Lauritzen Proposition 5.2** (§5.1.3, pp. 129–130): the partial regression
coefficient of `Y_μ` in the regression of `Y_γ` on all the remaining variables vanishes exactly
when `Y_γ` and `Y_μ` are conditionally independent given the rest. This is the "regress each
variable on all the others and read off the graph from the zero coefficients" characterisation
of the Gaussian graphical model. -/
theorem condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero
    (m : EuclideanSpace ℝ ι)
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} (Finset.univ \ {i, j})
      ↔ partialRegressionCoeff S i j = 0 := by
  sorry

/-- Asymmetry of the regression coefficients versus symmetry of the graph: `β_{γμ}` and `β_{μγ}`
differ (they are scaled by different diagonal entries) but vanish together, which is what makes
the edge set of the Gaussian graphical model well defined. -/
theorem partialRegressionCoeff_eq_zero_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialRegressionCoeff S i j = 0 ↔ partialRegressionCoeff S j i = 0 := by
  sorry

end Corollary

end StatLean.StatisticalModels.GraphicalModels
