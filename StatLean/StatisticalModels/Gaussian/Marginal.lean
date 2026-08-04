import StatLean.StatisticalModels.Gaussian.Affine

/-!
# Block marginals and independent blocks of a joint Gaussian

The block calculus of a Gaussian on the sum index `ι₁ ⊕ ι₂` with covariance
`fromBlocks Σ₁₁ Σ₁₂ Σ₁₂ᵀ Σ₂₂` (one off-diagonal block carried; the other is its transpose
definitionally — killing symmetry side conditions):

* `multivariateGaussian_map_blockFst`/`_blockSnd` — the block marginals are the block
  Gaussians `N(m₁, Σ₁₁)`, `N(m₂, Σ₂₂)`;
* **`multivariateGaussian_fromBlocks_prod` (G2.9)** — vanishing cross-covariance makes the
  blocks independent: the joint transported to the product space is the product of the
  marginals — the Gaussian "uncorrelated ⇒ independent" theorem in block form, and the base
  case of the conditioning theorem (G-B3).

**Reference.** `And58` §2.4–2.5 (marginal and independence properties of the multivariate
normal) (verify §).

**Proof formalization notes.** Marginals via `multivariateGaussian_map_affine` at the block
projection matrices (`blockFst` as the matrix `[1 0]`: the `fromBlocks`-algebra
`[1 0] · fromBlocks … · [1 0]ᵀ = Σ₁₁` is `Matrix.fromBlocks_multiply`-level) — or directly
via the pin's `measurePreserving_restrict₂_multivariateGaussian` if its submatrix form
matches. G2.9 by charFun on the sum space: `inner_sum_split` factorizes the joint charFun
when `Σ₁₂ = 0`; compare against `charFun` of the product (`charFun` of `Measure.prod` splits
— search `charFun_prod`; else compute through `MeasureTheory.integral_prod`), transported by
`ext_of_map_sumMeasEquivProd`.

**Bibliographic comments.** Classical; the "uncorrelated Gaussians are independent" caveat
(true jointly, false marginally) is the standard warning this block formulation makes
precise.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
  (Σ₁₁ : Matrix ι₁ ι₁ ℝ) (Σ₁₂ : Matrix ι₁ ι₂ ℝ) (Σ₂₂ : Matrix ι₂ ι₂ ℝ)

/-- **First block marginal** (`And58 §2.4`): the `blockFst`-image of the joint block
Gaussian is `N(m₁, Σ₁₁)`. -/
theorem multivariateGaussian_map_blockFst
    -- USER-INPUT: genuine joint covariance; And58 §2.4
    (hJ : (Matrix.fromBlocks Σ₁₁ Σ₁₂ Σ₁₂ᵀ Σ₂₂).PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks Σ₁₁ Σ₁₂ Σ₁₂ᵀ Σ₂₂)).map
        (blockFst (ι₁ := ι₁) (ι₂ := ι₂))
      = multivariateGaussian m₁ Σ₁₁ := by
  sorry

/-- **Second block marginal** (`And58 §2.4`). -/
theorem multivariateGaussian_map_blockSnd
    -- USER-INPUT: genuine joint covariance; And58 §2.4
    (hJ : (Matrix.fromBlocks Σ₁₁ Σ₁₂ Σ₁₂ᵀ Σ₂₂).PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks Σ₁₁ Σ₁₂ Σ₁₂ᵀ Σ₂₂)).map
        (blockSnd (ι₁ := ι₁) (ι₂ := ι₂))
      = multivariateGaussian m₂ Σ₂₂ := by
  sorry

/-- **G2.9, independent blocks** (`And58 §2.5`): with vanishing cross-covariance, the joint
block Gaussian transported to the product space is the product of its block marginals —
jointly-Gaussian uncorrelated blocks are independent. -/
theorem multivariateGaussian_fromBlocks_prod
    -- USER-INPUT: genuine block covariances; And58 §2.5
    (h₁ : Σ₁₁.PosSemidef) (h₂ : Σ₂₂.PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks Σ₁₁ 0 0 Σ₂₂)).map
        (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
      = (multivariateGaussian m₁ Σ₁₁).prod (multivariateGaussian m₂ Σ₂₂) := by
  sorry

end StatLean.StatisticalModels
