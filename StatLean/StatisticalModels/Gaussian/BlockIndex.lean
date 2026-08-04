import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Block-index plumbing: `EuclideanSpace ℝ (ι₁ ⊕ ι₂)` vs the product space

The Gaussian slice works on the **sum index** `ι₁ ⊕ ι₂` (where Mathlib's
`multivariateGaussian`, `Matrix.fromBlocks` and the Schur-complement API live) and crosses to
the product `EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂` (where `Measure.compProd` and kernels
live) through exactly the objects of this file — nothing downstream ever unfolds
`WithLp`/`PiLp` internals:

* `blockFst`/`blockSnd` — the two coordinate-block projections (continuous linear maps);
* `blockPair` — the block assembly `E ι₁ → E ι₂ → E (ι₁ ⊕ ι₂)`;
* `inner_sum_split` — the inner product on the sum space splits over the blocks (the charFun
  workhorse);
* `sumMeasEquivProd` — the measurable equivalence with the product space, with
  `map`-injectivity `ext_of_map_sumMeasEquivProd` (so all charFun-uniqueness arguments run on
  the sum space and transport).

The plain product `E ι₁ × E ι₂` carries the sup norm — **no inner-product structure** — so
characteristic-function arguments cannot run there; this file is what makes "charFun on the
sum space, statements on the product space" sound.

**Reference.** LEAN-ONLY plumbing; no book counterpart. The block-matrix calculus it serves
is And58 Ch. 2 (verify §).

**Proof formalization notes.** The projections/assembly are defined coordinatewise on the
`PiLp` carrier and bundled as continuous linear maps (finite dimension gives continuity);
`sumMeasEquivProd` is the Borel isomorphism induced by the underlying continuous linear
equivalence (`Homeomorph.toMeasurableEquiv`). `inner_sum_split` is
`Fintype.sum_sum_type` applied to `PiLp.inner_apply`. Map-injectivity along a measurable
equivalence is `μ = (μ.map e).map e.symm` rewriting.

**Bibliographic comments.** None (plumbing).
-/

open MeasureTheory
open scoped InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Block projection onto the first (`Sum.inl`) coordinates, as a continuous linear map. -/
noncomputable def blockFst :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →L[ℝ] EuclideanSpace ℝ ι₁ :=
  sorry

/-- Block projection onto the second (`Sum.inr`) coordinates, as a continuous linear map. -/
noncomputable def blockSnd :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →L[ℝ] EuclideanSpace ℝ ι₂ :=
  sorry

/-- Block assembly: build a sum-index vector from its two blocks. -/
noncomputable def blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) :=
  sorry

@[simp]
theorem blockFst_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) (i : ι₁) :
    blockFst x i = x (Sum.inl i) := by
  sorry

@[simp]
theorem blockSnd_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) (j : ι₂) :
    blockSnd x j = x (Sum.inr j) := by
  sorry

@[simp]
theorem blockPair_inl (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) (i : ι₁) :
    blockPair x₁ x₂ (Sum.inl i) = x₁ i := by
  sorry

@[simp]
theorem blockPair_inr (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) (j : ι₂) :
    blockPair x₁ x₂ (Sum.inr j) = x₂ j := by
  sorry

@[simp]
theorem blockFst_blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    blockFst (blockPair x₁ x₂) = x₁ := by
  sorry

@[simp]
theorem blockSnd_blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    blockSnd (blockPair x₁ x₂) = x₂ := by
  sorry

@[simp]
theorem blockPair_blockFst_blockSnd (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    blockPair (blockFst x) (blockSnd x) = x := by
  sorry

/-- **The inner product splits over the blocks** — the charFun workhorse:
`⟪t, x⟫ = ⟪t₁, x₁⟫ + ⟪t₂, x₂⟫`. -/
theorem inner_sum_split (t x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    ⟪t, x⟫_ℝ = ⟪blockFst t, blockFst x⟫_ℝ + ⟪blockSnd t, blockSnd x⟫_ℝ := by
  sorry

/-- The measurable equivalence between the sum-index Euclidean space and the product of the
block spaces. -/
noncomputable def sumMeasEquivProd :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) ≃ᵐ EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ :=
  sorry

@[simp]
theorem sumMeasEquivProd_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    sumMeasEquivProd x = (blockFst x, blockSnd x) := by
  sorry

@[simp]
theorem sumMeasEquivProd_symm_apply (p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂) :
    sumMeasEquivProd.symm p = blockPair p.1 p.2 := by
  sorry

/-- Pushforward along the block equivalence is injective on measures: charFun-uniqueness
arguments on the sum space transport to product-space statements. -/
theorem ext_of_map_sumMeasEquivProd
    {μ ν : Measure (EuclideanSpace ℝ (ι₁ ⊕ ι₂))}
    (h : μ.map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        = ν.map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))) :
    μ = ν := by
  sorry

end StatLean.StatisticalModels
