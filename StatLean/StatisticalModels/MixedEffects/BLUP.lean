import StatLean.StatisticalModels.MixedEffects.Marginal
import StatLean.StatisticalModels.Gaussian.Conditioning

/-!
# BLUP — the best linear unbiased predictor of the random effects

The prediction theory of the linear mixed model, in the (Y, b) block order fixed from the
start (so the Gaussian conditioning theorem applies without a block swap):

* `lmmJointLaw` — the joint law of `(Y, b)`; **M3a**: in the Gaussian case it is the block
  Gaussian with blocks `Σ_YY = Z G Zᵀ + R`, `Σ_Yb = Z G`, `Σ_bb = G`;
* `condMeanMatrix_lmm` — the Gaussian regression matrix is Henderson's `G Zᵀ V⁻¹`;
* **M3b (`compProd_lmmJointLaw`)** — BLUP as Gaussian conditioning: the joint disintegrates
  through `gaussianCondKernel`, whose mean function is `y ↦ G Zᵀ V⁻¹ (y − Xβ)` — the BLUP —
  and whose covariance is `G − G Zᵀ V⁻¹ Z G`;
* **M3c (`blupRisk_eq_add`)** — the variational (Gaussian-free) characterization: for
  *arbitrary* centered second-moment latent laws, the mean-squared prediction risk of any
  linear predictor decomposes as the risk of `A* = G Zᵀ V⁻¹` plus
  `tr((A − A*) V (A − A*)ᵀ)`; whence `A*` minimizes (`blupRisk_le`) — "BLUP is a good
  thing" with no Gaussianity at all.

**Reference.** C. R. Henderson, "Estimation of genetic parameters," *Ann. Math. Statist.*
**21** (1950), 309–310 (abstract) (`Hen50`); C. R. Henderson, "Best linear unbiased
estimation and prediction under a selection model," *Biometrics* **31** (1975), 423–447,
§2 (verify §) (`Hen75 §2`); G. K. Robinson, "That BLUP is a good thing: the estimation of
random effects," *Statist. Sci.* **6** (1991), 15–51, §2–3 (verify §) (`Rob91`);
D. A. Harville, "Extension of the Gauss–Markov theorem to include the estimation of random
effects," *Ann. Statist.* **4** (1976), 384–395.

**Proof formalization notes.** M3a is an affine image of the product Gaussian
(`multivariateGaussian_map_affine` at the stacked matrix `fromBlocks`-shaped map
`(b, ε) ↦ (Zb + ε, b)` plus the `Xβ` translation, through the block plumbing); M3b is the
instantiation of the closed `compProd_gaussianCondKernel` at M3a's blocks — the matrix
identity `condMeanMatrix (ZGZᵀ+R) (ZG) = G Zᵀ V⁻¹` needs only `G` symmetric. M3c is trace
algebra over the G-B1 covariance calculus: expand the risk as
`tr(G) − 2 tr(A · Cov(y−Xβ, b)) + tr(A V Aᵀ)` and complete the square; `Cov(Zb+ε, b) = Z G`
under independence. *Book vs Lean:* M3c holds for arbitrary latent laws — the books state
it under Gaussianity or as the linear-predictor optimum; the moment form here is the
strongest honest version.

**Bibliographic comments.** BLUP is Henderson's (1950); its unification with Gaussian
conditional expectation and the variational reading is surveyed by Robinson (1991).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.MixedEffects

open StatLean.StatisticalModels

variable {n p q : ℕ}

/-! ### LEAN-ONLY plumbing

The block-diagonal PSD lemma, the stacked design matrix `M = [Z 1; 1 0]` realizing the pair
map `(b, ε) ↦ (Z b + ε, b)` on the sum index, and its conjugation identity
`M · diag(G, R) · Mᵀ = [Z G Zᵀ + R, Z G; (Z G)ᵀ, G]` — the block bookkeeping of M3a.
-/

/-- LEAN-ONLY: the matrix action on Euclidean space is measurable. -/
private theorem measurable_matAct {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁]
    (A : Matrix ι₂ ι₁ ℝ) :
    Measurable fun x : EuclideanSpace ℝ ι₁ => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) A).continuous_of_finiteDimensional).measurable

/-- LEAN-ONLY: the joint LMM map `(b, ε) ↦ (Xβ + Z b + ε, b)` is measurable. -/
private theorem measurable_jointMap (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p)) :
    Measurable fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1
          + be.2,
        be.1) :=
  ((((measurable_matAct D.Z).comp measurable_fst).const_add _).add measurable_snd).prodMk
    measurable_fst

/-- LEAN-ONLY: the zero vector assembles from zero blocks. -/
private theorem blockPair_zero {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] :
    blockPair (0 : EuclideanSpace ℝ ι₁) (0 : EuclideanSpace ℝ ι₂) = 0 := by
  ext k; cases k <;> rfl

/-- LEAN-ONLY: the quadratic form of a block matrix splits into its four block terms. -/
private theorem dotProduct_fromBlocks_mulVec {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₁ ι₂ ℝ) (C : Matrix ι₂ ι₁ ℝ) (E : Matrix ι₂ ι₂ ℝ)
    (x : ι₁ ⊕ ι₂ → ℝ) :
    x ⬝ᵥ (Matrix.fromBlocks A B C E) *ᵥ x
      = ((x ∘ Sum.inl) ⬝ᵥ A *ᵥ (x ∘ Sum.inl) + (x ∘ Sum.inl) ⬝ᵥ B *ᵥ (x ∘ Sum.inr))
        + ((x ∘ Sum.inr) ⬝ᵥ C *ᵥ (x ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ E *ᵥ (x ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_add]

/-- LEAN-ONLY: a block-diagonal matrix with PSD blocks is PSD (no cross terms). -/
private theorem posSemidef_fromBlocks_diag {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {S₁₁ : Matrix ι₁ ι₁ ℝ} {S₂₂ : Matrix ι₂ ι₂ ℝ} (h₁ : S₁₁.PosSemidef)
    (h₂ : S₂₂.PosSemidef) :
    (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₂ ι₁ ℝ) S₂₂).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨h₁.1.fromBlocks (by simp) h₂.1, fun x => ?_⟩
  have e₁ := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h₁).2 (x ∘ Sum.inl)
  have e₂ := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h₂).2 (x ∘ Sum.inr)
  simp only [star_trivial] at e₁ e₂ ⊢
  rw [dotProduct_fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, zero_add]
  linarith

/-- LEAN-ONLY: the coordinates of the first block. -/
private theorem ofLp_blockFst {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    WithLp.ofLp (blockFst w) = WithLp.ofLp w ∘ Sum.inl := rfl

/-- LEAN-ONLY: the coordinates of the second block. -/
private theorem ofLp_blockSnd {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    WithLp.ofLp (blockSnd w) = WithLp.ofLp w ∘ Sum.inr := rfl

/-- LEAN-ONLY: the stacked design matrix `[Z 1; 1 0]` — the linear part of the joint map. -/
private noncomputable def stackM (D : LMMDesign n p q) :
    Matrix (Fin n ⊕ Fin q) (Fin q ⊕ Fin n) ℝ :=
  Matrix.fromBlocks D.Z 1 1 0

/-- LEAN-ONLY: the stacked design acts as `(b, ε) ↦ (Z b + ε, b)`. -/
private theorem stackM_apply (D : LMMDesign n p q) (w : EuclideanSpace ℝ (Fin q ⊕ Fin n)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (stackM D) w
      = blockPair (Matrix.toEuclideanLin (𝕜 := ℝ) D.Z (blockFst w) + blockSnd w)
          (blockFst w) := by
  ext k
  cases k with
  | inl i =>
      simp [stackM, Matrix.toLpLin_apply, Matrix.fromBlocks_mulVec, blockPair,
        ← ofLp_blockFst, ← ofLp_blockSnd]
  | inr j =>
      simp [stackM, Matrix.toLpLin_apply, Matrix.fromBlocks_mulVec, blockPair,
        ← ofLp_blockFst, ← ofLp_blockSnd]

/-- LEAN-ONLY: the conjugation of the block-diagonal latent covariance by the stacked design
is the joint covariance of `(Y, b)`. -/
private theorem stackM_conj (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ) (hGm : Gmᵀ = Gm) :
    stackM D * (Matrix.fromBlocks Gm 0 0 Rm) * (stackM D)ᵀ
      = Matrix.fromBlocks (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm) (D.Z * Gm)ᵀ Gm := by
  rw [stackM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [Matrix.transpose_mul, hGm]

/-- LEAN-ONLY: the joint covariance of `(Y, b)` is a genuine covariance. -/
private theorem posSemidef_lmmJoint (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ) (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    (Matrix.fromBlocks (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm) (D.Z * Gm)ᵀ Gm).PosSemidef := by
  have hGmT : Gmᵀ = Gm := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hGm.1
  rw [← stackM_conj D Gm Rm hGmT]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (posSemidef_fromBlocks_diag hGm hRm).mul_mul_conjTranspose_same (stackM D)

/-- The joint law of `(Y, b)` in the linear mixed model — response first (the conditioning
block), latent effects second. -/
noncomputable def lmmJointLaw (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q)) :=
  (G.prod R).map fun be =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1
        + be.2,
      be.1)

/-- The `Y`-marginal of the joint law is the mixed-model observation law. -/
theorem lmmJointLaw_fst (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure G] [IsProbabilityMeasure R] :
    (lmmJointLaw D β G R).map Prod.fst = lmmLaw D β G R := by
  rw [lmmJointLaw, Measure.map_map measurable_fst (measurable_jointMap D β)]
  rfl

/-- **M3a, the Gaussian joint** (`Hen75 §2`; `Rob91 §2`): with Gaussian latent effects and
noise, `(Y, b)` is the block Gaussian with `Σ_YY = Z G Zᵀ + R`, `Σ_Yb = Z G`, `Σ_bb = G`
(response block first). -/
theorem lmmJointLaw_eq_blockGaussian (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (Gm : Matrix (Fin q) (Fin q) ℝ) (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; Hen75 §2
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef) :
    lmmJointLaw D β (multivariateGaussian 0 Gm) (multivariateGaussian 0 Rm)
      = (multivariateGaussian
            (blockPair (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β) 0)
            (Matrix.fromBlocks (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm)
              (D.Z * Gm)ᵀ Gm)).map
          (sumMeasEquivProd (ι₁ := Fin n) (ι₂ := Fin q)) := by
  have hGmT : Gmᵀ = Gm := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hGm.1
  have hdiag : (Matrix.fromBlocks Gm (0 : Matrix (Fin q) (Fin n) ℝ)
      (0 : Matrix (Fin n) (Fin q) ℝ) Rm).PosSemidef := posSemidef_fromBlocks_diag hGm hRm
  have hprod : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Gm).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) Rm)
      = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q ⊕ Fin n))
          (Matrix.fromBlocks Gm 0 0 Rm)).map
            (sumMeasEquivProd (ι₁ := Fin q) (ι₂ := Fin n)) := by
    rw [← multivariateGaussian_fromBlocks_prod (m₁ := (0 : EuclideanSpace ℝ (Fin q)))
      (m₂ := (0 : EuclideanSpace ℝ (Fin n))) (S₁₁ := Gm) (S₂₂ := Rm) hGm hRm, blockPair_zero]
  have haff : Measurable fun w : EuclideanSpace ℝ (Fin q ⊕ Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) (stackM D) w
        + blockPair (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β) (0 : EuclideanSpace ℝ (Fin q)) :=
    (measurable_matAct (stackM D)).add_const _
  have hcomp : (fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
        (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1
            + be.2, be.1))
        ∘ ⇑(sumMeasEquivProd (ι₁ := Fin q) (ι₂ := Fin n))
      = ⇑(sumMeasEquivProd (ι₁ := Fin n) (ι₂ := Fin q))
        ∘ fun w : EuclideanSpace ℝ (Fin q ⊕ Fin n) =>
            Matrix.toEuclideanLin (𝕜 := ℝ) (stackM D) w
              + blockPair (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β)
                (0 : EuclideanSpace ℝ (Fin q)) := by
    funext w
    simp only [Function.comp_apply, sumMeasEquivProd_apply, stackM_apply]
    refine Prod.ext ?_ ?_
    · ext i
      simp [blockPair, add_assoc]
      ring
    · ext j
      simp [blockPair]
  rw [lmmJointLaw, hprod,
    Measure.map_map (measurable_jointMap D β)
      (sumMeasEquivProd (ι₁ := Fin q) (ι₂ := Fin n)).measurable,
    hcomp, ← Measure.map_map (sumMeasEquivProd (ι₁ := Fin n) (ι₂ := Fin q)).measurable haff,
    multivariateGaussian_map_affine (0 : EuclideanSpace ℝ (Fin q ⊕ Fin n))
      (Matrix.fromBlocks Gm 0 0 Rm) hdiag (stackM D)
      (blockPair (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β) (0 : EuclideanSpace ℝ (Fin q))),
    map_zero, zero_add, stackM_conj D Gm Rm hGmT]

/-- **Henderson's regression matrix**: the Gaussian conditioning mean matrix at the mixed-
model blocks is `G Zᵀ V⁻¹` (`Hen50`; `Rob91 §2`). -/
theorem condMeanMatrix_lmm (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: symmetric latent covariance; Hen50
    (hGm : Gmᵀ = Gm) :
    condMeanMatrix (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm)
      = Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ := by
  rw [condMeanMatrix, Matrix.transpose_mul, hGm]

/-- **M3b, BLUP = Gaussian conditioning** (`Hen75 §2`; `Rob91 §2`): the Gaussian mixed-model
joint disintegrates through the Gaussian conditional kernel — whose mean at `y` is the BLUP
`G Zᵀ V⁻¹ (y − Xβ)` (by `condMeanMatrix_lmm` and the kernel's `@[simp]` spec) and whose
covariance is the prediction-error covariance `G − G Zᵀ V⁻¹ Z G`. -/
theorem compProd_lmmJointLaw (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (Gm : Matrix (Fin q) (Fin q) ℝ) (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: genuine covariance parameters; Hen75 §2
    (hGm : Gm.PosSemidef) (hRm : Rm.PosSemidef)
    -- USER-INPUT: nondegenerate marginal covariance V = ZGZᵀ + R; Hen75 §2
    (hV : (D.Z * Gm * D.Zᵀ + Rm).PosDef) :
    lmmLaw D β (multivariateGaussian 0 Gm) (multivariateGaussian 0 Rm)
        ⊗ₘ gaussianCondKernel (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β) 0
            (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm) Gm
      = lmmJointLaw D β (multivariateGaussian 0 Gm) (multivariateGaussian 0 Rm) := by
  rw [lmmLaw_multivariateGaussian D β Gm Rm hGm hRm,
    compProd_gaussianCondKernel (Matrix.toEuclideanLin (𝕜 := ℝ) D.X β) 0
      (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm) Gm (posSemidef_lmmJoint D Gm Rm hGm hRm) hV,
    lmmJointLaw_eq_blockGaussian D β Gm Rm hGm hRm]

/-- The mean-squared prediction risk of the linear predictor `b̂ = A (Y − Xβ)` — for
**arbitrary** latent laws (no Gaussianity). -/
noncomputable def blupRisk (D : LMMDesign n p q)
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin q) (Fin n) ℝ) : ℝ :=
  ∫ be, ‖be.1 - Matrix.toEuclideanLin (𝕜 := ℝ) A
      (Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2)‖ ^ 2 ∂(G.prod R)

/-- **M3c, the variational BLUP identity** (Harville 1976; `Rob91 §3`): for centered
second-moment latent laws, the prediction risk of any linear `A` exceeds that of
`A* = G Zᵀ V⁻¹` by exactly `tr((A − A*) V (A − A*)ᵀ)` — completing the square in the
matrix trace. No Gaussianity. -/
theorem blupRisk_eq_add (D : LMMDesign n p q)
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure G] [IsProbabilityMeasure R]
    -- USER-INPUT: centered latent effects and noise with second moments; Rob91 §3
    (hGc : meanVec G = 0) (hRc : meanVec R = 0)
    (hG2 : MemLp id 2 G) (hR2 : MemLp id 2 R)
    -- USER-INPUT: nondegenerate marginal covariance; Rob91 §3
    (hV : (D.Z * covMatrix G * D.Zᵀ + covMatrix R).PosDef)
    (A : Matrix (Fin q) (Fin n) ℝ) :
    blupRisk D G R A
      = blupRisk D G R
            (covMatrix G * D.Zᵀ * (D.Z * covMatrix G * D.Zᵀ + covMatrix R)⁻¹)
          + ((A - covMatrix G * D.Zᵀ * (D.Z * covMatrix G * D.Zᵀ + covMatrix R)⁻¹)
              * (D.Z * covMatrix G * D.Zᵀ + covMatrix R)
              * (A - covMatrix G * D.Zᵀ
                  * (D.Z * covMatrix G * D.Zᵀ + covMatrix R)⁻¹)ᵀ).trace := by
  sorry

/-- **BLUP is optimal** (`Rob91` — "that BLUP is a good thing"): `A* = G Zᵀ V⁻¹` minimizes
the prediction risk among all linear predictors. -/
theorem blupRisk_le (D : LMMDesign n p q)
    (G : Measure (EuclideanSpace ℝ (Fin q))) (R : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure G] [IsProbabilityMeasure R]
    -- USER-INPUT: centered, second moments, nondegenerate V; Rob91 §3
    (hGc : meanVec G = 0) (hRc : meanVec R = 0)
    (hG2 : MemLp id 2 G) (hR2 : MemLp id 2 R)
    (hV : (D.Z * covMatrix G * D.Zᵀ + covMatrix R).PosDef)
    (A : Matrix (Fin q) (Fin n) ℝ) :
    blupRisk D G R
        (covMatrix G * D.Zᵀ * (D.Z * covMatrix G * D.Zᵀ + covMatrix R)⁻¹)
      ≤ blupRisk D G R A := by
  sorry

end StatLean.StatisticalModels.MixedEffects
