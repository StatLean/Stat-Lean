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
  sorry

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
  sorry

/-- **Henderson's regression matrix**: the Gaussian conditioning mean matrix at the mixed-
model blocks is `G Zᵀ V⁻¹` (`Hen50`; `Rob91 §2`). -/
theorem condMeanMatrix_lmm (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: symmetric latent covariance; Hen50
    (hGm : Gmᵀ = Gm) :
    condMeanMatrix (D.Z * Gm * D.Zᵀ + Rm) (D.Z * Gm)
      = Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ := by
  sorry

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
  sorry

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
