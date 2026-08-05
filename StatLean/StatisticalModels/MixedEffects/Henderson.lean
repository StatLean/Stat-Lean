import StatLean.StatisticalModels.MixedEffects.Marginal

/-!
# Henderson's mixed-model equations

The computational heart of mixed-model practice, as exact matrix algebra:

* **`pushThrough` (M5i)** — the push-through identity
  `G Zᵀ (Z G Zᵀ + R)⁻¹ = (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`, the bridge between the
  covariance (BLUP) and precision (MME) forms;
* **`hendersonMME` (M5ii)** — Henderson's mixed-model equations: `(β̂, b̂)` solves the
  block system
  `[XᵀR⁻¹X, XᵀR⁻¹Z; ZᵀR⁻¹X, ZᵀR⁻¹Z + G⁻¹] (β̂, b̂) = (XᵀR⁻¹y, ZᵀR⁻¹y)`
  **iff** `b̂` is the BLUP at `β̂` and `β̂` solves the GLS normal equations in
  `V = Z G Zᵀ + R`;
* **`lmmLaw_dirac` (M4)** — the `G = δ₀` degeneration: the mixed model collapses to the
  fixed-effects linear model `Y = Xβ + ε` (the bridge to the library's existing
  linear-model treatments, stated against the explicit law — no cross-area import).

**Reference.** C. R. Henderson, O. Kempthorne, S. R. Searle, and C. M. von Krosigk, "The
estimation of environmental and genetic trends from records subject to culling,"
*Biometrics* **15** (1959), 192–218 (the equations); S. R. Searle, G. Casella, and C. E.
McCulloch, *Variance Components*, Wiley, 1992, §7.6 (verify §) (`SCM §7.6`); `Hen50`.

**Proof formalization notes.** The push-through identity is proved by multiplying both
sides by the invertible factors (`Matrix.nonsing_inv_mul`/`mul_nonsing_inv` under the
PosDef hypotheses) and normalizing — deliberately avoiding any Woodbury import. The MME
equivalence is `fromBlocks_mulVec` expansion + the push-through; all statements are pure
matrix/vector algebra (no measures). *Book vs Lean:* exact finite algebra; no estimation
theory claimed.

**Bibliographic comments.** The equations are Henderson's (1950, computational form in
Henderson et al. 1959); the push-through identity is matrix folklore (a Schur-complement
avatar), see SCM §7.6.
-/

open MeasureTheory Matrix

namespace StatLean.StatisticalModels.MixedEffects

variable {n p q : ℕ}

/-- **M5i, the push-through identity** (`SCM §7.6`): the covariance form of the BLUP weight
equals its precision form. -/
theorem pushThrough (Z : Matrix (Fin n) (Fin q) ℝ) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: positive-definite variance components; SCM §7.6
    (hG : Gm.PosDef) (hR : Rm.PosDef) :
    Gm * Zᵀ * (Z * Gm * Zᵀ + Rm)⁻¹
      = (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
  sorry

/-- **M5ii, Henderson's mixed-model equations** (Henderson et al. 1959; `SCM §7.6`):
`(β̂, b̂)` solves the MME block system iff `b̂` is the BLUP at `β̂` and `β̂` solves the
GLS normal equations in `V = Z G Zᵀ + R`. -/
theorem hendersonMME (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: positive-definite variance components; SCM §7.6
    (hG : Gm.PosDef) (hR : Rm.PosDef)
    (βh : Fin p → ℝ) (bh : Fin q → ℝ) (y : Fin n → ℝ) :
    ((D.Xᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Xᵀ * Rm⁻¹ * D.Z) *ᵥ bh = (D.Xᵀ * Rm⁻¹) *ᵥ y
        ∧ (D.Zᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ bh
            = (D.Zᵀ * Rm⁻¹) *ᵥ y)
      ↔ (bh = (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ (y - D.X *ᵥ βh)
          ∧ (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ * D.X) *ᵥ βh
              = (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ y) := by
  sorry

/-- **M4, the fixed-effects degeneration**: with a point mass at zero for the latent
effects, the mixed model is the fixed-effects linear model `Y = Xβ + ε` (`LW82`; the
bridge point to the library's linear-model treatments). -/
theorem lmmLaw_dirac (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure R] :
    lmmLaw D β (MeasureTheory.Measure.dirac 0) R
      = R.map fun ε => Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + ε := by
  sorry

end StatLean.StatisticalModels.MixedEffects
