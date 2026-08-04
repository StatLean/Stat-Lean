import StatLean.StatisticalModels.Longitudinal.Sandwich

/-!
# Godambe optimality — the true covariance is the optimal working covariance

**L3.** Among GEE working covariances, choosing `V = Σ` (the truth) minimizes the exact
sandwich covariance in the Loewner order:
$$B^{-1} M B^{-1} \succeq K^{-1}, \qquad K = \sum_i D_i^\top \Sigma_i^{-1} D_i,$$
with equality at `V = Σ`. Stated as a pure matrix theorem (the probabilistic content — that
`B⁻¹MB⁻¹` and `K⁻¹` are the two candidate estimator covariances — is
`Sandwich.covMatrix_geeEstimator`); the cross-term cancellation `E[U U^{*\top}] = B` that
powers the classical proof appears here as the algebraic identity
`∑ Dᵀ V⁻¹ Σ Σ⁻¹ D = B` inside the stacked-covariance PSD argument.

**Reference.** V. P. Godambe, "An optimum property of regular maximum likelihood
estimation," *Ann. Math. Statist.* **31** (1960), 1208–1211 (`God60`); V. P. Godambe and
C. C. Heyde, "Quasi-likelihood and optimal estimation," *Int. Statist. Rev.* **55** (1987),
231–244 (verify §); `LZ86` (remark after Theorem 2); GMM lineage: L. P. Hansen,
*Econometrica* **50** (1982).

**Proof formalization notes.** Route: the block matrix
`fromBlocks M B Bᵀ K` is PSD (it is the covariance of the stacked scores `(U, U*)` — proved
matricially: it equals `∑ᵢ Wᵢ Σᵢ Wᵢᵀ`-type conjugations with
`Wᵢ = [Dᵢᵀ Vᵢ⁻¹; Dᵢᵀ Σᵢ⁻¹]`-stacked, each PSD by
`Matrix.PosSemidef.mul_mul_conjTranspose_same` and PSD sums); then the Schur-complement
characterization `Matrix.PosSemidef.fromBlocks₁₁`-family (with `K` PosDef) yields
`M − B K⁻¹ Bᵀ ⪰ 0`; congruence by `B⁻¹` (PSD is congruence-stable — again
`mul_mul_conjTranspose_same`) gives the claim, **deliberately avoiding matrix
inverse-monotonicity** (absent from Mathlib). Relation to the Gauss–Markov theorem
(`PointEstimation.LinearModel.GaussMarkov.gauss_markov`, the scalar subspace form of the
same Loewner argument): noted here, no import.

**Bibliographic comments.** Godambe (1960) proved the score is the optimal estimating
function; the working-covariance corollary for GEE is Liang–Zeger's remark; the
finite-sample matrix form here is the standard textbook argument made exact.
-/

open Matrix

namespace StatLean.StatisticalModels.Longitudinal

variable {N m q : ℕ}

/-- The **Godambe information** `K = ∑ Dᵢᵀ Σᵢ⁻¹ Dᵢ` — the bread at the true covariance
(`God60`). -/
noncomputable def godambeInfo (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (Covs i)⁻¹ * D i

/-- The stacked-score covariance block matrix is PSD — the matricial form of
"`Cov (U, U*)` is a covariance" with the cross-block `B` (the Godambe cancellation). -/
theorem posSemidef_fromBlocks_meat_bread (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: true covariances positive definite; God60
    (hΣ : ∀ i, (Covs i).PosDef)
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    (Matrix.fromBlocks (geeMeat D V Covs) (geeBread D V)
      (geeBread D V)ᵀ (godambeInfo D Covs)).PosSemidef := by
  sorry

/-- **L3, Godambe optimality** (`God60`; `LZ86` remark after Thm 2): the exact sandwich
dominates the inverse Godambe information in the Loewner order — no working covariance
beats the truth. -/
theorem godambe_optimality (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: true covariances positive definite; God60
    (hΣ : ∀ i, (Covs i).PosDef)
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i)
    -- USER-INPUT: identified designs — Godambe information and bread invertible; God60
    (hK : (godambeInfo D Covs).PosDef) (hB : IsUnit (geeBread D V).det) :
    ((geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹
      - (godambeInfo D Covs)⁻¹).PosSemidef := by
  sorry

/-- **Equality at the truth**: with `V = Σ` the sandwich collapses to `K⁻¹`. -/
theorem sandwich_eq_inv_godambeInfo_of_true (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: identified design at the truth; God60
    (hK : IsUnit (godambeInfo D Covs).det)
    -- USER-INPUT: symmetric true covariances; LZ86 §2
    (hCovsymm : ∀ i, (Covs i)ᵀ = Covs i) :
    (geeBread D Covs)⁻¹ * geeMeat D Covs Covs * (geeBread D Covs)⁻¹
      = (godambeInfo D Covs)⁻¹ := by
  sorry

end StatLean.StatisticalModels.Longitudinal
