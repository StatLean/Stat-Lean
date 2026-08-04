import StatLean.StatisticalModels.Longitudinal.Defs
import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix

/-!
# The exact finite-sample sandwich — bread, meat, and the GEE estimator's moments

The conditional-on-design (fixed-matrix) GEE layer: `N` independent subjects with fixed
per-subject Jacobians `D i`, working covariances `V i`, and response laws `Qs i` (true
covariances `Covs i`, unknown). Everything here is **exact at finite `N`** — zero asymptotics:

* `geeBread D V = ∑ Dᵢᵀ Vᵢ⁻¹ Dᵢ` and `geeMeat D V Covs = ∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ`;
* `geeScoreTotal` — the centered total estimating function; `geeEstimatorMap` — the linear
  GEE/WLS estimator `B⁻¹ ∑ Dᵢᵀ Vᵢ⁻¹ yᵢ`;
* `geeEstimatorMap_eq_add` — the linearization `β̂ = β₀ + B⁻¹ U(β₀)` (the workhorse);
* `meanVec_geeScoreTotal` / `meanVec_geeEstimator` — unbiasedness under the mean model;
* **`covMatrix_geeScoreTotal` (the meat)** and **`covMatrix_geeEstimator` (the exact
  bread-meat-bread sandwich)** `Cov(β̂) = B⁻¹ M B⁻¹` — `LZ86 §3` Eq. (13) with the
  asymptotics stripped away.

Cluster-independence additivity is not a separate statement: it *is* the
`covMatrix_map_sum_pi` engine (G-B1) these proofs instantiate.

**Reference.** K.-Y. Liang and S. L. Zeger, *Biometrika* **73** (1986), §3, Eq. (13) (the
robust/sandwich covariance) (`LZ86 §3`); bibliographic lineage: P. J. Huber (1967 Berkeley
Symposium) and H. White, *Econometrica* **48** (1980) (heteroscedasticity-consistent
covariance); FLW Ch. 13 (verify §).

**Proof formalization notes.** *Book vs Lean:* LZ86 state the sandwich asymptotically; here
the estimator is exactly linear in the data, so its mean and covariance are exact matrix
identities — a strict finite-sample strengthening. The design is conditional-on-covariates
(fixed matrices); the random-`X` version is a named future debt (D-M1). Working covariances
are required symmetric (USER-INPUT `hVsymm` — every covariance model is); invertibility of
the bread enters as `IsUnit (geeBread D V).det`.

**Bibliographic comments.** The bread–meat vocabulary is folklore for the
Huber–White–Liang–Zeger estimator; Godambe optimality of the weights is
`Longitudinal.Godambe`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.Longitudinal

open StatLean.StatisticalModels

variable {N m q : ℕ}

/-- The **bread** `B = ∑ Dᵢᵀ Vᵢ⁻¹ Dᵢ` (`LZ86 §3`). -/
noncomputable def geeBread (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (V i)⁻¹ * D i

/-- The **meat** `M = ∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ` (`LZ86 §3` Eq. (13)). -/
noncomputable def geeMeat (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (V i)⁻¹ * Covs i * (V i)⁻¹ * D i

/-- The centered total estimating function `U(β₀)(y) = ∑ Dᵢᵀ Vᵢ⁻¹ (yᵢ − Dᵢ β₀)`. -/
noncomputable def geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (y : Fin N → EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin q) :=
  ∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹)
    (y i - Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)

/-- The linear GEE/WLS estimator `β̂(y) = B⁻¹ ∑ Dᵢᵀ Vᵢ⁻¹ yᵢ` (`LZ86 §2`). -/
noncomputable def geeEstimatorMap (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (y : Fin N → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin q) :=
  Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V)⁻¹
    (∑ i, Matrix.toEuclideanLin (𝕜 := ℝ) ((D i)ᵀ * (V i)⁻¹) (y i))

/-- **Linearization** `β̂(y) = β₀ + B⁻¹ U(β₀)(y)` — the exact-moments workhorse. -/
theorem geeEstimatorMap_eq_add (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    -- USER-INPUT: invertible bread (identified design); LZ86 §2
    (hB : IsUnit (geeBread D V).det) (y : Fin N → EuclideanSpace ℝ (Fin m)) :
    geeEstimatorMap D V y
      = β₀ + Matrix.toEuclideanLin (𝕜 := ℝ) (geeBread D V)⁻¹ (geeScoreTotal D V β₀ y) := by
  sorry

/-- The total estimating function is centered under the mean model (the fixed-design form
of `gee_unbiased`). -/
theorem meanVec_geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: correct marginal means; LZ86 §2
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    -- USER-INPUT: integrable responses; LZ86 §3
    (hL1 : ∀ i, Integrable id (Qs i)) :
    meanVec ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = 0 := by
  sorry

/-- **Unbiasedness of the GEE estimator** (exact, finite `N`). -/
theorem meanVec_geeEstimator (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: correct marginal means; LZ86 §2
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    -- USER-INPUT: integrable responses; LZ86 §3
    (hL1 : ∀ i, Integrable id (Qs i))
    -- USER-INPUT: invertible bread; LZ86 §2
    (hB : IsUnit (geeBread D V).det) :
    meanVec ((Measure.pi Qs).map (geeEstimatorMap D V)) = β₀ := by
  sorry

/-- **The meat** (exact): the covariance of the total estimating function is
`∑ Dᵢᵀ Vᵢ⁻¹ Σᵢ Vᵢ⁻¹ Dᵢ` (`LZ86 §3` Eq. (13), finite-sample form). -/
theorem covMatrix_geeScoreTotal (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: true response covariances; LZ86 §3
    (hcov : ∀ i, covMatrix (Qs i) = Covs i)
    -- USER-INPUT: second moments; LZ86 §3
    (hL2 : ∀ i, MemLp id 2 (Qs i))
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    covMatrix ((Measure.pi Qs).map (geeScoreTotal D V β₀)) = geeMeat D V Covs := by
  sorry

/-- **The exact sandwich** `Cov(β̂) = B⁻¹ M B⁻¹` (`LZ86 §3` Eq. (13), exact at finite `N`). -/
theorem covMatrix_geeEstimator (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) (β₀ : EuclideanSpace ℝ (Fin q))
    (Qs : Fin N → Measure (EuclideanSpace ℝ (Fin m)))
    [∀ i, IsProbabilityMeasure (Qs i)]
    -- USER-INPUT: correct means, true covariances, second moments; LZ86 §2–3
    (hmean : ∀ i, meanVec (Qs i) = Matrix.toEuclideanLin (𝕜 := ℝ) (D i) β₀)
    (hcov : ∀ i, covMatrix (Qs i) = Covs i) (hL2 : ∀ i, MemLp id 2 (Qs i))
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i)
    -- USER-INPUT: invertible bread; LZ86 §2
    (hB : IsUnit (geeBread D V).det) :
    covMatrix ((Measure.pi Qs).map (geeEstimatorMap D V))
      = (geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹ := by
  sorry

end StatLean.StatisticalModels.Longitudinal
