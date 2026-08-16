import StatLean.StatisticalModels.FactorModels.Rotation
import StatLean.StatisticalModels.Identifiability.Transfer

/-!
# What a factor model does and does not identify

The rotational indeterminacy of `FactorModels.Rotation` is exactly an identifiability
failure, and it is stated here against the library's own predicates
(`StatLean.PointEstimation.Identifiable` and `StatisticalModels.IdentifiesTarget`) — no new
notion of identifiability is introduced.

**Not identified — the loadings.**

* `loadingModel μ Ψ` — the normal factor model with `μ` and `Ψ` held fixed and standardized
  factors, indexed by the loading matrix alone;
* `loadingModel_mul_orthogonal` — `Λ` and `Λ Q` index the *same* law for every orthogonal
  `Q` (for `q ≥ 2` these are genuine rotations; `Q = -I` is the sign flip that already
  defeats identifiability at `q = 1`);
* **`not_identifiable_loadingModel`** — hence `¬ Identifiable (loadingModel μ Ψ)` as soon as
  `p, q ≥ 1`, with an explicit witness pair, and the model-level companion
  `not_identifiable_properGaussianFactorModel`.

**Identified — the covariance decomposition.**

* **`identifiesTarget_loadingModel_commonCovariance`** — `Λ Λᵀ` *is* identified;
* `identifiesTarget_factorCovariance` and `identifiesTarget_mean` — over proper parameters,
  `Σ = Λ Φ Λᵀ + Ψ` and `μ` are identified. (Splitting `Σ` into `Λ Φ Λᵀ` and `Ψ` is a further
  question — the counting condition of `BKM` Eq. (3.50)–(3.51) — and is not claimed here.)

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §3.12.1, pp. 64–65 and
Eq. (3.50)–(3.51) (the parameter count); §2.11, Eq. (2.24)–(2.26) and §3.13.1 (rotation);
§3.3, p. 50 (`Λ′Ψ⁻¹Λ` diagonal "removes the freedom to arbitrarily rotate `Λ`") (`BKM`);
E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §1.5
(identifiability of a parametrization) (`TPE2 §1.5`).

**Proof formalization notes.** The negative results are `Rotation.gaussianFactorModel_rotateParams`
plus an explicit witness (the all-ones loading matrix and its negative, distinct because
`p, q ≥ 1` and `ℝ` has characteristic zero); the positive ones are
`Identifiability.identifiesTarget_of_rep` at the representing functional `covMatrix`
(resp. `meanVec`), evaluated through `Gaussian.covMatrix_gaussianFactorModel`.
*Junk values:* the positive results are stated over the **subtype of proper parameters**, and
this is not cosmetic — at a non-PSD `Φ` the Gaussian collapses to a Dirac and the law no
longer determines `factorCovariance` (two parameters with `Φ = 0` and with a non-PSD `Φ`
share a law but not a target), so the unrestricted statement is **false**.
*Book vs Lean:* `BKM` treats identifiability by counting free parameters
(Eq. (3.50)–(3.51)); the counting condition is necessary but not sufficient and is not
formalized here — what is formalized is the exact indeterminacy group and the identified
functional.

**Bibliographic comments.** The rotation problem is Thurstone's (1947); the modern
identification-by-restriction treatments (`Λ′Ψ⁻¹Λ` diagonal, or a triangular `Λ`) are
surveyed in `BKM` §3.3 and §3.12.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels StatLean.PointEstimation

variable {p q : ℕ}

/-! ### The loading-indexed model -/

/-- The **normal factor model indexed by its loadings**, with the mean `μ`, standardized
factors (`Φ = I`, `BKM` Eq. (3.2)) and the specific-factor covariance `Ψ` held fixed. This is
the family in which "the loadings are not identified" is a statement about a statistical
model rather than about matrices. -/
noncomputable def loadingModel (p q : ℕ) (μ : EuclideanSpace ℝ (Fin p))
    (Ψ : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin q) ℝ → Measure (EuclideanSpace ℝ (Fin p)) :=
  fun Λ => gaussianFactorModel p q ⟨μ, Λ, 1, Ψ⟩

/-- The loading model is the normal law with covariance `Λ Λᵀ + Ψ` (`BKM` Eq. (3.5)). -/
theorem loadingModel_eq_multivariateGaussian (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) :
    loadingModel p q μ Ψ Λ = multivariateGaussian μ (Λ * Λᵀ + Ψ) := by
  sorry

/-! ### The loadings are not identified -/

/-- **The rotational indeterminacy, model form** (`BKM` §2.11, Eq. (2.24)–(2.26); §3.13.1):
`Λ` and `Λ Q` index the *same* law for every orthogonal `Q`. For `q ≥ 2` these include
genuine rotations; `Q = -I` is the sign flip below. -/
theorem loadingModel_mul_orthogonal (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    loadingModel p q μ Ψ (Λ * Q) = loadingModel p q μ Ψ Λ := by
  sorry

/-- **The sign flip** — the `q = 1` instance of the rotational indeterminacy, and the witness
used below at every `q`. -/
theorem loadingModel_neg (μ : EuclideanSpace ℝ (Fin p)) {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) :
    loadingModel p q μ Ψ (-Λ) = loadingModel p q μ Ψ Λ := by
  sorry

/-- **HEADLINE (negative) — the loadings of a factor model are not identifiable**
(`BKM` §3.12.1, pp. 64–65): with at least one observed variable and at least one factor, two
distinct loading matrices index the same observed law. Stated against the library predicate
`StatLean.PointEstimation.Identifiable`. -/
theorem not_identifiable_loadingModel (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef)
    -- USER-INPUT: a nondegenerate model — at least one observed variable and one factor;
    -- at `p = 0` or `q = 0` there is only one loading matrix and the model is vacuously
    -- identifiable; BKM §3.12.1
    (hp : 0 < p) (hq : 0 < q) :
    ¬ Identifiable (loadingModel p q μ Ψ) := by
  sorry

/-! ### What *is* identified -/

/-- **HEADLINE (positive) — the common covariance is identified**: `Λ Λᵀ` is a functional of
the observed law even though `Λ` is not (`BKM` §3.12.1). -/
theorem identifiesTarget_loadingModel_commonCovariance (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) :
    IdentifiesTarget (loadingModel p q μ Ψ) fun Λ : Matrix (Fin p) (Fin q) ℝ => Λ * Λᵀ := by
  sorry

/-- The full covariance `Λ Λᵀ + Ψ` is identified in the loading model. -/
theorem identifiesTarget_loadingModel_covariance (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) :
    IdentifiesTarget (loadingModel p q μ Ψ)
      fun Λ : Matrix (Fin p) (Fin q) ℝ => Λ * Λᵀ + Ψ := by
  sorry

/-! ### The model over the full (proper) parameter space

`gaussianFactorModel` is only a `BKM`-model at proper parameters — at a non-PSD `Φ` or `Ψ`
the `multivariateGaussian` junk value (a Dirac mass) takes over and the law stops determining
`factorCovariance`. The identified-target statements are therefore over the subtype. -/

/-- The normal factor model restricted to **proper** parameter tuples. -/
noncomputable def properGaussianFactorModel (p q : ℕ) :
    {P : FactorParams p q // IsProperFactorParams P} → Measure (EuclideanSpace ℝ (Fin p)) :=
  fun P => gaussianFactorModel p q P.1

/-- **`Σ = Λ Φ Λᵀ + Ψ` is identified** — it is the covariance matrix of the observed law
(`BKM` Eq. (3.12), general `Φ`). -/
theorem identifiesTarget_factorCovariance :
    IdentifiesTarget (properGaussianFactorModel p q)
      fun P : {P : FactorParams p q // IsProperFactorParams P} => factorCovariance P.1 := by
  sorry

/-- **`μ` is identified** — it is the mean vector of the observed law (`BKM` Eq. (3.5)). -/
theorem identifiesTarget_mean :
    IdentifiesTarget (properGaussianFactorModel p q)
      fun P : {P : FactorParams p q // IsProperFactorParams P} => P.1.μ := by
  sorry

/-- **The parameter tuple itself is not identified** (`BKM` §3.12.1, pp. 64–65) — the
model-level companion of `not_identifiable_loadingModel`. -/
theorem not_identifiable_properGaussianFactorModel
    -- USER-INPUT: a nondegenerate model — at least one observed variable and one factor;
    -- BKM §3.12.1
    (hp : 0 < p) (hq : 0 < q) :
    ¬ Identifiable (properGaussianFactorModel p q) := by
  sorry

end StatLean.StatisticalModels.FactorModels
