import StatLean.PointEstimation.LinearModel.LeastSquares
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Regression coefficients and random designs

In the regression form of the linear model the mean vector is `ξ = θ A` for a known design
matrix `A` of full row rank; the least-squares estimator of the coefficient vector is
`θ̂(y) = y Aᵀ (A Aᵀ)⁻¹`. This file records:

* `designMean`, `designSpace`, `lseCoeff`, `regressionModel` — the regression form and its
  least-squares estimator, together with the bridge `designMean_lseCoeff` identifying
  `θ̂` with the least-squares estimator of the mean vector;
* `isUMVU_regression_coeff` — every linear function of `θ̂` is UMVU for the corresponding
  linear function of `θ`;
* `covariance_regression_coeff` — the covariance matrix of `θ̂` is `σ² (A Aᵀ)⁻¹`;
* `not_exists_blue_of_known_design_moment` — when the design is itself random with a law
  whose second moment `E(A Aᵀ)` is known, no best linear unbiased estimator exists
  (DEFERRAL-ELIGIBLE, see below).

**Reference.** Classical regression theory and its random-design variants; original sources
in the bibliographic comments below.

**Proof formalization notes.**
* *Row convention.* Coefficient vectors multiply the design on the left, `ξ = θ A` with `A`
  of size `s × n`, matching `Matrix.vecMul`; `lseCoeff` is the total function
  `y ↦ y Aᵀ (A Aᵀ)⁻¹`, which is junk (zero) when `A A ᵀ` is singular, i.e. exactly when the
  full-row-rank hypothesis fails.
* *Measurable carrier for a random design.* `Matrix` is a non-reducible definition and
  carries no `MeasurableSpace` instance, so a random design is carried by the plain
  function type `DesignSample s n = Fin s → Fin n → ℝ` (product measurable structure) and
  read as a matrix through `Matrix.of`.
* *Random-design model.* The joint law of design and response is `Q ⊗ₘ K p`: a fixed design
  law `Q` (the same under every parameter) and a Markov kernel `K p` giving the conditional
  law of the response, constrained only through its conditional mean and covariance. This
  keeps the moments-only spirit of the fixed-design theorem while making "expectations are
  taken over the joint distribution" precise.
* *The nonexistence clause is a planned debt.* Its classical proof is delegated to
  exercises, and the printed statement omits the nondegeneracy needed to make it true — for
  an almost surely constant design the fixed-design theorem *does* provide a best linear
  unbiased estimator. The statement below therefore carries an explicit nondegeneracy
  hypothesis on the design law; whether that hypothesis is exactly the right one is part of
  the deferred content, and the statement is to be renegotiated when the debt is closed.

**Bibliographic comments.** The regression form of the linear model and the covariance
formula `σ²(A Aᵀ)⁻¹` are classical, going back to C. F. Gauss (*Theoria combinationis
observationum erroribus minimis obnoxiae*, 1821/1823) and A. A. Markov
(*Wahrscheinlichkeitsrechnung*, Teubner, 1912); see H. Scheffé (*The Analysis of Variance*,
Wiley, 1959), W. Kruskal ("When are Gauss–Markov and least squares estimators identical?"
in *Essays in Probability and Statistics*, 1965) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973). The failure of best linear unbiased
estimation for random regressors with known second moment is due to J. P. Shaffer
("The Gauss–Markov theorem and random regressors," *Amer. Statist.* **45** (1991),
269–273); its relation to ancillarity and admissibility was investigated by L. D. Brown
("An ancillarity paradox which appears in multiple linear regression," *Ann. Statist.*
**18** (1990), 471–493).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix

namespace StatLean.PointEstimation

/-- The regression parameter: the coefficient vector together with the unknown positive
variance (the same packaging as in the canonical model). -/
abbrev RegressionParam (k : ℕ) : Type := (Fin k → ℝ) × PosVar

/-- Random designs are carried by the plain function type `Fin k → Fin l → ℝ`, which has
the product measurable structure, and are read as matrices through `Matrix.of`: `Matrix` is
a non-reducible definition and carries no `MeasurableSpace` instance. -/
abbrev DesignSample (k l : ℕ) : Type := Fin k → Fin l → ℝ

variable {s n : ℕ}

/-! ## The regression form -/

/-- The **regression mean vector** `ξ = θ A` of a design matrix `A`. -/
noncomputable def designMean (A : Matrix (Fin s) (Fin n) ℝ) (θ : Fin s → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) (θ ᵥ* A)

/-- The **mean subspace of a design**: the span of the rows of `A`, over which the
regression mean vector ranges. -/
noncomputable def designSpace (A : Matrix (Fin s) (Fin n) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i : Fin s =>
    ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) (A i)))

/-- The **least-squares estimator of the regression coefficients**,
`θ̂(y) = y Aᵀ (A Aᵀ)⁻¹`. For a design that does not have full row rank the matrix `A Aᵀ` is
singular, its Mathlib inverse is `0`, and this definition returns the junk value `0`; every
theorem below carries the full-row-rank hypothesis. -/
noncomputable def lseCoeff (A : Matrix (Fin s) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Fin s → ℝ :=
  ((fun i => y i) ᵥ* Aᵀ) ᵥ* (A * Aᵀ)⁻¹

/-- The **regression model**: independent normal observations with mean vector `θ A` and
unknown common variance. -/
noncomputable def regressionModel (A : Matrix (Fin s) (Fin n) ℝ) (p : RegressionParam s) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  gaussianVector (designMean A p.1) p.2.1

/-- The regression mean vector lies in the span of the rows of the design. -/
theorem designMean_mem_designSpace (A : Matrix (Fin s) (Fin n) ℝ) (θ : Fin s → ℝ) :
    designMean A θ ∈ designSpace A := by
  rw [designMean, designSpace]
  have hsum : (θ ᵥ* A) = ∑ i, θ i • A i := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  have he : (WithLp.toLp 2 (∑ i, θ i • A i) : EuclideanSpace ℝ (Fin n))
      = ∑ i, θ i • (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)) :=
    (map_sum (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (fun i => θ i • A i) Finset.univ).trans
      (Finset.sum_congr rfl (fun i _ => map_smul _ (θ i) (A i)))
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- A design of full row rank identifies its coefficient vector. -/
theorem injective_designMean {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) :
    Function.Injective (designMean A) := by
  have hli : LinearIndependent ℝ A.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← Matrix.rank_eq_finrank_span_row, hA]
    simp
  have hvec : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hli
  intro θ φ h
  exact hvec ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.injective h)

/-- **The coefficient LSE is the mean LSE**: applying the design to `θ̂(y)` returns the
orthogonal projection of `y` onto the mean subspace. This is the bridge that transports the
optimality statements from the mean vector to the regression coefficients. -/
theorem designMean_lseCoeff {A : Matrix (Fin s) (Fin n) ℝ}
    [(designSpace A).HasOrthogonalProjection]
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) (y : EuclideanSpace ℝ (Fin n)) :
    designMean A (lseCoeff A y) = lse (designSpace A) y := by
  classical
  have hli : LinearIndependent ℝ A.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← Matrix.rank_eq_finrank_span_row, hA]; simp
  have hvecA : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hli
  have hunit : IsUnit (A * Aᵀ) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro x z h
    have hx0 : (x - z) ᵥ* (A * Aᵀ) = 0 := by rw [Matrix.sub_vecMul, sub_eq_zero]; exact h
    have hself : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A) = 0 := by
      have e1 : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A)
          = ((x - z) ᵥ* A) ⬝ᵥ (Aᵀ *ᵥ (x - z)) := by rw [Matrix.mulVec_transpose]
      rw [e1, Matrix.dotProduct_mulVec,
        show ((x - z) ᵥ* A) ᵥ* Aᵀ = (x - z) ᵥ* (A * Aᵀ) from Matrix.vecMul_vecMul _ _ _,
        hx0, zero_dotProduct]
    have hxA : (x - z) ᵥ* A = 0 := by rw [← dotProduct_self_eq_zero]; exact hself
    have hxz : x - z = 0 := hvecA (by simpa using hxA)
    exact sub_eq_zero.mp hxz
  have hunitdet : IsUnit (A * Aᵀ).det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact hunit
  have hAAT_symm : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hinv_symm : ((A * Aᵀ)⁻¹)ᵀ = (A * Aᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAAT_symm]
  set c := lseCoeff A y with hc_def
  have hnormal : A *ᵥ (c ᵥ* A) = A *ᵥ (fun i => y i) := by
    have hcv : c = (A *ᵥ (fun i => y i)) ᵥ* (A * Aᵀ)⁻¹ := by
      rw [hc_def, lseCoeff, Matrix.vecMul_transpose]
    calc A *ᵥ (c ᵥ* A)
        = A *ᵥ (Aᵀ *ᵥ c) := by rw [Matrix.mulVec_transpose]
      _ = (A * Aᵀ) *ᵥ c := by rw [Matrix.mulVec_mulVec]
      _ = (A * Aᵀ) *ᵥ ((A *ᵥ (fun i => y i)) ᵥ* (A * Aᵀ)⁻¹) := by rw [hcv]
      _ = (A * Aᵀ) *ᵥ (((A * Aᵀ)⁻¹)ᵀ *ᵥ (A *ᵥ (fun i => y i))) := by rw [Matrix.mulVec_transpose]
      _ = (A * Aᵀ) *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ (fun i => y i))) := by rw [hinv_symm]
      _ = ((A * Aᵀ) * (A * Aᵀ)⁻¹) *ᵥ (A *ᵥ (fun i => y i)) := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ (A *ᵥ (fun i => y i)) := by rw [Matrix.mul_nonsing_inv _ hunitdet]
      _ = A *ᵥ (fun i => y i) := by rw [Matrix.one_mulVec]
  have hgen : ∀ r : Fin s,
      ⟪y - designMean A c, (WithLp.toLp 2 (A r) : EuclideanSpace ℝ (Fin n))⟫_ℝ = 0 := by
    intro r
    have hsub : (y - designMean A c : EuclideanSpace ℝ (Fin n))
        = WithLp.toLp 2 ((fun i => y i) - c ᵥ* A) := by
      rw [designMean]
      exact (map_sub (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm _ _)
    rw [hsub]
    show (A r) ⬝ᵥ star ((fun i => y i) - c ᵥ* A) = 0
    have hstar : star ((fun i => y i) - c ᵥ* A) = (fun i => y i) - c ᵥ* A := by
      funext i; exact star_trivial _
    rw [hstar, dotProduct_sub]
    have h1 : (A r) ⬝ᵥ (fun i => y i) = (A *ᵥ (fun i => y i)) r := rfl
    have h2 : (A r) ⬝ᵥ (c ᵥ* A) = (A *ᵥ (c ᵥ* A)) r := rfl
    rw [h1, h2, hnormal, sub_self]
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (designMean_mem_designSpace A c) (fun w hw => ?_)).symm
  induction hw using Submodule.span_induction with
  | mem w hwm => obtain ⟨r, rfl⟩ := hwm; exact hgen r
  | zero => exact inner_zero_right _
  | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
  | smul t a _ ha => rw [real_inner_smul_right, ha, mul_zero]

/-! ## Optimality and covariance of the coefficient estimator -/

/-- **Optimality of the regression coefficient estimator**: every linear function of the
least-squares coefficients is the UMVU estimator of the corresponding linear function of the
coefficients. -/
theorem isUMVU_regression_coeff {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s)
    -- USER-INPUT: more observations than coefficients (`s < n`); standing dimension
    -- condition of the model, without which the variance is not estimable
    (hsn : s < n)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (c : Fin s → ℝ) :
    IsUMVU (regressionModel A) (fun p => ∑ i, c i * p.1 i)
      (fun y => ∑ i, c i * lseCoeff A y i) := by
  sorry

/-- **Covariance of the regression coefficient estimator**: `cov(θ̂) = σ² (A Aᵀ)⁻¹`. -/
theorem covariance_regression_coeff {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) (p : RegressionParam s) (i j : Fin s) :
    covariance (fun y => lseCoeff A y i) (fun y => lseCoeff A y j) (regressionModel A p)
      = (p.2.1 : ℝ) * (A * Aᵀ)⁻¹ i j := by
  sorry

/-! ## Random designs -/

/-- A **linear estimator for a random design**: linear in the response vector, with
coefficients allowed to depend on the observed design. -/
def IsRandomDesignLinear (δ : DesignSample s n × EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ c : DesignSample s n → EuclideanSpace ℝ (Fin n), ∀ a y, δ (a, y) = ⟪c a, y⟫_ℝ

/-- The **joint model of design and response**: the design has the parameter-free law `Q`,
and given the design the response follows the kernel `K p`. -/
noncomputable def randomDesignModel (Q : Measure (DesignSample s n))
    (K : RegressionParam s → Kernel (DesignSample s n) (EuclideanSpace ℝ (Fin n)))
    (p : RegressionParam s) : Measure (DesignSample s n × EuclideanSpace ℝ (Fin n)) :=
  Q ⊗ₘ K p

/-- A **best linear unbiased estimator** for a random design: linear, unbiased,
square-integrable, and of minimal variance at every parameter among the linear unbiased
estimators. -/
def IsBLUERandomDesign
    (P : RegressionParam s → Measure (DesignSample s n × EuclideanSpace ℝ (Fin n)))
    (g : RegressionParam s → ℝ)
    (δ : DesignSample s n × EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsRandomDesignLinear δ ∧ IsUnbiased P g δ ∧ MemEstL2 P δ ∧
    ∀ δ', IsRandomDesignLinear δ' → IsUnbiased P g δ' → MemEstL2 P δ' →
      ∀ p, variance δ (P p) ≤ variance δ' (P p)

/-- **Nonexistence of a best linear unbiased estimator for a random design with known second
moment.**

DEFERRAL-ELIGIBLE (planned debt): the classical proof of this clause is delegated to
exercises, and the printed statement omits the nondegeneracy that makes it true — for an
almost surely constant design the fixed-design theorem does supply a best linear unbiased
estimator. The nondegeneracy hypothesis below is our reading of the intended scope; if it
turns out to be insufficient the statement is renegotiated when the debt is discharged. -/
theorem not_exists_blue_of_known_design_moment
    (Q : Measure (DesignSample s n)) [IsProbabilityMeasure Q]
    (K : RegressionParam s → Kernel (DesignSample s n) (EuclideanSpace ℝ (Fin n)))
    [∀ p, IsMarkovKernel (K p)]
    -- USER-INPUT: given the design, the response has mean `θ A` (the regression form,
    -- now conditional on the observed design)
    (hmean : ∀ p a i, ∫ y, y i ∂(K p a) = designMean (Matrix.of a) p.1 i)
    -- USER-INPUT: given the design, the response coordinates are uncorrelated with common
    -- variance σ² (the moment assumptions, now conditional)
    (hcov : ∀ p a i j, covariance (fun y => y i) (fun y => y j) (K p a)
      = if i = j then (p.2.1 : ℝ) else 0)
    -- USER-INPUT: the design is genuinely random — its law is not a point mass; a
    -- deterministic design falls under the fixed-design theorem instead
    (hQ : ∀ a₀, Q ≠ Measure.dirac a₀)
    -- USER-INPUT: a nontrivial linear functional of the coefficients is estimated
    {c : Fin s → ℝ} (hc : c ≠ 0) :
    ¬ ∃ δ, IsBLUERandomDesign (randomDesignModel Q K) (fun p => ∑ i, c i * p.1 i) δ := by
  sorry

end StatLean.PointEstimation
