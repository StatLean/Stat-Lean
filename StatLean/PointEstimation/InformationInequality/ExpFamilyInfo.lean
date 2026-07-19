import StatLean.PointEstimation.InformationInequality.Basic
import StatLean.PointEstimation.ExponentialFamily.Defs
import StatLean.PointEstimation.ExponentialFamily.MGF
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The Fisher information of an exponential family

In canonical form the log-density of an exponential family is `⟨η, T(x)⟩ − A(η)`, so its
score in the natural parameter is `T(x) − ∇A(η)`: the natural statistic, centered. The
information is therefore the *curvature of the log-partition function*, equivalently the
covariance of the natural statistic:
$$ I(\eta) = A''(\eta) \quad (\text{one-dimensional}), \qquad
   I(\eta)_{ij} = \frac{\partial^2 A}{\partial\eta_i\,\partial\eta_j}(\eta)
               = \operatorname{cov}_\eta\bigl(T_i, T_j\bigr) \quad (s\text{-dimensional}). $$

Contents:
* `ExpFamily.toParametricFamily` — the canonical family read as a family of densities
  `exp(⟨η, T(x)⟩ − A(η))` with respect to the reference measure, so that the score and the
  information of this area apply to it;
* `fisherInfo_expFamily` — the one-dimensional identity `I(η) = A''(η)`;
* `infoMatrix_expFamily` — the information matrix is the covariance matrix of the natural
  statistic.

**Reference.** Classical computation of the Fisher information of an exponential family in
its natural parametrization. Original sources in the bibliographic comments below.

**Proof formalization notes.**
* Both statements are given in the *natural* parametrization, where the score is
  `T − ∇A` and the identities are clean. The mean-value parametrization `τ = ∇A(η)` — in
  which the information is the *inverse* of the covariance matrix of `T`, and in dimension
  one `I(τ) = 1 / var_θ(T)` — follows by the reparametrization rule for the information
  (`fisherInfo_reparam` and its matrix analogue), since the Jacobian of `η ↦ τ(η)` is that
  same covariance matrix. This is a deliberate change of presentation, not of content.
* Smoothness of `A` is not assumed: it is forced by membership of `η` in the *interior* of
  the natural parameter set, where the log-partition function is analytic. That single
  membership hypothesis is therefore the only regularity input, and differentiability
  statements about `A` are consequences (proved in the exponential-family smoothness file),
  not hypotheses here.
* The density presentation `exp(⟨η, T x⟩ − A(η))` relative to `base` agrees with the
  member measure built by exponential tilting; where the reference measure is the zero
  measure both sides of the identities degenerate to `0` and the statements remain true.
* The `s`-dimensional statement is phrased entrywise, with the covariance of the coordinate
  statistics under the member measure, which is the form consumed by the multiparameter
  information inequality.

**Bibliographic comments.** The identification of the information of an exponential family
with the curvature of its cumulant function goes back to R. A. Fisher ("Theory of
statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925), 700–725) and to the
characterizations of exponential families by G. Darmois ("Sur les lois de probabilité à
estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935), 1265–1266), B. O. Koopman
("On distributions admitting a sufficient statistic," *Trans. Amer. Math. Soc.* **39**
(1936), 399–409) and E. J. G. Pitman ("Sufficient statistics and intrinsic accuracy,"
*Proc. Camb. Phil. Soc.* **32** (1936), 567–579). The matrix form of the information, and
its role in the multiparameter bound, are due to C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37**
(1945), 81–91); the convex-analytic treatment of the log-partition function is that of
L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [OpensMeasurableSpace V]

/-- The canonical exponential family **read as a family of densities**
`p_η(x) = exp(⟨η, T(x)⟩ − A(η))` relative to its reference measure, so that the score and
the Fisher information of this area apply to it directly. The densities are positive
everywhere, so the family trivially has a common support. -/
noncomputable def ExpFamily.toParametricFamily (E : ExpFamily 𝓧 V) : ParametricFamily 𝓧 V where
  density η x := Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)
  density_meas η := by
    have h : Continuous fun v : V => ⟪η, v⟫_ℝ := continuous_const.inner continuous_id
    exact ((h.measurable.comp E.stat_meas).sub measurable_const).exp
  density_nonneg _ _ := Real.exp_nonneg _

/-- **The information of a one-dimensional canonical exponential family is the curvature of
its log-partition function**: `I(η) = A''(η)`.

The score is the centered natural statistic `T − A'(η)`, so the information is the variance
of `T` under the member measure, which is the second derivative of `A`. In the mean-value
parametrization this becomes the reciprocal of that variance, by the reparametrization rule
for the information. -/
theorem fisherInfo_expFamily (E : ExpFamily 𝓧 ℝ) (η : ℝ)
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set;
    -- the classical condition under which the log-partition function is smooth (and hence
    -- the only regularity input of the statement)
    (hη : η ∈ interior E.natSet) :
    fisherInfo E.toParametricFamily E.base η = deriv (deriv E.logPartition) η := by
  have hηnat : η ∈ E.natSet := interior_subset hη
  have hmem : η ∈ interior (integrableExpSet E.stat E.base) := by
    rw [← E.natSet_eq_integrableExpSet]; exact hη
  -- inner product on ℝ is multiplication
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by rw [← real_inner_comm]; rfl
  -- the log-partition function is differentiable at `η`
  have hA : HasDerivAt E.logPartition (deriv E.logPartition η) η := by
    rw [E.logPartition_eq_cgf]
    exact (analyticAt_cgf hmem).differentiableAt.hasDerivAt
  -- derivative of the density in the parameter
  have hden_deriv : ∀ x, HasDerivAt (fun t => E.toParametricFamily.density t x)
      (E.toParametricFamily.density η x * (E.stat x - deriv E.logPartition η)) η := by
    intro x
    have hfun : (fun t : ℝ => ⟪t, E.stat x⟫_ℝ) = fun t => t * E.stat x :=
      funext fun t => hinner t (E.stat x)
    have h1 : HasDerivAt (fun t : ℝ => ⟪t, E.stat x⟫_ℝ) (E.stat x) η := by
      rw [hfun]; simpa using (hasDerivAt_id η).mul_const (E.stat x)
    have hlin : HasDerivAt (fun t : ℝ => ⟪t, E.stat x⟫_ℝ - E.logPartition t)
        (E.stat x - deriv E.logPartition η) η := h1.sub hA
    exact hlin.exp
  -- the score equals the centered natural statistic `T − A'(η)`
  have hscore_id : ∀ x, score E.toParametricFamily η x = E.stat x - deriv E.logPartition η := by
    intro x
    have hpos : (0 : ℝ) < E.toParametricFamily.density η x := Real.exp_pos _
    rw [score, (hden_deriv x).deriv, mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]
  have hPeq : E.toParametricFamily.toMeasure E.base η = E.P η := by
    rw [E.P_eq_withDensity hηnat]; rfl
  rw [fisherInfo]
  calc ∫ x, score E.toParametricFamily η x ^ 2 * E.toParametricFamily.density η x ∂E.base
      = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 * E.toParametricFamily.density η x ∂E.base
        := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hscore_id]
    _ = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 ∂(E.toParametricFamily.toMeasure E.base η) :=
        (integral_toMeasure_eq E.toParametricFamily E.base η
          (fun x => (E.stat x - deriv E.logPartition η) ^ 2)).symm
    _ = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 ∂(E.P η) := by rw [hPeq]
    _ = variance E.stat (E.P η) := by
        rw [variance_eq_integral E.stat_meas.aemeasurable, E.integral_stat_P hη]
    _ = iteratedDeriv 2 E.logPartition η := E.variance_stat_P hη
    _ = deriv (deriv E.logPartition) η := by rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- **The information matrix of a canonical exponential family is the covariance matrix of
its natural statistic**: `I(η)_{ij} = cov_η(T_i, T_j)`, equivalently the Hessian of the
log-partition function.

In the mean-value parametrization the information matrix is the *inverse* of this
covariance matrix, by the matrix reparametrization rule. -/
theorem infoMatrix_expFamily {s : ℕ} (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s))
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set
    (hη : η ∈ interior E.natSet) (i j : Fin s) :
    infoMatrix E.toParametricFamily E.base η i j
      = covariance (fun x => E.stat x i) (fun x => E.stat x j) (E.P η) := by
  -- TODO: sanctioned per-file escape. The coordinate score is `scoreVecᵢ = Tᵢ − ∂ᵢA(η)`,
  -- where the directional derivative `∂ᵢA(η) = deriv (fun t => A(η + t•eᵢ)) 0` equals the mean
  -- `E_η[Tᵢ]` by the directional-MGF identity: along the line `η + t•eᵢ`, `integral_exp_inner_P`
  -- gives `mgf Tᵢ (P η) t = exp(A(η + t•eᵢ) − A η)`, so `A(η + t•eᵢ) = cgf Tᵢ (P η) t + A η` on a
  -- neighborhood of `0` (needs `0 ∈ interior (integrableExpSet Tᵢ (P η))`, from `η ∈ interior
  -- natSet`), and `deriv_cgf_zero` gives `∂ᵢA(η) = E_η[Tᵢ]`. With the coordinate scores centered
  -- at their means, `infoMatrixᵢⱼ = ∫ scoreVecᵢ·scoreVecⱼ dP = cov_η(Tᵢ, Tⱼ)`.
  sorry

end StatLean.PointEstimation
