import StatLean.PointEstimation.UMVU.Defs
import Mathlib.Probability.Moments.Covariance

/-!
# The covariance characterization of minimum-variance unbiased estimation

Adding a multiple of an unbiased estimator of zero to an unbiased estimator keeps it
unbiased and changes its variance by `λ² var(U) + 2λ cov(δ, U)`, an expression that takes
negative values for some `λ` unless `cov(δ, U) = 0`. This makes orthogonality to the space of
unbiased estimators of zero both necessary and sufficient for minimum variance:

* `isUMVU_iff_uncorrelated_unbiasedZero` — a square-integrable unbiased estimator of `g` is
  UMVU exactly when it is uncorrelated, under every member of the model, with every
  square-integrable unbiased estimator of zero.

The same orthogonality condition is what makes a covariance-based lower bound on the variance
of unbiased estimators possible at all: the bound `var(δ) ≥ cov(δ, ψ)² / var(ψ)` is useful
only when its right-hand side does not depend on the particular unbiased estimator `δ`.

* `covariance_depends_only_on_mean_iff` — the covariance of an estimator with a fixed
  reference statistic `ψ` depends on the estimator only through its mean function exactly when
  `ψ` is uncorrelated with every square-integrable unbiased estimator of zero.

**Reference.** Classical characterization of uniformly minimum variance unbiased estimators
by uncorrelatedness with the unbiased estimators of zero, and the corresponding condition for
covariance-type variance bounds.

**Proof formalization notes.**
* Mathlib's covariance takes its two arguments before the measure,
  `ProbabilityTheory.covariance X Y μ`, and is symmetric; the arguments are written here in
  the order (estimator, unbiased estimator of zero) to match the classical display, but no
  statement depends on the order.
* The classical statement is phrased as `E_θ(δ U) = 0`; since `E_θ U = 0` this is the same as
  `cov_θ(δ, U) = 0`, and the covariance form is used here because it is the form Mathlib's
  bilinearity API (`covariance_sub_left`, `covariance_zero_left`) consumes directly.
* Both statements quantify over the estimator class `Δ` of square-integrable estimators
  (`MemEstL2`), exactly as the classical theorems do: outside `Δ` the variance-minimization
  problem is vacuous, and the sufficiency direction of the first theorem is proved by
  discarding competitors of infinite variance.
* The second theorem formalizes "`cov(δ, ψ)` depends on `δ` only through `g(θ)`" as: any two
  square-integrable estimators with the same mean function have the same covariance with `ψ`
  at every parameter. The reference statistic is allowed to depend on the parameter
  (`ψ : Θ → 𝓧 → ℝ`), as in the classical statement where `ψ = ψ(x, θ)`; only its value at the
  parameter at which the covariance is computed ever enters, so the added generality is free.
* The reference statistic is required square-integrable under every member, which is the
  classical "finite second moment" hypothesis; without it both covariances are junk.

**Bibliographic comments.** The covariance characterization of minimum-variance unbiased
estimators is due to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and
unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955), 219–236) and C. R. Rao
("Sufficient statistics and minimum variance estimates," *Proc. Camb. Phil. Soc.* **45**
(1949), 213–218), with the projection-theoretic account given by R. R. Bahadur ("On unbiased
estimates of uniformly minimum variance," *Sankhyā* **18** (1957), 211–224); the extension
beyond squared-error loss also originates there. The condition under which a covariance
inequality yields a genuine lower bound for all unbiased estimators is due to C. R. Blyth
("Necessary and sufficient conditions for inequalities of Cramér–Rao type," *Ann. Statist.*
**2** (1974), 464–473); the underlying inequality goes back to C. R. Rao ("Information and the
accuracy attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.*
**37** (1945), 81–91).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **UMVU ⟺ uncorrelated with every unbiased estimator of zero.** A square-integrable
unbiased estimator of `g` has uniformly minimum variance among the square-integrable unbiased
estimators of `g` exactly when its covariance with every square-integrable unbiased estimator
of zero vanishes at every parameter. -/
theorem isUMVU_iff_uncorrelated_unbiasedZero (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {δ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate estimator is unbiased for the estimand
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the candidate estimator lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    IsUMVU P g δ ↔
      ∀ U : 𝓧 → ℝ, IsUnbiasedZero P U → MemEstL2 P U → ∀ θ, covariance δ U (P θ) = 0 := by
  sorry

/-- **When does a covariance bound apply to all unbiased estimators?** The covariance of an
estimator with a fixed reference statistic `ψ` is determined by the estimator's mean function
alone exactly when `ψ` is uncorrelated with every square-integrable unbiased estimator of
zero. This is the condition under which `var(δ) ≥ cov(δ, ψ)² / var(ψ)` becomes a bound valid
for every unbiased estimator of a given estimand. -/
theorem covariance_depends_only_on_mean_iff (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (ψ : Θ → 𝓧 → ℝ)
    -- USER-INPUT: the reference statistic has a finite second moment under every member
    (hψ : ∀ θ, MemLp (ψ θ) 2 (P θ)) :
    (∀ δ₁ δ₂ : 𝓧 → ℝ, MemEstL2 P δ₁ → MemEstL2 P δ₂ →
        (∀ θ, ∫ x, δ₁ x ∂(P θ) = ∫ x, δ₂ x ∂(P θ)) →
        ∀ θ, covariance δ₁ (ψ θ) (P θ) = covariance δ₂ (ψ θ) (P θ)) ↔
      ∀ U : 𝓧 → ℝ, IsUnbiasedZero P U → MemEstL2 P U → ∀ θ, covariance U (ψ θ) (P θ) = 0 := by
  sorry

end StatLean.PointEstimation
