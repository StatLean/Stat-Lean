import StatLean.StatisticalModels.Longitudinal.Defs
import StatLean.AsymptoticStatistics.ForMathlib.CondExpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# GEE unbiasedness — the estimating function is centered at the truth

**Headline (L1).** Under the marginal mean model, the GEE estimating function has mean zero:
$$\mathbb E_Q\big[D^\top V^{-1}\,(y - \mu(\beta_0))\big] = 0,$$
coordinate by coordinate. The mechanism: each coordinate of the score is a finite sum of
`(weight entry) · (residual)` terms; the weight entry is a function of the covariates only
(constitutive: `D` and `V` depend on the visit data), and the residual has vanishing
conditional mean given the covariates — so each term is an inner product of a
covariate-measurable factor against a conditionally centered factor.

Two routes, both stated:

* `gee_unbiased` — the **L² pairing route** (primary): with `MemLp 2` USER-INPUT moment
  hypotheses, each term is `⟪W, y − μ⟫_{L²(Q)} = ⟪W, condExpL2 (y − μ)⟫ = 0` via the
  self-adjointness of `condExpL2` against covariate-measurable elements — the exact pattern
  of `AsymptoticStatistics.Operators.CAR` (its `condExpL2` pairing toolkit is imported and
  reused). This avoids the bounded-factor limitation of `condExp` pull-out.
* `gee_unbiased_of_bounded` — the corollary whose hypotheses match the books' phrasing
  (bounded weights, integrable responses), via `condExp` pull-out for bounded factors.

**Reference.** `LZ86 §2` (the remark below Eq. (6): the equations are unbiased under the
mean model alone, whatever the working covariance); FLW Ch. 13 (verify §); McCulloch–Searle–
Neuhaus, *Generalized, Linear, and Mixed Models*, 2nd ed., Ch. 9 (verify §) (`MSN Ch. 9`).

**Proof formalization notes.** Coordinatewise: `geeScore … k = ∑ j, W k j · resid j`;
linearity of the integral reduces to one visit. The measurability hypotheses on the mean
function and the weight entries are LEAN-ONLY (the books implicitly assume everything
measurable); the `MemLp 2` moment hypotheses are USER-INPUT (LZ86 assume finite second
moments throughout). *Book vs Lean:* no correctness of `V` and no independence across visits
is assumed — exactly LZ86's point.

**Bibliographic comments.** Unbiasedness of estimating functions as the defining property is
`God60`; the GEE instance is Liang–Zeger (1986). The observation that only the conditional
mean model matters (robustness to working-covariance misspecification) is the celebrated
LZ86 Theorem 1 hypothesis structure.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace StatLean.StatisticalModels.Longitudinal

variable {p m q : ℕ} {Θβ : Type*}

/-- The covariate σ-algebra is a sub-σ-algebra of the record σ-algebra (LEAN-ONLY
structural fact used by every conditioning step). -/
theorem covariateSigma_le (p m : ℕ) :
    covariateSigma p m ≤ (inferInstance : MeasurableSpace (LongitudinalRecord p m)) := by
  sorry

/-- Record accessors are measurable (LEAN-ONLY plumbing). -/
theorem measurable_record_y (j : Fin m) :
    Measurable fun r : LongitudinalRecord p m => r.y j := by
  sorry

/-- Covariate functionals are `covariateSigma`-measurable (LEAN-ONLY plumbing): any
measurable function of `(times, x)` is measurable for the covariate σ-algebra. -/
theorem covariateSigma_measurable_comp
    {g : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) → ℝ} (hg : Measurable g) :
    Measurable[covariateSigma p m] fun r : LongitudinalRecord p m => g (r.times, r.x) := by
  sorry

/-- **L1, GEE unbiasedness (L² route)** (`LZ86 §2`, remark below Eq. (6)): under the marginal
mean model, every coordinate of the GEE estimating function integrates to zero — whatever the
working covariance. -/
theorem gee_unbiased (Q : Measure (LongitudinalRecord p m)) [IsProbabilityMeasure Q]
    (S : GEESpec p m q Θβ) (β₀ : Θβ)
    -- USER-INPUT: the marginal mean model holds at β₀; LZ86 §2 Eq. (2)
    (hmean : IsMarginalMeanModel Q S.μfun β₀)
    -- USER-INPUT: square-integrable responses and fitted values; LZ86 §2
    (hY : ∀ j, MemLp (fun r => r.y j) 2 Q)
    (hμ : ∀ j, MemLp (fun r : LongitudinalRecord p m =>
      S.μfun β₀ (r.times j, r.x j)) 2 Q)
    -- USER-INPUT: square-integrable weight entries; LZ86 §2
    (hW : ∀ k j, MemLp (fun r : LongitudinalRecord p m =>
      S.geeWeight β₀ r.times r.x k j) 2 Q)
    -- LEAN-ONLY: measurability of the weight entries as covariate functionals
    (hWmeas : ∀ k j, Measurable fun tx : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) =>
      S.geeWeight β₀ tx.1 tx.2 k j)
    (k : Fin q) :
    ∫ r, S.geeScore β₀ r k ∂Q = 0 := by
  sorry

/-- **L1', the bounded-weights corollary** (hypotheses in the books' phrasing: bounded
weights, integrable data), via `condExp` pull-out for bounded factors. -/
theorem gee_unbiased_of_bounded (Q : Measure (LongitudinalRecord p m))
    [IsProbabilityMeasure Q] (S : GEESpec p m q Θβ) (β₀ : Θβ)
    -- USER-INPUT: the marginal mean model holds at β₀; LZ86 §2 Eq. (2)
    (hmean : IsMarginalMeanModel Q S.μfun β₀)
    -- USER-INPUT: integrable responses and fitted values; FLW Ch. 13
    (hY : ∀ j, Integrable (fun r => r.y j) Q)
    (hμ : ∀ j, Integrable (fun r : LongitudinalRecord p m =>
      S.μfun β₀ (r.times j, r.x j)) Q)
    -- USER-INPUT: uniformly bounded weight entries; FLW Ch. 13
    {C : ℝ} (hC : ∀ k j r, |S.geeWeight β₀ (LongitudinalRecord.times r)
      (LongitudinalRecord.x r) k j| ≤ C)
    -- LEAN-ONLY: measurability of the weight entries as covariate functionals
    (hWmeas : ∀ k j, Measurable fun tx : (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin p)) =>
      S.geeWeight β₀ tx.1 tx.2 k j)
    (k : Fin q) :
    ∫ r, S.geeScore β₀ r k ∂Q = 0 := by
  sorry

end StatLean.StatisticalModels.Longitudinal
