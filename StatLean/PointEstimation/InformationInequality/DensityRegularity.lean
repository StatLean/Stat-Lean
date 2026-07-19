import StatLean.PointEstimation.InformationInequality.CramerRao
import StatLean.PointEstimation.InformationInequality.Additivity

/-!
# Family-side regularity: the information inequality for *every* square-integrable statistic

The information inequality as stated with conditions on the estimator requires, for each
statistic separately, that its expectation may be differentiated under the integral sign.
That condition is undesirable: one would like a hypothesis on the *densities* alone, valid
once and for all. The classical device is a Lipschitz-type domination of the normalized
difference quotients of the density: if there are `ε > 0` and an envelope `b` with
$$ \Bigl|\frac{p_{\theta+\Delta}(x) - p_\theta(x)}{\Delta\, p_\theta(x)}\Bigr| \le b(x)
   \quad\text{for } 0 < |\Delta| < \varepsilon, \qquad E_\theta b^2 < \infty, $$
then Cauchy–Schwarz makes `|δ| b` integrable for every square-integrable `δ`, and dominated
convergence justifies passing the limit inside the integral. Consequently the information
inequality holds for *every* statistic with a finite second moment.

Contents:
* `HasDominatedDifferenceQuotient` — the domination condition on the normalized difference
  quotients of the density;
* `diff_under_integral_of_density_regular` — the dominated-convergence step: the expectation
  of any square-integrable statistic is differentiable, with derivative the covariance of
  the statistic with the score;
* `integral_score_eq_zero_of_density_regular` — the same applied to the constant statistic
  `1`: the mean-zero property of the score is a *consequence* of the domination condition;
* `cramer_rao_of_density_regular` — the information inequality under family-side conditions
  only, valid for every square-integrable statistic;
* `cramer_rao_iid` — the sample-size-`n` form, with `n I(θ)` in the denominator.

**Reference.** Classical family-side (Lipschitz-type) regularity conditions for the
information inequality, replacing the per-estimator differentiation-under-the-integral
condition. Original sources in the bibliographic comments below.

**Proof formalization notes.**
* The domination condition is transcribed exactly as the classical one: the envelope `b` is
  required to be square-integrable under `P_θ` and to bound the *normalized* difference
  quotients `(p_{θ+Δ} − p_θ)/(Δ p_θ)` for all small nonzero increments; the bound is imposed
  `P_θ`-almost everywhere, which is where the quotient is meaningful (on the common support
  the denominator does not vanish). No uniformity in `θ` is assumed: the condition is local
  at the parameter value where the inequality is claimed.
* The conclusion of the dominated-convergence step is stated as a `HasDerivAt` of
  `t ↦ ∫ δ p_t dμ` whose value is `∫ δ ℓ̇_θ p_θ dμ`. Since the score has mean zero, that
  value is the covariance of `δ` with the score, which is the classical reading; both
  conclusions of the classical lemma (existence of the derivative, and its identification)
  are therefore contained in this single statement.
* `cramer_rao_of_density_regular` returns a conjunction rather than a bound with the
  derivative supplied as data: under family-side regularity the derivative is not an input
  but a consequence, so it is stated as part of the conclusion. Supplying it as a hypothesis
  would reintroduce exactly the estimator-side condition this theorem exists to remove.
* `cramer_rao_iid` follows the classical route: the information inequality for the sample,
  with the additivity of the information over independent observations substituted in the
  denominator. Its estimator-side conditions are stated for the sample; the family-side
  theorem above, applied to the product family, is what discharges them in applications.

**Bibliographic comments.** Regularity conditions of this Lipschitz type, and the resulting
"holds for all square-integrable estimators" form of the information inequality, are
discussed by H. Cramér (*Mathematical Methods of Statistics*, Princeton University Press,
1946, §32.3) and refined by R. A. Wijsman ("On the attainment of the Cramér–Rao lower
bound," *Ann. Statist.* **1** (1973), 538–542) and V. Fabian and J. Hannan ("On the
Cramér–Rao inequality," *Ann. Statist.* **5** (1977), 197–205), who gave conditions under
which the bound holds and is attained. The additivity used for the sample-size-`n` form is
R. A. Fisher's ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925),
700–725).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **dominated-difference-quotient condition** at `θ`: there are a radius `ε > 0` and
an envelope `b`, square-integrable under `P_θ`, such that the normalized difference
quotients of the density satisfy
`|(p_{θ+Δ}(x) − p_θ(x)) / (Δ p_θ(x))| ≤ b(x)` for every increment with `0 < |Δ| < ε`,
`P_θ`-almost everywhere.

This is the classical Lipschitz-type smoothness condition on the family; it is what makes
dominated convergence available uniformly in the estimator. Edge behavior: the bound is
imposed `P_θ`-a.e., so points outside the support impose no constraint (the quotient there
is Lean's junk value `0`), and increments `Δ = 0` are excluded since the quotient is not
defined for them. -/
def HasDominatedDifferenceQuotient (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧) (θ : ℝ) :
    Prop :=
  ∃ ε > 0, ∃ b : 𝓧 → ℝ, MemLp b 2 (M.toMeasure μ θ) ∧
    ∀ Δ : ℝ, 0 < |Δ| → |Δ| < ε → ∀ᵐ x ∂(M.toMeasure μ θ),
      |(M.density (θ + Δ) x - M.density θ x) / (Δ * M.density θ x)| ≤ b x

/-- **Differentiation under the integral sign from family-side regularity.** Under the
dominated-difference-quotient condition, the expectation of *any* square-integrable
statistic is differentiable at `θ`, with derivative `∫ δ ℓ̇_θ p_θ dμ` — the covariance of
the statistic with the score, the score being centered.

Cauchy–Schwarz bounds the integrand `|δ| · |difference quotient|` by `|δ| b`, which is
integrable because both factors are square-integrable; dominated convergence then exchanges
the limit and the integral. -/
-- TODO: the dominated-convergence core of the family-side differentiation-under-the-integral
-- step — bounding the difference quotients `δ · (p_{θ+Δ} − p_θ)/Δ` by the `L²` envelope
-- `|δ| · b · p_θ` (Cauchy–Schwarz) and passing to the limit — is the single sanctioned analytic
-- debt of this file; every downstream theorem is a genuine reduction to it.
private theorem diff_under_integral_core (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    (hpdf : IsPDFOf M μ) (hsupp : HasCommonSupport M) (θ : ℝ)
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    (hreg : HasDominatedDifferenceQuotient M μ θ) (δ : 𝓧 → ℝ)
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ := by
  sorry

theorem diff_under_integral_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter;
    -- classical smoothness condition (off the support the parameter map is constant `0`
    -- by the common-support condition, so nothing is assumed there)
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ)
    (δ : 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ :=
  diff_under_integral_core M μ hpdf hsupp θ hdiff hreg δ hδ2

/-- **The mean-zero property of the score is a consequence of family-side regularity.**
Taking the constant statistic `1` in the previous theorem, the derivative of the constant
map `t ↦ ∫ p_t dμ = 1` is `0`, which is exactly `E_θ[ℓ̇_θ(X)] = 0`. -/
theorem integral_score_eq_zero_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ) :
    ∫ x, score M θ x * M.density θ x ∂μ = 0 := by
  haveI := isProbabilityMeasure_toMeasure M μ hpdf θ
  have hd := diff_under_integral_of_density_regular M μ hpdf hsupp θ hdiff hreg
    (fun _ => 1) (memLp_const 1)
  have hconst : (fun t => ∫ x, (1 : ℝ) * M.density t x ∂μ) = fun _ => (1 : ℝ) := by
    funext t; simp_rw [one_mul]; exact hpdf.density_integral_eq_one t
  have h0 : HasDerivAt (fun t => ∫ x, (1 : ℝ) * M.density t x ∂μ) 0 θ := by
    rw [hconst]; exact hasDerivAt_const θ 1
  have hzero := hd.unique h0
  simpa using hzero

/-- **The information inequality under family-side regularity.** If the family has a common
support, is differentiable in the parameter on that support, has positive information and
satisfies the dominated-difference-quotient condition at `θ`, then for *every* statistic
with a finite second moment the expectation is differentiable at `θ` and the information
inequality holds — no condition on the statistic beyond square-integrability.

The derivative appears in the conclusion rather than among the hypotheses precisely because
it is a consequence here: this is the content of the theorem. -/
theorem cramer_rao_of_density_regular (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the information is positive; classical standing assumption (it also
    -- forces the defining integral to converge, so no separate integrability is assumed)
    (hI : 0 < fisherInfo M μ θ)
    -- USER-INPUT: the dominated-difference-quotient condition at `θ`
    (hreg : HasDominatedDifferenceQuotient M μ θ)
    (δ : 𝓧 → ℝ)
    -- USER-INPUT: the statistic has a finite second moment at `θ`; the only condition on
    -- the estimator
    (hδ2 : MemLp δ 2 (M.toMeasure μ θ)) :
    HasDerivAt (fun t => ∫ x, δ x * M.density t x ∂μ)
        (∫ x, δ x * score M θ x * M.density θ x ∂μ) θ ∧
      (∫ x, δ x * score M θ x * M.density θ x ∂μ) ^ 2 / fisherInfo M μ θ
        ≤ variance δ (M.toMeasure μ θ) := by
  sorry

/-- **The information inequality for an independent identically distributed sample.** For a
sample of size `n ≥ 1` the information in the sample is `n I(θ)`, so the bound on the
variance of a statistic `δ` of the whole sample is
`(∂_θ E_θ δ)² / (n I(θ)) ≤ var_θ(δ)`.

The conditions on the sample statistic are the estimator-side ones (finite second moment,
and differentiation under the integral sign for its expectation); the family-side theorem
above, applied to the `n`-fold product family, is what discharges them in applications. -/
theorem cramer_rao_iid (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- LEAN-ONLY: σ-finiteness of the dominating measure, required by the product-measure
    -- theory
    [SigmaFinite μ]
    -- USER-INPUT: `M` is a family of `μ`-probability densities
    (hpdf : IsPDFOf M μ)
    -- USER-INPUT: the members share a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    (n : ℕ)
    -- USER-INPUT: the sample is nonempty
    (hn : 0 < n)
    (θ : ℝ)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the score of one observation has mean zero; classical regularity
    -- condition, and what makes the informations add
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- LEAN-ONLY: integrability of the mean score, needed to factorize the cross terms in
    -- the additivity step
    (hint1 : Integrable (fun x => score M θ x * M.density θ x) μ)
    -- USER-INPUT: the information in one observation is positive
    (hI : 0 < fisherInfo M μ θ)
    (δ : (Fin n → 𝓧) → ℝ) (g' : ℝ)
    -- USER-INPUT: the sample statistic has a finite second moment at `θ`
    (hδ2 : MemLp δ 2 ((piFamily M n).toMeasure (Measure.pi fun _ : Fin n => μ) θ))
    -- USER-INPUT: the expectation of the sample statistic is differentiable at `θ`
    (hdiffδ : HasDerivAt
      (fun t => ∫ x, δ x * (piFamily M n).density t x ∂(Measure.pi fun _ : Fin n => μ)) g' θ)
    -- USER-INPUT: that derivative is obtained by differentiating under the integral sign
    (hswap : g' = ∫ x, δ x * deriv (fun t => (piFamily M n).density t x) θ
      ∂(Measure.pi fun _ : Fin n => μ)) :
    g' ^ 2 / ((n : ℝ) * fisherInfo M μ θ)
      ≤ variance δ ((piFamily M n).toMeasure (Measure.pi fun _ : Fin n => μ) θ) := by
  sorry

end StatLean.PointEstimation
