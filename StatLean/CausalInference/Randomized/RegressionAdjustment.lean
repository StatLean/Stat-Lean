import StatLean.CausalInference.Randomized.Neyman

/-!
# Regression adjustment — the difference in means as a least-squares coefficient

Two classical algebraic facts about running regressions on experimental data.

1. **The unadjusted regression is the difference in means.** The ordinary least squares
   coefficient of `Z` in the fit of `Y` on `(1, Z)` is exactly `τ̂` — regression buys
   nothing by itself, it merely repackages the estimator.
2. **Covariate adjustment stays unbiased.** For fixed coefficients `β₁, β₀`, the adjusted
   estimator
   `τ̂(β₁,β₀) = (Ȳ₁ - β₁(X̄₁ - X̄)) - (Ȳ₀ - β₀(X̄₀ - X̄))`
   is still unbiased under complete randomization, because the arm covariate means are
   themselves unbiased for the population covariate mean.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). eq. (4.3) (§4.4, p. 49: the OLS coefficient of `Z`
in `Y ~ (1, Z)` equals `τ̂`; stated in the text, no theorem number); eqs. (6.2)–(6.3)
(§6.2: the adjusted family `τ̂(β₁,β₀)`, of which Lin's estimator is the member with
estimated coefficients). (`Ding eq. (4.3); eqs. (6.2)–(6.3)`.) Compare G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*, Cambridge
University Press, 2015, ch. 7. (`IR ch. 7`.)

**Scope.** Ding's Proposition 6.2 — that Lin's estimator, with coefficients *estimated* by
the fully interacted OLS fit, is the coefficient of `Z` in the regression of `Y` on
`(1, Z, X, ZX)` — is **not** formalized: it is multivariate least-squares algebra whose
causal content (unbiasedness for any fixed coefficients, which is what makes adjustment
safe under randomization) is already captured by `adjEstimator_unbiased` below. Likewise
the asymptotic efficiency comparison between `τ̂` and Lin's estimator is out of scope for
this release.

**Proof formalization notes.** The OLS identity is proved directly from the two normal
equations for a binary regressor rather than by invoking a general OLS API: with `Z` binary
the design matrix has rank at most `2`, the normal equations read
`∑(Yᵢ - a - bZᵢ) = 0` and `∑Zᵢ(Yᵢ - a - bZᵢ) = 0`, and subtracting `n₁/n` times the first
from the second gives `b = Ȳ₁ - Ȳ₀` after dividing by `n₁n₀/n`. The characterization is
stated as "any `(a, b)` satisfying the normal equations has `b = τ̂`", which avoids
committing to an existence-and-uniqueness statement about the minimizer and is the form
Ding uses. Unbiasedness of the adjusted family follows from linearity of `Design.expect`
plus `completeDesign_expect_ind`.

**Bibliographic comments.** The cautionary analysis of regression adjustment in randomized
experiments is D. A. Freedman, "On regression adjustments to experimental data," *Adv. in
Appl. Math.* **40** (2008), 180–193; the repair is W. Lin, "Agnostic notes on regression
adjustments to experimental data: reexamining Freedman's critique," *Ann. Appl. Statist.*
**7** (2013), 295–318.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-- The **normal equations** of the least-squares fit of the observed outcome on
`(1, Z)`: the residuals are orthogonal to the constant and to the regressor. -/
def IsOLSFit (S : ScienceTable n) (z : Assignment n) (a b : ℝ) : Prop :=
  (∑ i, (S.observed z i - a - b * ind (z i)) = 0)
  ∧ (∑ i, ind (z i) * (S.observed z i - a - b * ind (z i)) = 0)

/-- **The OLS coefficient of the treatment is the difference in means** (Ding eq. (4.3)):
regressing the observed outcome on an intercept and the treatment indicator reproduces
`τ̂` exactly. -/
theorem olsCoeff_eq_diffInMeans (S : ScienceTable n) {z : Assignment n} {a b : ℝ}
    -- USER-INPUT: `(a, b)` solves the least-squares normal equations; Ding §4.4
    (hfit : IsOLSFit S z a b)
    -- USER-INPUT: both arms are nonempty, else the regressor is constant and `b` is not
    -- identified; Ding §4.4
    (h1 : 0 < (armIdx z true).card) (h0 : 0 < (armIdx z false).card) :
    b = diffInMeans S z := by
  sorry

/-- The intercept of the same fit is the control arm mean. -/
theorem olsIntercept_eq_armMean (S : ScienceTable n) {z : Assignment n} {a b : ℝ}
    (hfit : IsOLSFit S z a b)
    (h1 : 0 < (armIdx z true).card) (h0 : 0 < (armIdx z false).card) :
    a = armMean S z false := by
  sorry

/-- The **arm mean of a covariate** under an assignment. -/
noncomputable def armCovMean (x : Fin n → ℝ) (z : Assignment n) (arm : Bool) : ℝ :=
  ((armIdx z arm).card : ℝ)⁻¹ * ∑ i ∈ armIdx z arm, x i

/-- **The arm covariate mean is unbiased for the population covariate mean** under complete
randomization — the fact that makes covariate adjustment harmless. -/
theorem armCovMean_unbiased (x : Fin n → ℝ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armCovMean x z true) = popMean x := by
  sorry

/-- The **covariate-adjusted estimator with fixed coefficients** (Ding eqs. (6.2)–(6.3)). -/
noncomputable def adjEstimator (S : ScienceTable n) (x : Fin n → ℝ) (β1 β0 : ℝ)
    (z : Assignment n) : ℝ :=
  (armMean S z true - β1 * (armCovMean x z true - popMean x))
  - (armMean S z false - β0 * (armCovMean x z false - popMean x))

/-- **Unbiasedness of covariate adjustment** (Ding §6.2): for any *fixed* adjustment
coefficients, the adjusted estimator remains unbiased under complete randomization. -/
theorem adjEstimator_unbiased (S : ScienceTable n) (x : Fin n → ℝ) (β1 β0 : ℝ)
    (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty; Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (adjEstimator S x β1 β0) = S.finiteATE := by
  sorry

/-- With zero adjustment coefficients the adjusted estimator is the difference in means. -/
theorem adjEstimator_zero (S : ScienceTable n) (x : Fin n → ℝ) (z : Assignment n) :
    adjEstimator S x 0 0 z = diffInMeans S z := by
  sorry

end StatLean.CausalInference
