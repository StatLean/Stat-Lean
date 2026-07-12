import StatLean.Bayesian.DirichletLaplace.Defs
import StatLean.Bayesian.ForMathlib.GammaBounds
import StatLean.Bayesian.ForMathlib.BindWithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Dirichlet–Laplace marginal density (C2)

The univariate Dirichlet–Laplace marginal `DLₐ` (BPPD eq. (10)) is a scale mixture
`θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(shape a, rate 1/2)`. This file computes its **Lebesgue density**
in the mixture-integral form and records the basic analytic API used by the density bounds
(`DensityBounds`, C3), the product-density bounds (`PriorDensityBounds`, C4), and the small-ball
estimates (`PriorSmallBall`, C5).

Objects:
* `dlDensity a` — the marginal density `f_{DL,a}(x) = ∫₀^∞ g_{a,1/2}(ψ) · ℓ_ψ(x) dψ` against
  Lebesgue measure (`g_{a,1/2}` the `Gamma(a, rate 1/2)` density, `ℓ_ψ` the centered `Laplace(ψ)`
  density). This is the **mixture-integral** density, *not* the Bessel-function closed form of
  BPPD Proposition 3.1 (a documented non-goal).
* `dlNormConst a = (1/2)^{a+1}/Γ(a)` — the leading constant of `f_{DL,a}` (the `Gamma` prefactor
  `(1/2)^a/Γ(a)` times the Laplace prefactor `1/2`).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). Prior (10)/(11); Proposition 3.1 (marginal density).

**Proof formalization notes.**
* `dlMarginal_eq_withDensity`: unfold the mixture `bind` through `Measure.bind_withDensity` (F3)
  and the `Gamma`-`withDensity` representation `gammaMeasure a 2⁻¹ = volume.withDensity (gammaPDF …)`;
  `lintegral_withDensity` collapses `∫ ℓ_ψ dGamma` to the Lebesgue integral `∫ g_{a,1/2}(ψ) ℓ_ψ(·)`.
* **P1** (`lintegral_dlDensity_eq_one`): total mass `1`, i.e. `f_{DL,a}` is a probability density —
  immediate from `dlMarginal_eq_withDensity` and `isProbabilityMeasure_dlMarginal`.
* **P2** (`dlDensity_anti`): `f_{DL,a}` is nonincreasing in `|x|`, since each Laplace mixand
  `ℓ_ψ(x) = (2ψ)^{-1} e^{-|x|/ψ}` is nonincreasing in `|x|` and the `Gamma` weight is nonnegative
  (`lintegral_mono`, pointwise in `ψ`).
* `dlMarginal_abs_gt_eq_mixture`: the tail `ℙ_{DL,a}(|θ| > δ)` equals `∫ e^{-δ/ψ} dGamma_{a,1/2}(ψ)`
  (each Laplace tail is `ℙ(|θ| > δ | ψ) = e^{-δ/ψ}`, `laplaceMeasure_abs_gt`, F1) — the starting
  point of Lemma 3.3 (C3).
* `dlNormConst` two-sided bounds `a/8 ≤ C(a) ≤ (e/2)·a` on `0 < a ≤ 1`, from the elementary `Γ`
  bounds `1/(e a) ≤ Γ(a) ≤ 2/a` (F2). These feed the `17 a` / `a/64` prefactors of C3.

**Bibliographic comments.** The double-exponential (Laplace) prior as a sparsity-inducing prior
originates with the Bayesian Lasso (T. Park and G. Casella, *J. Amer. Statist. Assoc.* 103 (2008),
681–686); the representation of a heavy-tailed marginal as a global–local scale mixture is the
organizing idea of the shrinkage-prior literature (N. G. Polson and J. G. Scott, *Bayesian
Statistics 9*, Oxford, 2011). The Dirichlet–Laplace prior formalized here is the specific
`Gamma`-mixture-of-Laplace construction of Bhattacharya–Pati–Pillai–Dunson achieving the optimal
posterior-contraction rate in the sparse normal-means problem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-! ### The marginal density and its normalizing constant -/

/-- **Dirichlet–Laplace marginal density** `f_{DL,a}` against Lebesgue measure (BPPD eq. (10)/(11),
mixture-integral form — *not* the Bessel closed form of Proposition 3.1). Pointwise
`f_{DL,a}(x) = ∫₀^∞ g_{a,1/2}(ψ) · ℓ_ψ(x) dψ`, where `g_{a,1/2}` is the `Gamma(a, rate 1/2)` density
(`gammaPDF a 2⁻¹`) and `ℓ_ψ` is the centered `Laplace(ψ)` density (`laplacePDF ψ`). Edge behavior:
at `x = 0` (and, more generally, whenever `a ≤ 1`) the integral is `+∞` — the DL marginal has an
integrable pole at the origin — so the value is a genuine `ℝ≥0∞`. -/
noncomputable def dlDensity (a : ℝ) : ℝ → ℝ≥0∞ :=
  fun x => ∫⁻ ψ, gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume

/-- **Leading normalizing constant** of the DL marginal density, `C(a) = (1/2)^{a+1} / Γ(a)`
(BPPD §3.1): the product of the `Gamma(a, rate 1/2)` prefactor `(1/2)^a/Γ(a)` with the Laplace
prefactor `1/2`. For `a ≤ 0` it inherits Mathlib's `Real.Gamma` pole conventions and carries no
statistical meaning; every content lemma assumes `0 < a`. -/
noncomputable def dlNormConst (a : ℝ) : ℝ := (1 / 2 : ℝ) ^ (a + 1) / Real.Gamma a

variable {a δ : ℝ}

/-- `x ↦ f_{DL,a}(x)` is measurable: a parametrized Lebesgue integral of the jointly measurable
integrand `(ψ, x) ↦ gammaPDF a 2⁻¹ ψ · laplacePDF ψ x`. -/
lemma measurable_dlDensity : Measurable (dlDensity a) := by
  sorry

/-- The DL marginal is the `withDensity` of `f_{DL,a}` against Lebesgue measure (BPPD eq. (11)). -/
lemma dlMarginal_eq_withDensity
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    dlMarginal a = volume.withDensity (dlDensity a) := by
  sorry

/-- **Real integral form** away from the origin: for `x ≠ 0` the mixture integral is finite and is
the `ℝ≥0∞`-coercion of the Bochner integral of `C(a) · ψ^{a-2} · exp(-ψ/2 - |x|/ψ)` over `(0, ∞)`
(the integrand `gammaPDFReal a 2⁻¹ ψ · laplacePDFReal ψ x` on `ψ > 0`, with the two prefactors
collected into `dlNormConst a`). This is the form on which C3's `u = |x|/ψ` substitutions operate. -/
lemma dlDensity_eq_ofReal_integral
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- LEAN-ONLY: off the origin, where the density is finite; the pole at 0 is excluded
    {x : ℝ} (hx : x ≠ 0) :
    dlDensity a x
      = ENNReal.ofReal (∫ ψ in Set.Ioi (0 : ℝ),
          dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)) := by
  sorry

/-- **Integrability** of the real mixture integrand on `(0, ∞)` for `x ≠ 0`: near `0` the factor
`e^{-|x|/ψ}` kills the `ψ^{a-2}` pole, near `∞` the factor `e^{-ψ/2}` dominates. -/
lemma integrable_dlDensity_integrand
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- LEAN-ONLY: off the origin, where the integrand is integrable
    {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn
      (fun ψ => dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ))
      (Set.Ioi (0 : ℝ)) := by
  sorry

/-- **P1 (total mass one).** `f_{DL,a}` integrates to `1` — the DL marginal is a probability density
(BPPD eq. (10)); immediate from `dlMarginal_eq_withDensity` and `isProbabilityMeasure_dlMarginal`. -/
lemma lintegral_dlDensity_eq_one
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    ∫⁻ x, dlDensity a x ∂volume = 1 := by
  sorry

/-- **P2 (monotone in `|x|`).** The DL marginal density is nonincreasing in `|x|`: for `|x| ≤ |y|`,
`f_{DL,a}(y) ≤ f_{DL,a}(x)`. Each Laplace mixand is nonincreasing in `|·|` and the `Gamma` weight is
nonnegative, so the inequality holds pointwise in `ψ` and passes through the integral. -/
lemma dlDensity_anti {x y : ℝ} (hxy : |x| ≤ |y|) :
    dlDensity a y ≤ dlDensity a x := by
  sorry

/-- **Tail as a `Gamma`-mixture of Laplace tails.** Since `θ | ψ ~ Laplace(ψ)` has
`ℙ(|θ| > δ) = e^{-δ/ψ}`, marginalizing over `ψ ~ Gamma(a, rate 1/2)` gives
`ℙ_{DL,a}(|θ| > δ) = ∫ e^{-δ/ψ} dGamma_{a,1/2}(ψ)` — the starting identity for Lemma 3.3 (C3). -/
lemma dlMarginal_abs_gt_eq_mixture
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: nonnegative tail threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 ≤ δ) :
    dlMarginal a {x | δ < |x|}
      = ∫⁻ ψ, ENNReal.ofReal (Real.exp (-δ / ψ)) ∂(gammaMeasure a 2⁻¹) := by
  sorry

/-! ### Two-sided bounds on the leading constant (from `GammaBounds`, F2) -/

/-- `C(a) > 0` for `0 < a`. -/
lemma dlNormConst_pos
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a) :
    0 < dlNormConst a := by
  sorry

/-- **Upper bound** `C(a) ≤ (e/2)·a` on `0 < a ≤ 1`, from `Γ(a) ≥ 1/(e a)` (`inv_e_mul_le_Gamma`,
F2) and `(1/2)^{a+1} ≤ 1/2`. Source of the `17 a` prefactor in the density upper bound P3 (C3). -/
lemma dlNormConst_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1
    (ha1 : a ≤ 1) :
    dlNormConst a ≤ Real.exp 1 / 2 * a := by
  sorry

/-- **Lower bound** `a/8 ≤ C(a)` on `0 < a ≤ 1`, from `Γ(a) ≤ 2/a` (`Gamma_le_two_div`, F2) and
`(1/2)^{a+1} ≥ 1/4`. Source of the `a/64` prefactor in the density lower bound P4 (C3). -/
lemma dlNormConst_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1
    (ha1 : a ≤ 1) :
    a / 8 ≤ dlNormConst a := by
  sorry

end StatLean.Bayesian
