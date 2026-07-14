import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds
import StatLean.NonparametricStatistics.LocalPolynomial.Reproduction
import StatLean.NonparametricStatistics.SmoothnessClasses.HolderTaylor
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

/-!
# Pointwise risk of the local polynomial estimator

Bias and variance of LP(`ℓ`) with `ℓ = holderIndex β` over the Hölder class `Σ(β, L)` on
`[0,1]`, under the standing design/kernel assumptions and independent centered noise with
second moments bounded by `σ²_max`:
$$ |b(x_0)| \le q_1 h^{\beta}, \qquad \sigma^2(x_0) \le \frac{q_2}{nh}, \qquad
   q_1 = \frac{C^* L}{\ell!},\quad q_2 = \sigma_{\max}^2 (C^*)^2, $$
and the assembled pointwise rate with `h = α·n^{−1/(2β+1)}`:
`E[(f̂(x₀) − f(x₀))²] ≤ lpRateConst·n^{−2β/(2β+1)}` — with a fully explicit constant.

**Proof formalization notes.** *Bias* (deterministic): with `∑ W* = 1` (reproduction) and the
support/ℓ¹ weight bounds,
`|∑ f(xᵢ)W*ᵢ − f(t)| = |∑ (f(xᵢ) − Taylor_t(xᵢ))W*ᵢ| ≤ (L/ℓ!)·∑|xᵢ−t|^β|W*ᵢ|
 ≤ (L/ℓ!)·h^β·C*` — the intermediate Taylor terms of orders `1, …, ℓ` are killed by monomial
reproduction, and `|xᵢ−t| ≤ h` on the support of the weights. *Variance*: independence gives
`σ²(x₀) = ∑ (W*ᵢ)²·E ξᵢ² ≤ σ²_max·(sup|W*|)·∑|W*| ≤ σ²_max·C*²/(nh)` (noise second moments in
`∫⁻` form force genuine square-integrability). *Rate*: MSE = bias² + variance (exact under
`L²`), then substitute the bandwidth. Positive definiteness of `B_t` needed by reproduction
is derived from the eigenvalue hypothesis (`lpMatrix_posDef`).

**Bibliographic comments.** Pointwise rates for local polynomial estimators over Hölder
classes are due to C. J. Stone, *Ann. Statist.* **8** (1980), 1348–1360 (rectangular kernel)
with the general kernel treatment standard since the 1980s; see J. Fan and I. Gijbels,
*Local Polynomial Modelling and Its Applications* (1996).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ}

/-- **Deterministic bias bound of LP(`ℓ`)** over `Σ(β, L)` on `[0,1]`:
`|∑ i, f(xdat i)·W*ᵢ(t) − f(t)| ≤ q₁·h^β` with `q₁ = lpBiasConst β L Kmax lam0 a₀`. -/
theorem lp_bias_deterministic {β L : ℝ}
    -- USER-INPUT: positive smoothness and nonnegative Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 ≤ L)
    -- LEAN-ONLY: nonempty sample; standard side condition
    (hn : 0 < n)
    -- USER-INPUT: bandwidth at least `1/(2n)`; classical range of the weight bounds
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: design points lie in `[0,1]`; the fixed-design model on the unit interval
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: design density bound; standing design assumption
    (hdens : DesignDensityBound xdat a₀)
    {f : ℝ → ℝ}
    -- USER-INPUT: the regression function lies in `Σ(β, L)` on `[0,1]`
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) t i - f t|
      ≤ lpBiasConst β L Kmax lam0 a₀ * h ^ β := by
  sorry

/-- **Pointwise variance bound of LP(`ℓ`)** under independent centered noise with second
moments at most `σ²_max`: `σ²(t) ≤ q₂/(n·h)` with `q₂ = lpVarConst σmax2 Kmax lam0 a₀`. -/
theorem lp_variance_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {ℓ : ℕ} {f : ℝ → ℝ}
    -- LEAN-ONLY: nonempty sample; standard side condition
    (hn : 0 < n)
    -- USER-INPUT: bandwidth at least `1/(2n)`; classical range of the weight bounds
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h ℓ lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: design density bound; standing design assumption
    (hdens : DesignDensityBound xdat a₀)
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: mutually independent noise; the fixed-design regression model
    (hξi : iIndepFun ξ P)
    -- USER-INPUT: centered noise; the fixed-design regression model
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    -- USER-INPUT: noise second moments at most `σ²_max` (lower-Lebesgue form, so the bound
    -- is a genuine moment constraint); the fixed-design regression model
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t
          - ∫ ω', lpEstimator xdat (fun i => f (xdat i) + ξ i ω') K h ℓ t ∂P) ^ 2) ∂P
      ≤ ENNReal.ofReal (lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)) := by
  sorry

/-- **Pointwise MSE bound of LP(`ℓ`)** over `Σ(β, L)`: bias² + variance,
`E[(f̂(t) − f(t))²] ≤ q₁²·h^{2β} + q₂/(n·h)`. -/
theorem lp_mse_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hσ : 0 ≤ σmax2)
    (hn : 0 < n) (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    (hξm : ∀ i, Measurable (ξ i)) (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ENNReal.ofReal ((lpBiasConst β L Kmax lam0 a₀) ^ 2 * h ^ (2 * β)
          + lpVarConst σmax2 Kmax lam0 a₀ / ((n : ℝ) * h)) := by
  sorry

/-- **Pointwise rate of LP(`ℓ`) over `Σ(β, L)`**: with the bandwidth
`h = α·n^{−1/(2β+1)}`, uniformly over `t ∈ [0,1]` and `f ∈ Σ(β, L)`,
`E[(f̂(t) − f(t))²] ≤ lpRateConst·n^{−2β/(2β+1)}` — the constant is fully explicit. -/
theorem lp_pointwise_rate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L α : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hσ : 0 ≤ σmax2)
    (hn : 0 < n)
    -- LEAN-ONLY: the bandwidth is the rate-optimal tuning; packaged as an equation so all
    -- design hypotheses are stated at this bandwidth
    (hform : h = α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
    -- LEAN-ONLY: side condition `h ≥ 1/(2n)`, satisfied for all large `n`
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    (hξm : ∀ i, Measurable (ξ i)) (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ ω, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t - f t) ^ 2) ∂P
      ≤ ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  sorry

end StatLean.NonparametricStatistics
