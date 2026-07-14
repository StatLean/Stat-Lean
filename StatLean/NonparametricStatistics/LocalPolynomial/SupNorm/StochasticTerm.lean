import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds
import StatLean.NonparametricStatistics.ForMathlib.MaxExpSquare

/-!
# Sup-norm control of the stochastic term of the local polynomial estimator

Under i.i.d. centered Gaussian noise and a Lipschitz boxed kernel, the stochastic component
of LP(`ℓ`) satisfies
$$ \mathbb E\Bigl[\ \sup_{t\in[0,1]}\Bigl|\sum_i \xi_i\,W^*_i(t)\Bigr|^2\Bigr]
   \;\le\; C\,\frac{\sigma_\xi^2\,\log n}{n h}, $$
with `C = C(ℓ, K_max, λ₀, a₀, L_K)` — the `log n` being the price of the supremum.

**Proof formalization notes.** Discretize `[0,1]` on the grid `t_j = j/M`, `M = n⁴`:

1. *Grid maximum.* At each grid point, `∑ᵢ ξᵢW*ᵢ(t_j) = U(0)ᵀB_{t_j}⁻¹·η_j/√(nh)·…` where the
   coordinates of `η_j = (nh)^{-1/2}∑ᵢ ξᵢU(zᵢ)K(zᵢ)` are *linear combinations of i.i.d.
   Gaussians*, hence Gaussian with variance `≤ 2a₀K²_max·σ_ξ²`
   (`hasLaw_sum_mul_gaussianReal` + the design density bound). The inverse bound converts
   `|∑ξW*| ≤ ‖η_j‖·…/λ₀·(nh)^{-1/2}`, and `lintegral_iSup_normSq_gaussian_le` gives
   `E max_j ‖η_j‖² ≲ (ℓ+1)·vmax·log(√2·M(ℓ+1)) = O(log n)`.
2. *Increments.* Between grid points, `∑ᵢ|W*ᵢ(t) − W*ᵢ(t_j)| ≤ C_L·|t−t_j|/h³`
   (`lp_weight_lipschitz_sum`, from `SupNorm/Increments.lean`), so the continuum supremum
   exceeds the grid maximum by at most `max_i|ξ_i|·C_L·n^{-4}/h³`, whose second moment is
   `O(σ_ξ²·log n·n^{-8}/h⁶) = o(σ_ξ²·log n/(nh))` for `h ≥ 1/(2n)`.

The constant is existential with the stated dependence (by binder position before the
quantifiers over `n`, the design, the noise, and the sample space).

**Bibliographic comments.** The discretize-and-bound-the-maximum route to sup-norm rates is
classical; cf. C. J. Stone, *Ann. Statist.* **10** (1982), 1040–1053, and W. Härdle,
*Applied Nonparametric Regression* (Cambridge, 1990).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Sup-norm stochastic bound**: there is `C = C(ℓ, K_max, λ₀, a₀, L_K)` such that under
the standing design assumptions, a Lipschitz boxed kernel, and i.i.d. `N(0, v)` noise,
`E[(sup_{t∈[0,1]} |∑ᵢ ξᵢ·W*ᵢ(t)|)²] ≤ C·v·log n/(n·h)` for all `n ≥ 2`,
`1/(2n) ≤ h ≤ 1`. -/
theorem lp_supnorm_stochastic_le {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ) (v : ℝ≥0),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) →
        ∫⁻ ω, ENNReal.ofReal
            ((⨆ t : Set.Icc (0 : ℝ) 1, |∑ i, ξ i ω * lpWeight xdat K h ℓ (t : ℝ) i|) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
  sorry

end StatLean.NonparametricStatistics
