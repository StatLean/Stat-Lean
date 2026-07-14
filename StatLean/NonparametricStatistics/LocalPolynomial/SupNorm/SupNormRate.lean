import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.StochasticTerm
import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.Increments
import StatLean.NonparametricStatistics.LocalPolynomial.PointwiseRisk

/-!
# Sup-norm rate of the local polynomial estimator

Over the Hölder class `Σ(β, L)` on `[0,1]`, with i.i.d. centered Gaussian noise, a Lipschitz
boxed kernel, and the sup-norm bandwidth `h = α·(log n/n)^{1/(2β+1)}`:
$$ \mathbb E\bigl[\ \|\hat f_n - f\|_\infty^2\ \bigr]
   \;\le\; C\,\Bigl(\frac{\log n}{n}\Bigr)^{\frac{2\beta}{2\beta+1}}, $$
uniformly over the class — the pointwise rate deteriorates by exactly a `log n` factor, the
classical price of the supremum (and this rate is optimal for sup-norm loss).

**Proof formalization notes.** Split
`‖f̂ − f‖∞² ≤ 2·(sup_t |∑ᵢ ξᵢW*ᵢ(t)|)² + 2·(sup_t |bias(t)|)²`: the bias sup is
`q₁·h^β` pointwise-uniformly (`lp_bias_deterministic`), the stochastic sup is
`C·σ_ξ²·log n/(nh)` (`lp_supnorm_stochastic_le`, whose proof uses
`lp_weight_lipschitz_sum`); substituting the bandwidth balances
`h^{2β} = (log n/n)^{2β/(2β+1)}` against `log n/(nh) = α^{-(2β+1)}·…·(log n/n)^{2β/(2β+1)}`.
The supremum is a genuine `⨆` over `[0,1]`; no measurability is needed since the risk is a
lower Lebesgue integral. The constant is existential with dependence
`(β, L, α, K, λ₀, a₀, σ_ξ)` fixed by binder position.

**Bibliographic comments.** Sup-norm rates with the `(log n/n)^{β/(2β+1)}` phenomenon go back
to I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic Theory*
(Springer, 1981), and C. J. Stone, *Ann. Statist.* **10** (1982), 1040–1053.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Sup-norm rate of LP(`ℓ`) over `Σ(β, L)`** with Gaussian noise and bandwidth
`h = α·(log n/n)^{1/(2β+1)}`: there is `C` (depending only on the displayed fixed parameters)
with `E‖f̂ − f‖∞² ≤ C·(log n/n)^{2β/(2β+1)}` for all admissible `n`, designs, noise, and
`f ∈ Σ(β, L)`. -/
theorem lp_supnorm_rate {β L α : ℝ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ} {v : ℝ≥0}
    -- USER-INPUT: class, tuning, and design parameters; classical inputs
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n →
      ∀ {h : ℝ},
        -- LEAN-ONLY: the sup-norm-optimal bandwidth, packaged as an equation
        h = α * (Real.log n / n) ^ ((1 : ℝ) / (2 * β + 1)) →
        -- LEAN-ONLY: side conditions, satisfied for all large `n`
        1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h (holderIndex β) lam0 →
        DesignDensityBound xdat a₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) →
      ∀ {f : ℝ → ℝ}, MemHolderOn β L f (Set.Icc 0 1) →
        ∫⁻ ω, ENNReal.ofReal
            ((⨆ t : Set.Icc (0 : ℝ) 1,
              |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ)
                - f (t : ℝ)|) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (Real.log n / n) ^ (2 * β / (2 * β + 1))) := by
  sorry

end StatLean.NonparametricStatistics
