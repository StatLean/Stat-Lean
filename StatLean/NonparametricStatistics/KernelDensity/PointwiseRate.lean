import StatLean.NonparametricStatistics.KernelDensity.Variance
import StatLean.NonparametricStatistics.KernelDensity.Bias
import StatLean.NonparametricStatistics.KernelDensity.UniformDensityBound

/-!
# Pointwise minimax rate of the kernel density estimator over Hölder classes

With bandwidth `h = α·n^{−1/(2β+1)}`, the kernel estimator attains, **uniformly over the
point `x₀` and the density class `P(β, L)`**, the pointwise rate
$$ \sup_{x_0}\ \sup_{p \in \mathcal P(\beta,L)}
   \mathbb E_p\bigl[(\hat p_n(x_0) - p(x_0))^2\bigr] \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}}
   \qquad (n \ge 1), $$
with `C = C(β, L, α, K)`. (The rate `n^{−β/(2β+1)}` is optimal over the class; lower bounds
are minimax-theory material outside this area.)

**Proof formalization notes.** MSE = bias² + variance (`kdeMseAt_eq_bias_sq_add_variance`);
the bias term is `(C₂·h^β)²` (`kde_bias_abs_le`), the variance term `C₁/(nh)`
(`kde_variance_le`) with `pmax` supplied *internally* by `holder_density_uniform_bound` — the
uniform boundedness of the class is derived, not assumed. Substituting the bandwidth gives
`C = C₂²α^{2β} + C₁/α`; since `pmax` (inside `C₁`) is existential, the headline constant is
existential too, with the stated dependence. Uniformity in `x₀`, `p`, and the underlying
probability space is by quantifier position: `C` is chosen before them.

**Bibliographic comments.** The pointwise rate `n^{−2β/(2β+1)}` for kernel estimators over
smoothness classes is classical, going back to M. Rosenblatt, *Ann. Math. Statist.* **27**
(1956), 832–837, and E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076, with the
higher-order-kernel form standard since the 1960s–70s (cf. C. J. Stone, *Ann. Statist.* **8**
(1980), 1348–1360, for optimality).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **Pointwise rate over the Hölder density class**: with `h = α·n^{−1/(2β+1)}` there is a
constant `C = C(β, L, α, K)` such that for every `n ≥ 1`, every point, every density of
`P(β, L)`, and every i.i.d. sample of size `n`,
`E[(p̂ₙ(x₀) − p(x₀))²] ≤ C·n^{−2β/(2β+1)}`. -/
theorem kde_pointwise_rate {β L α : ℝ}
    -- USER-INPUT: positive smoothness, Hölder constant, and bandwidth scale; class and
    -- tuning parameters
    (hβ : 0 < β) (hL : 0 < L) (hα : 0 < α)
    {K : ℝ → ℝ}
    -- USER-INPUT: `K` is a kernel of order `ℓ = holderIndex β`; classical bias-reduction
    -- condition (cf. Parzen 1962)
    (hK : IsKernelOfOrder K (holderIndex β))
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: square-integrable kernel; classical variance-bound input
    (hK2 : Integrable fun u => (K u) ^ 2)
    -- USER-INPUT: finite `β`-moment of the kernel; classical bias-bound input
    (hKβ : Integrable fun u => |u| ^ β * |K u|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ) (p : ℝ → ℝ) (x₀ : ℝ),
        1 ≤ n →
        IsIIDSample P X (densityMeasure p) →
        (∀ i, Measurable (X i)) →
        IsHolderDensity β L p →
        kdeMseAt P X K (α * (n : ℝ) ^ (-(1 / (2 * β + 1)))) p x₀
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  sorry

end StatLean.NonparametricStatistics
