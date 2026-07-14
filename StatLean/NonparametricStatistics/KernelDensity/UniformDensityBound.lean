import StatLean.NonparametricStatistics.KernelDensity.Bias
import StatLean.NonparametricStatistics.KernelDensity.AuxiliaryKernel

/-!
# Uniform boundedness of Hölder densities

Densities in a Hölder class are uniformly bounded:
$$ \sup_{x} \sup_{p \in \mathcal P(\beta, L)} p(x) \;\le\; p_{\max}(\beta, L) < \infty. $$

This is the hidden ingredient of the pointwise minimax rate: the variance bound needs
`p ≤ pmax`, and over the class this bound must be *derived*, not assumed — keeping it as a
hypothesis of the rate theorem would silently shrink the class.

**Proof formalization notes.** Apply the deterministic bias core
(`abs_integral_kernel_taylor_le`) with bandwidth `h = 1` and an auxiliary **bounded** kernel
`K*` of order `ℓ` supported in `[−1,1]` (`exists_bounded_kernel_of_order`):
`p(x) ≤ |∫K*(u)p(x+u)du| + C₂* ≤ sup|K*|·∫p + C₂* = sup|K*| + C₂*`, using `∫ p = 1` and
`p ≥ 0`. The compact support makes the `β`-moment of `K*` finite. The bound `pmax` is
existential (it depends on the auxiliary kernel construction), which suffices for its sole
consumer, the rate theorem.

**Bibliographic comments.** A classical remark in the pointwise risk analysis of kernel
estimators; folklore, implicit in E. Parzen, *Ann. Math. Statist.* **33** (1962), 1065–1076.
-/

namespace StatLean.NonparametricStatistics

/-- **Uniform bound on a Hölder density class**: there is `pmax = pmax(β, L)` bounding every
density of `P(β, L)` everywhere. -/
theorem holder_density_uniform_bound (β L : ℝ)
    -- USER-INPUT: positive smoothness and Hölder constant; class parameters
    (hβ : 0 < β) (hL : 0 < L) :
    ∃ pmax : ℝ, 0 < pmax ∧
      ∀ p : ℝ → ℝ, IsHolderDensity β L p → ∀ x, p x ≤ pmax := by
  sorry

end StatLean.NonparametricStatistics
