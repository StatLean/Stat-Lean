import StatLean.NonparametricStatistics.Regression.Defs
import StatLean.NonparametricStatistics.KernelDensity.Defs

/-!
# The kernel regression estimator as a ratio of density estimates

For a kernel of order `1` (so `∫K = 1` and `∫uK = 0`), the kernel regression estimator is the
plug-in conditional-mean formula built from kernel density estimates:
$$ f_n(x) \;=\; \frac{\int y\,\hat p_n(x, y)\,dy}{\hat p_n(x)} \qquad
   \text{whenever } \hat p_n(x) \ne 0, $$
where `p̂ₙ(x, y)` is the bivariate product-kernel estimate from the pairs `(Xᵢ, Yᵢ)` and
`p̂ₙ(x)` the marginal estimate from the `Xᵢ`. This identifies the locally-weighted average as
the natural estimator of `E[Y | X = x] = ∫y·p(x,y)dy / p(x)`.

**Proof formalization notes.** A purely algebraic/deterministic identity in the data vectors
(no probability): compute
`∫ y·K((Yᵢ−y)/h) dy = h·(Yᵢ·∫K − h·∫uK) = h·Yᵢ` by the change of variables `y = Yᵢ − hu`
(order-1 moments), then swap the finite sum with the integral and cancel the normalizations.
Integrability of `y ↦ y·K((Yᵢ−y)/h)` comes from the kernel's order-`1` integrability
(`integrable_pow` at `j = 0, 1`) via the same change of variables.

**Bibliographic comments.** E. A. Nadaraya, "On estimating regression," *Theory Probab. Appl.*
**9** (1964), 141–142; G. S. Watson, "Smooth regression analysis," *Sankhyā Ser. A* **26**
(1964), 359–372.
-/

open MeasureTheory

namespace StatLean.NonparametricStatistics

/-- **Kernel regression as a ratio of kernel density estimates**: for a kernel of order `1`,
positive bandwidth, and nonvanishing marginal estimate at `x`,
`nadarayaWatson xdat ydat K h x = (∫ y, y·p̂ₙ(x,y) dy) / p̂ₙ(x)`. -/
theorem nadarayaWatson_eq_kde_ratio {n : ℕ} (xdat ydat : Fin n → ℝ) {K : ℝ → ℝ}
    -- USER-INPUT: `K` is a kernel of order 1 (`∫K = 1`, `∫uK = 0`); the classical hypothesis
    -- making the bivariate plug-in formula collapse to the weighted average
    (hK : IsKernelOfOrder K 1)
    {h : ℝ}
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    {x : ℝ}
    -- USER-INPUT: nonvanishing marginal density estimate at `x`; the classical proviso of
    -- the ratio formula
    (hden : kdeData xdat K h x ≠ 0) :
    nadarayaWatson xdat ydat K h x
      = (∫ y, y * kde2Data xdat ydat K h x y) / kdeData xdat K h x := by
  sorry

end StatLean.NonparametricStatistics
