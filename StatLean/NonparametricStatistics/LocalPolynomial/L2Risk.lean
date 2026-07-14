import StatLean.NonparametricStatistics.LocalPolynomial.PointwiseRisk

/-!
# L² risk of the local polynomial estimator

The integrated version of the pointwise rate: with `h = α·n^{−1/(2β+1)}`, uniformly over
`f ∈ Σ(β, L)` on `[0,1]`,
$$ \mathbb E\,\|\hat f_n - f\|_2^2 \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}},
   \qquad \|g\|_2^2 = \int_0^1 g^2(t)\,dt, $$
with the same explicit constant as the pointwise bound.

**Proof formalization notes.** Tonelli swaps the sample-space and `t` integrals; the pointwise
MSE bound (`lp_pointwise_rate`) is uniform over `t ∈ [0,1]`, and `volume (Icc 0 1) = 1`, so
integrating costs nothing. Everything stays in `∫⁻`, so no measurability of the risk in `t`
is needed beyond joint measurability of the integrand (finite sums of measurable functions).

**Bibliographic comments.** C. J. Stone, "Optimal global rates of convergence for
nonparametric regression," *Ann. Statist.* **10** (1982), 1040–1053.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **L² rate of LP(`ℓ`) over `Σ(β, L)`**: with `h = α·n^{−1/(2β+1)}`,
`E ∫₀¹ (f̂(t) − f(t))² dt ≤ lpRateConst·n^{−2β/(2β+1)}`. -/
theorem lp_l2_rate {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin n → Ω → ℝ} {σmax2 : ℝ} {β L α : ℝ} {f : ℝ → ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hσ : 0 ≤ σmax2)
    (hn : 0 < n)
    -- LEAN-ONLY: rate-optimal bandwidth, packaged as an equation
    (hform : h = α * (n : ℝ) ^ (-(1 / (2 * β + 1))))
    -- LEAN-ONLY: side condition `h ≥ 1/(2n)`, satisfied for all large `n`
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- LEAN-ONLY: measurability of the kernel, needed for the Tonelli swap of the two risk
    -- integrals; standard regularity (all classical kernels qualify)
    (hKmeas : Measurable K)
    -- USER-INPUT: design in `[0,1]`, eigenvalue floor, boxed kernel, design density bound;
    -- the standing fixed-design assumptions
    (hx : ∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1)
    (heig : DesignEigenvalueLB xdat K h (holderIndex β) lam0)
    (hbox : KernelBoxed K Kmax)
    (hdens : DesignDensityBound xdat a₀)
    -- USER-INPUT: the regression function lies in `Σ(β, L)` on `[0,1]`
    (hf : MemHolderOn β L f (Set.Icc 0 1))
    -- LEAN-ONLY: measurability of the noise; standard regularity
    (hξm : ∀ i, Measurable (ξ i))
    -- USER-INPUT: independent centered noise with second moments ≤ `σ²_max`; the
    -- fixed-design regression model
    (hξi : iIndepFun ξ P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
    (hξ2 : ∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P ≤ ENNReal.ofReal σmax2) :
    ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        ((lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) t
          - f t) ^ 2)) ∂P
      ≤ ENNReal.ofReal (lpRateConst β L α σmax2 Kmax lam0 a₀
          * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  sorry

end StatLean.NonparametricStatistics
