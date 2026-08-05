import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.CondCharFun
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Brown/Hall–Heyde martingale central limit theorem

**Main theorem** (`mds_clt`): a martingale-difference triangular array whose
conditional variance process converges in probability to a constant `σ²` and which
satisfies the (unconditional) Lindeberg condition has asymptotically `N(0, σ²)` row
sums — stated through pointwise characteristic-function convergence.

This is the probability pillar commissioned for Hannan's Theorem 3.2 (FY §3.2): the
ARMA quasi-score at the true parameter is a stationary ergodic martingale-difference
sequence, and the array `X_{n,i} = ξ_i/√n` fed into `mds_clt` yields asymptotic
normality of the score (batch D wires this through `ARMA/ScoreAnalysis`).

**Assembly plan** (from `MartingaleCLT/CondCharFun.lean`):
1. `norm_integral_exp_rowSum_sub_prod_le` reduces `E e^{iuS_n}` to the Taylor product
   at cost of the Lindeberg sums (choose `ε = ε_n → 0` slowly);
2. `tendsto_integral_prod_one_sub_condVar` sends the Taylor product to `e^{−u²σ²/2}`
   (uniform negligibility of the conditional variances follows from Lindeberg +
   variance convergence — derive, don't assume);
3. rewrite `charFun (gaussianReal 0 σ²) u = e^{−u²σ²/2}`.
The truncation/stopping refinement of Hall–Heyde (replacing the L¹-boundedness input
by a stopping-time argument) is NOT needed at this generality: the `hbdd` input of
step 2 is derived from `hvar` + `hlind` via the row variance identity
`Σᵢ E Xᵢ² = E V_n`.

**Reference.** B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist.
**42** (1971), 59–66, Thm 2; P. Hall & C. C. Heyde, *Martingale Limit Theory and Its
Application*, Academic Press, 1980, Thm 3.2/Cor 3.1. (`Hall–Heyde Thm 3.2`.)

**Bibliographic comments.** Martingale CLTs originate with P. Lévy (1935, 1937);
Billingsley (1961) and Ibragimov (1963) proved the stationary-ergodic case; Brown
(1971) isolated the conditional-variance normalization; Hall–Heyde (1980) is the
standard reference form. The charFun proof implemented here is Brown's original
telescope, with the conditional Taylor estimates of `CondCharFun.lean`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The Brown/Hall–Heyde martingale CLT** (charFun form): martingale-difference
array + conditional variance `→p σ²` + Lindeberg ⇒ row sums are asymptotically
`N(0, σ²)`. -/
theorem mds_clt [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: the Lindeberg condition; Hall–Heyde (3.7) unconditional form
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map (mdsRowSum k X n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

/-- **Stationary-sequence corollary** (the Hannan-facing form): a single
martingale-difference sequence `ξ` against a filtration `G` with
`n⁻¹ Σ_{i<n} E[ξᵢ² | Gᵢ] →p σ²` and the averaged Lindeberg property has
`S_n/√n →d N(0, σ²)`. Instantiates `mds_clt` at `X_{n,i} = ξ_i/√n`. -/
theorem mds_clt_sequence [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → ℝ} {G : ℕ → MeasurableSpace Ω}
    (hle : ∀ i, G i ≤ ‹MeasurableSpace Ω›) (hmono : Monotone G)
    (hadapted : ∀ i, Measurable[G (i + 1)] (ξ i))
    (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    -- USER-INPUT: martingale-difference property; Hall–Heyde Thm 3.2 setting
    (hmds : ∀ i, μ[ξ i | G i] =ᵐ[μ] 0)
    {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: averaged conditional variance → σ² in probability
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
          (∑ i ∈ Finset.range n, μ[fun ω' => ξ i ω' ^ 2 | G i] ω) - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: averaged Lindeberg condition
    (hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          ∫ ω in {ω | ε * Real.sqrt n ≤ |ξ i ω|}, (ξ i ω) ^ 2 ∂μ)
        atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, ξ i ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

end StatLean.TimeSeries
