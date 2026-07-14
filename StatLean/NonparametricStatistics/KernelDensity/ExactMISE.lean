import StatLean.NonparametricStatistics.KernelDensity.MISEVariance
import StatLean.NonparametricStatistics.KernelDensity.MISEBias

/-!
# Exact asymptotic MISE of the kernel density estimator

For a twice (weakly) differentiable density and a kernel of order `1` with `S_K = ∫u²K ≠ 0`:
$$ \mathrm{MISE} \;=\; \Bigl(\frac{1}{nh}\int K^2
     + \frac{h^4}{4}\,S_K^2\int (p'')^2\Bigr)\bigl(1 + o(1)\bigr), $$
with `o(1)` independent of `n` and vanishing as `h → 0`. Minimizing the main term in `h` (and
then over nonnegative kernels) is the classical route to the optimal-bandwidth formula and to
the parabolic (Epanechnikov) kernel; the theorem is stated here in the ε-form
$$ \bigl|\mathrm{MISE} - A(n,h)\bigr| \;\le\; \varepsilon\,\Bigl(\frac{1}{nh} + h^4\Bigr),
   \qquad 0 < h < h_0(\varepsilon),\ n \ge 1, $$
which is equivalent to the multiplicative form because `A(n,h) ≍ (nh)⁻¹ + h⁴` (both
coefficients `∫K² > 0` and `S_K²∫(p'')² > 0` are bounded away from zero; the equivalence is
recorded in the batch ledger).

**Proof formalization notes.** MISE decomposes exactly as `∫b² + ∫σ²`
(`kdeMise_eq_integrated`, Tonelli plus the a.e.-`x` bias–variance decomposition); the variance
part is pinned by `kde_integrated_variance_le` / `kde_integrated_variance_ge` (correction
`O(1/n) ≤ (nh)·h·…` absorbed into `ε/(nh)` for small `h`), and the bias part by
`kde_integrated_sq_bias_asymptotic`. The `L²` hypothesis on `p` feeding the variance lower
bound is inherited (documented input).

**Bibliographic comments.** G. S. Watson and M. R. Leadbetter, *Ann. Math. Statist.* **34**
(1963), 480–491 (exact MISE); M. S. Bartlett, *Sankhyā Ser. A* **25** (1963), 245–254, and
V. A. Epanechnikov, *Theory Probab. Appl.* **14** (1969), 153–158 (second-order form and
optimal kernel); the fixed-density optimality critique built on this expansion is due to
L. D. Brown, M. G. Low and L. H. Zhao, "Superefficiency in nonparametric function estimation,"
*Ann. Statist.* **25** (1997), 2607–2625.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- The main term of the exact asymptotic MISE:
`A(n, h) = (nh)⁻¹·∫K² + (h⁴/4)·(∫u²K)²·∫w²`. -/
noncomputable def kdeMiseMain (K w : ℝ → ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2)
    + h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * ∫ x, (w x) ^ 2

/-- **Exact MISE decomposition**: `MISE = ∫ b²(x) dx + ∫ σ²(x) dx` (Tonelli plus the
pointwise bias–variance decomposition, valid a.e. in `x`). -/
theorem kdeMise_eq_integrated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ} {p K : ℝ → ℝ} {h : ℝ}
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: i.i.d. sample with density `p`; the sampling model
    (hs : IsIIDSample P X (densityMeasure p))
    -- LEAN-ONLY: measurability; standard regularity
    (hX : ∀ i, Measurable (X i)) (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (hK : Measurable K)
    -- USER-INPUT: integrable and square-integrable kernel; classical inputs
    (hK1 : Integrable K) (hK2 : Integrable fun u => (K u) ^ 2) :
    kdeMise P X K h p
      = (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
        + ∫⁻ x, kdeVarianceAt P X K h x := by
  sorry

/-- **Exact asymptotic MISE**: under second-order smoothness of `p` and a kernel of order `1`
with `S_K ≠ 0`, for every `ε > 0` there is `h₀ > 0` such that for all `0 < h < h₀` and all
`n ≥ 1` (uniformly in `n`):
`ofReal (A(n,h) − ε·((nh)⁻¹ + h⁴)) ≤ MISE ≤ ofReal (A(n,h) + ε·((nh)⁻¹ + h⁴))`,
where `A = kdeMiseMain K w n h`. -/
theorem kde_exact_mise {p K w : ℝ → ℝ}
    -- USER-INPUT: `p` is a probability density; the sampling model
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    -- USER-INPUT: `p` is differentiable with absolutely continuous derivative and a.e.
    -- second derivative `w`; second-order smoothness inputs
    (hp1 : Differentiable ℝ p) (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    -- USER-INPUT: square-integrable second derivative; second-order smoothness input
    (hw2 : MemLp w 2 volume)
    -- USER-INPUT: square-integrable density; input of the exact variance asymptotics
    -- (documented: derivable in principle, kept as an input in this batch)
    (hp2 : MemLp p 2 volume)
    -- USER-INPUT: kernel of order 1 with nonvanishing second moment `S_K ≠ 0`; classical
    -- inputs of the second-order expansion
    (hK : IsKernelOfOrder K 1) (hSK : (∫ u, u ^ 2 * K u) ≠ 0)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: square-integrable kernel and finite second moment; classical inputs
    (hK2 : Integrable fun u => (K u) ^ 2) (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), 1 ≤ n →
        IsIIDSample P X (densityMeasure p) → (∀ i, Measurable (X i)) →
          ENNReal.ofReal (kdeMiseMain K w n h - ε * (((n : ℝ) * h)⁻¹ + h ^ 4))
              ≤ kdeMise P X K h p ∧
            kdeMise P X K h p
              ≤ ENNReal.ofReal (kdeMiseMain K w n h + ε * (((n : ℝ) * h)⁻¹ + h ^ 4)) := by
  sorry

end StatLean.NonparametricStatistics
