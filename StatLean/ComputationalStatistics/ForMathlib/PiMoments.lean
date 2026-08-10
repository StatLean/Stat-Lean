import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProductMeasure

/-!
# Moments and limits of coordinate averages under product measures

The first- and second-moment identities and the strong-law limit for the average
`x ↦ (1/n)·Σᵢ g(xᵢ)` of a function of the coordinates under the canonical i.i.d.
laws `Measure.pi (fun _ : Fin n => P)` and `Measure.infinitePi (fun _ : ℕ => P)`:

* `integral_avg_eval_pi` — `E[X̄] = μ`;
* `variance_avg_eval_pi` — `Var(X̄) = σ²/n`;
* `integral_sq_dev_avg_eval_pi` — the mean-squared error of the average is `σ²/n`;
* `tendsto_avg_eval_infinitePi` — `X̄ₙ → μ` almost surely (SLLN transport).

These four facts are used throughout StatLean (bootstrap root laws, Lindeberg
CLT bricks, empirical-process parameter estimation) but were previously inlined
at each use site from `ProbabilityTheory.IndepFun.variance_sum`; this file
packages them once, at the bottom layer, for reuse.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.8)–(2.9), and
the law-of-large-numbers discussion on p. 53).  (`ECS §X.Y`.)

**Proof formalization notes.**

* The sample space is the canonical product; the coordinate maps are
  measure-preserving (`MeasureTheory.measurePreserving_eval`) and independent
  (`ProbabilityTheory.iIndepFun_pi`) — both loaded from the pinned Mathlib, not
  reproved.
* `[NeZero n]` rules out the `n = 0` junk value `(0 : ℝ)⁻¹ = 0` of the average.
* The strong-law statement is in `Finset.range`-sum form on the sequence space
  `ℕ → 𝓧`; the `Fin`-indexed Monte Carlo wrapper lives in
  `MonteCarlo/Estimation.lean`.

**Bibliographic comments.** The variance identity for sample means is classical
(Laplace); the almost-sure law of large numbers is Kolmogorov's (1933), here
obtained from Mathlib's Etemadi-style `ProbabilityTheory.strong_law_ae_real`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ} {g : 𝓧 → ℝ}

/-- **Unbiasedness of the coordinate average** (ECS §2.2, eq. (2.8)): under the
i.i.d. product law, the average of `g` over the coordinates integrates to
`∫ g dP`. -/
theorem integral_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P) :
    ∫ x, (n : ℝ)⁻¹ * ∑ i, g (x i) ∂(Measure.pi fun _ : Fin n => P)
      = ∫ z, g z ∂P := by
  sorry

/-- **Variance of the coordinate average** (ECS §2.2, eq. (2.9) discussion):
`Var(X̄) = Var_P(g)/n` under the i.i.d. product law. -/
theorem variance_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    variance (fun x : Fin n → 𝓧 => (n : ℝ)⁻¹ * ∑ i, g (x i))
        (Measure.pi fun _ : Fin n => P)
      = variance g P / n := by
  sorry

/-- **Mean-squared error of the coordinate average** (ECS §2.2): since the
average is unbiased, its mean-squared deviation from `∫ g dP` is `Var_P(g)/n`. -/
theorem integral_sq_dev_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    ∫ x, ((n : ℝ)⁻¹ * ∑ i, g (x i) - ∫ z, g z ∂P) ^ 2
        ∂(Measure.pi fun _ : Fin n => P)
      = variance g P / n := by
  sorry

/-- **Strong law for coordinate averages** (ECS §2.2, p. 53): on the canonical
sequence space, the running averages of `g` over the coordinates converge to
`∫ g dP` almost surely. -/
theorem tendsto_avg_eval_infinitePi
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P)
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hgm : Measurable g) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => P),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (ω i))
        atTop (𝓝 (∫ z, g z ∂P)) := by
  sorry

end StatLean.ComputationalStatistics
