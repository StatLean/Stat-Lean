import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import StatLean.ComputationalStatistics.ForMathlib.PiMoments

/-!
# Multinomial resampling of weighted particles

The correctness core of the resampling step of sequential Monte Carlo: given a
weighted particle population `(x₁, w₁), …, (x_m, w_m)` with `Σ wᵢ = 1`, draw
`N` indices `A₁, …, A_N` i.i.d. `categorical w` and replace the population by
the equally-weighted `x_{A₁}, …, x_{A_N}`.  Resampling is *unbiased*: it
preserves the weighted empirical measure in expectation,

* `particleResampling_unbiased` —
  `E[(1/N)·Σⱼ g(x_{Aⱼ})] = Σᵢ wᵢ·g(xᵢ)`;
* `particleResampling_unbiased_integral` — the same, with the right-hand side
  written as `∫ g d(weightedMeasure w x)`;
* `particleResampling_measure_unbiased` — the setwise form
  `E[𝔽_N(x ∘ A)(s)] = (Σᵢ wᵢ δ_{xᵢ})(s)`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.5 (Monte Carlo sampling from the discrete
population carried by data; the multinomial resampling vector of ch. 4,
p. 84).  (`ECS §2.5`.)

**Proof formalization notes.**

* Conditioning on the particle population is formalized by treating `(x, w)`
  as parameters: the only randomness is the index draw
  `Measure.pi (fun _ : Fin N => categorical w)`, which *is* the conditional
  law given particles and weights.
* The sample space of indices is finite, so no integrability hypotheses are
  needed; simplex hypotheses on `w` are genuine user inputs.
* Sequential Monte Carlo itself (the propagate–reweight–resample recursion,
  Feynman–Kac laws) is deliberately out of scope for Round 1; this file is
  the reusable single-step correctness brick.

**Bibliographic comments.** Multinomial resampling enters the particle-filter
literature with N. Gordon, D. Salmond, A. F. M. Smith, "Novel approach to
nonlinear/non-Gaussian Bayesian state estimation," *IEE Proc. F* **140** (1993),
107–113; the unbiasedness property stated here is Lemma-level in Douc–Cappé,
"Comparison of resampling schemes for particle filtering," *ISPA* 2005.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {m N : ℕ} {x : Fin m → 𝓧}
  {w : Fin m → ℝ} {g : 𝓧 → ℝ}

/-- **Multinomial resampling is unbiased** (ECS §2.5, ch. 4 p. 84): drawing
`N` indices i.i.d. from `categorical w`, the resampled average of `g` has
conditional expectation the weighted average `Σᵢ wᵢ·g(xᵢ)`. -/
theorem particleResampling_unbiased [NeZero N]
    -- USER-INPUT: nonnegative particle weights; ECS §2.6
    (hw0 : ∀ i, 0 ≤ w i)
    -- USER-INPUT: normalized particle weights; ECS §2.6
    (hw1 : ∑ i, w i = 1) :
    ∫ a, mcEstimate g (x ∘ a) ∂(Measure.pi fun _ : Fin N => categorical w)
      = ∑ i, w i * g (x i) := by
  sorry

/-- **Multinomial resampling preserves the weighted measure in expectation**,
integral form: `E[(1/N)·Σⱼ g(x_{Aⱼ})] = ∫ g d(Σᵢ wᵢ δ_{xᵢ})`. -/
theorem particleResampling_unbiased_integral [NeZero N]
    -- USER-INPUT: nonnegative particle weights; ECS §2.6
    (hw0 : ∀ i, 0 ≤ w i)
    -- USER-INPUT: normalized particle weights; ECS §2.6
    (hw1 : ∑ i, w i = 1)
    -- LEAN-ONLY: strong measurability, needed to integrate against Diracs
    (hg : StronglyMeasurable g) :
    ∫ a, mcEstimate g (x ∘ a) ∂(Measure.pi fun _ : Fin N => categorical w)
      = ∫ z, g z ∂(weightedMeasure w x) := by
  sorry

/-- **Setwise form**: the resampled empirical measure of any measurable set is,
in expectation, the weighted measure of the set. -/
theorem particleResampling_measure_unbiased [NeZero N]
    -- USER-INPUT: nonnegative particle weights; ECS §2.6
    (hw0 : ∀ i, 0 ≤ w i)
    -- USER-INPUT: normalized particle weights; ECS §2.6
    (hw1 : ∑ i, w i = 1) {s : Set 𝓧}
    -- LEAN-ONLY: measurability of the event (regularity)
    (hs : MeasurableSet s) :
    ∫ a, (empiricalMeasure (x ∘ a) s).toReal
        ∂(Measure.pi fun _ : Fin N => categorical w)
      = (weightedMeasure w x s).toReal := by
  sorry

end StatLean.ComputationalStatistics
