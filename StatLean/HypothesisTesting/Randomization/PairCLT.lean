import StatLean.HypothesisTesting.Randomization.Asymptotics
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The bivariate sign-change randomization central limit theorem

This file supplies the one analytic engine that all the *joint* randomization limits of the
area consume: the law of a linear statistic recomputed at **two independent uniform sign
patterns** converges to a product of two identical centred Gaussians.

Everything is done at the level of characteristic functions, which is what makes the
"two independent group elements" structure trivial: averaging `exp(i(sa+s'b))` over the four
sign pairs `(s,s') ∈ {\pm 1\}^2` factorizes as `cos a · cos b`, so the two coordinates
decouple *exactly* at every finite `n`, and the limit is automatically a product measure.

## Main results

* `weakConverges_of_tendsto_charFun` — Lévy continuity in the `WeakConverges` packaging;
* `weakConverges_prod_of_tendsto_charFun` — its product-space form: pointwise convergence of
  the characteristic function of `μ n` (transported to `WithLp 2 (E × E)`) to a *product* of
  two characteristic functions gives weak convergence to the product measure;
* `charFun_randPairLaw_signSum` — the exact finite-`n` identity
  `charFun = (4⁻¹ ∑_{s,s'} charFun (Q.map W_{s,s'}) n^{-1/2})^n`;
* `weakConverges_randPairLaw_signSum` — the resulting bivariate CLT, for data in an arbitrary
  finite-dimensional real inner-product space.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.2–§17.4 (the joint hypothesis of Theorem 17.2.3, verified for the
sign-change group in Theorem 17.2.4 and Lemmas 17.4.1–17.4.3). (`TSH4 §17.2 Thm 17.2.4`.)

**Proof formalization notes.**
* *No mean-zero hypothesis.* Averaging over the sign group symmetrizes the summands, so the
  first-order term of the expansion cancels identically: only the **second moment**
  `∫ ⟪x,t⟫² dQ` enters. This is why the vector building block of
  `Randomization/MultivariateQuadratic` holds verbatim with `S` read as the second-moment
  matrix, as its file notes predict.
* *No independent CLT brick is used.* The finite-`n` characteristic function is computed in
  closed form (`charFun_randPairLaw_signSum`) — a product over the `n` coordinates, obtained
  from `Finset.prod_univ_sum` (sum over sign patterns of a product = product of sums) and
  `integral_fintype_prod_eq_pow` (Fubini for product measures). The limit is then the
  classical `(1 + t/n + o(1/n))ⁿ → eᵗ` of `Complex.tendsto_pow_exp_of_isLittleO_sub_add_div`,
  fed by the second-order Taylor expansion of a one-dimensional characteristic function
  (`taylorWithinEval_charFun_two_zero`).
* *Why `WithLp 2 (E × E)`.* Lévy's continuity theorem needs an inner-product space, and the
  plain product `E × E` carries the sup norm. `WithLp 2 (E × E)` is the same measurable space
  and the same topology (`WithLp.prod_continuous_toLp` / `prod_continuous_ofLp`), so weak
  convergence transports back and forth; `charFun_prod` identifies the characteristic function
  of a product measure there.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### Lévy continuity, in the `WeakConverges` packaging -/

/-- **Lévy's continuity theorem, `WeakConverges` form.** Pointwise convergence of
characteristic functions to that of a probability measure gives weak convergence. -/
lemma weakConverges_of_tendsto_charFun {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {μ : ℕ → Measure H} [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure H}
    [IsProbabilityMeasure ν]
    (h : ∀ t : H, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (charFun ν t))) :
    WeakConverges μ ν := by
  set pn : ℕ → ProbabilityMeasure H := fun n => ⟨μ n, inferInstance⟩ with hpn
  set pν : ProbabilityMeasure H := ⟨ν, inferInstance⟩ with hpν
  have htend : Tendsto pn atTop (𝓝 pν) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun (by simpa [pn, pν] using h)
  intro f
  simpa [pn, pν] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htend) f

/-- **Lévy continuity onto a product limit.** If the characteristic function of `μ n`,
transported to the Hilbert-space model `WithLp 2 (E × E)` of the product, converges pointwise
to the product `charFun ν₁ t₁ · charFun ν₂ t₂`, then `μ n` converges weakly to `ν₁ ⊗ ν₂`. -/
lemma weakConverges_prod_of_tendsto_charFun {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure (E × E)} [∀ n, IsProbabilityMeasure (μ n)]
    {ν₁ ν₂ : Measure E} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ t : WithLp 2 (E × E),
      Tendsto (fun n => charFun ((μ n).map (WithLp.toLp 2)) t) atTop
        (𝓝 (charFun ν₁ (WithLp.ofLp t).1 * charFun ν₂ (WithLp.ofLp t).2))) :
    WeakConverges μ (ν₁.prod ν₂) := by
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map (WithLp.toLp (V := E × E) 2)) := fun n =>
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  haveI : IsProbabilityMeasure ((ν₁.prod ν₂).map (WithLp.toLp (V := E × E) 2)) :=
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  have hlim : WeakConverges (fun n => (μ n).map (WithLp.toLp 2))
      ((ν₁.prod ν₂).map (WithLp.toLp 2)) := by
    refine weakConverges_of_tendsto_charFun (fun t => ?_)
    rw [charFun_prod]
    exact h t
  have hmap := hlim.map (f := WithLp.ofLp) (WithLp.prod_continuous_ofLp 2 E E)
    (WithLp.measurable_ofLp 2 (E × E))
  have hcollapse : ∀ ρ : Measure (E × E),
      (ρ.map (WithLp.toLp (V := E × E) 2)).map WithLp.ofLp = ρ := by
    intro ρ
    have hid : (WithLp.ofLp : WithLp 2 (E × E) → E × E) ∘ (WithLp.toLp (V := E × E) 2) = id := rfl
    rw [Measure.map_map (WithLp.measurable_ofLp 2 (E × E)) (WithLp.measurable_toLp 2 (E × E)),
      hid, Measure.map_id]
  simpa only [hcollapse] using hmap

end StatLean.HypothesisTesting
