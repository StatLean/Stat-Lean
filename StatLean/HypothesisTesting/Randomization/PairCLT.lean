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

/-! ### Integrating a bounded test function against `randPairLaw` -/

/-- **`randPairLaw` unfolded inside an integral.** For a bounded measurable `F`, the integral
against the doubly randomized law is the group average of the integrals of `F` composed with
the two randomized statistics. -/
lemma integral_randPairLaw {𝓧 Z : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Z]
    {G : Type*} [Group G] [Fintype G] [MulAction G 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P]
    (T : 𝓧 → Z) (hT : ∀ g : G, Measurable fun x : 𝓧 => T (g • x))
    (F : Z × Z → ℂ) (hF : Measurable F) (hFb : ∀ z, ‖F z‖ ≤ 1) :
    ∫ z, F z ∂(randPairLaw G T P)
      = ((Fintype.card G : ℂ) ^ 2)⁻¹ *
        ∑ g : G, ∑ g' : G, ∫ x, F (T (g • x), T (g' • x)) ∂P := by
  classical
  have hint : ∀ (ρ : Measure (Z × Z)), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ _
    exact Integrable.mono' (integrable_const (1 : ℝ)) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  have hpair : ∀ g g' : G, Measurable fun x : 𝓧 => (T (g • x), T (g' • x)) :=
    fun g g' => (hT g).prodMk (hT g')
  haveI hprob : ∀ g g' : G,
      IsProbabilityMeasure (P.map fun x : 𝓧 => (T (g • x), T (g' • x))) :=
    fun g g' => Measure.isProbabilityMeasure_map (hpair g g').aemeasurable
  rw [randPairLaw, integral_smul_measure,
    integral_finset_sum_measure (fun g _ => integrable_finset_sum_measure.2
      (fun g' _ => hint _ inferInstance))]
  have hstep : ∀ g : G, ∫ z, F z ∂(∑ g' : G, P.map fun x : 𝓧 => (T (g • x), T (g' • x)))
      = ∑ g' : G, ∫ x, F (T (g • x), T (g' • x)) ∂P := by
    intro g
    rw [integral_finset_sum_measure (fun g' _ => hint _ inferInstance)]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [integral_map (hpair g g').aemeasurable hF.aestronglyMeasurable]
  simp_rw [hstep]
  have hcoef : ((((Fintype.card G : ℝ≥0∞)) ^ 2)⁻¹).toReal = ((Fintype.card G : ℝ) ^ 2)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hc : ((((Fintype.card G : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) = ((Fintype.card G : ℂ) ^ 2)⁻¹ := by
    push_cast
    ring
  rw [hcoef, ← hc]
  exact RCLike.real_smul_eq_coe_mul _ _

/-! ### The sign-change group acting on vector-valued data -/

/-- The sign-change action on vector data, written out: `(ε • x) i = εᵢ • xᵢ`, with the
integer unit read as a real scalar. -/
lemma signChange_smul_apply_vec {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (ε : Fin n → ℤˣ) (x : Fin n → V) (i : Fin n) :
    (ε • x) i = ((ε i : ℤ) : ℝ) • x i := by
  change ((ε i : ℤ)) • x i = _
  rw [← Int.cast_smul_eq_zsmul ℝ]

/-- The sign-change group on `n` coordinates has `2ⁿ` elements. -/
private lemma card_signPattern (n : ℕ) : Fintype.card (Fin n → ℤˣ) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_units_int]

section SignSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The real linear form `y ↦ s⟪y,t₁⟫ + s'⟪y,t₂⟫` obtained by pairing the data with the two
test directions through a sign pair. Averaging over the four sign pairs is what makes the two
components of `randPairLaw` decouple. -/
private noncomputable def signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) : ℝ :=
  ((s : ℤ) : ℝ) * ⟪y, (WithLp.ofLp t).1⟫ + ((s' : ℤ) : ℝ) * ⟪y, (WithLp.ofLp t).2⟫

private lemma continuous_signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Continuous (signDir t s s') := by
  have h1 : Continuous fun y : E => ⟪y, (WithLp.ofLp t).1⟫ :=
    (continuous_id (X := E)).inner continuous_const
  have h2 : Continuous fun y : E => ⟪y, (WithLp.ofLp t).2⟫ :=
    (continuous_id (X := E)).inner continuous_const
  exact (h1.const_mul _).add (h2.const_mul _)

private lemma measurable_signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Measurable (signDir t s s') := (continuous_signDir t s s').measurable

/-- Pairing the sign-flipped normalized sum with a test direction. -/
private lemma inner_signSum (n : ℕ) (ε : Fin n → ℤˣ) (x : Fin n → E) (t : E) :
    ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, t⟫
      = ∑ i, (Real.sqrt (n : ℝ))⁻¹ * (((ε i : ℤ) : ℝ) * ⟪x i, t⟫) := by
  rw [real_inner_smul_left, sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [signChange_smul_apply_vec, real_inner_smul_left]

/-- The joint exponential factorizes across coordinates. -/
private lemma exp_inner_pair_eq_prod (n : ℕ) (t : WithLp 2 (E × E)) (ε ε' : Fin n → ℤˣ)
    (x : Fin n → E) :
    Complex.exp (((⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, (WithLp.ofLp t).1⟫
        + ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε' • x) i, (WithLp.ofLp t).2⟫ : ℝ) : ℂ) * Complex.I)
      = ∏ i, Complex.exp
          ((((Real.sqrt (n : ℝ))⁻¹ * signDir t (ε i) (ε' i) (x i) : ℝ) : ℂ) * Complex.I) := by
  have hexp : (⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, (WithLp.ofLp t).1⟫
      + ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε' • x) i, (WithLp.ofLp t).2⟫ : ℝ)
      = ∑ i, (Real.sqrt (n : ℝ))⁻¹ * signDir t (ε i) (ε' i) (x i) := by
    rw [inner_signSum, inner_signSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold signDir
    ring
  rw [hexp, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

end SignSum

end StatLean.HypothesisTesting
