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

/-- A double sum over the two-element group `ℤˣ`, written out. -/
private lemma sum_units_int {M : Type*} [AddCommMonoid M] (f : ℤˣ → ℤˣ → M) :
    (∑ s : ℤˣ, ∑ s' : ℤˣ, f s s') = f 1 1 + f 1 (-1) + (f (-1) 1 + f (-1) (-1)) := by
  classical
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ,
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]

section SignSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

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

/-- The single-coordinate factor of the randomized characteristic function. -/
private noncomputable def signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) : ℂ :=
  Complex.exp ((((Real.sqrt (n : ℝ))⁻¹ * signDir t s s' y : ℝ) : ℂ) * Complex.I)

private lemma measurable_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Measurable (signFactor n t s s') := by
  unfold signFactor
  exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    ((continuous_signDir t s s').const_mul _)).mul continuous_const)).measurable

private lemma norm_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) :
    ‖signFactor n t s s' y‖ = 1 := by
  unfold signFactor
  exact Complex.norm_exp_ofReal_mul_I _

/-- Sum over sign patterns of a product = product of the coordinatewise sums, applied to the
two independent sign vectors. -/
private lemma prod_sum_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (x : Fin n → E) :
    ∏ i, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' (x i))
      = ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
          ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
  classical
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ℤˣ))
    (fun i s => ∑ s' : ℤˣ, signFactor n t s s' (x i)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ℤˣ))
    (fun i s' => signFactor n t (ε i) s' (x i)), Fintype.piFinset_univ]

/-- **The exact characteristic function of the sign-change randomized pair.**
At every finite `n` the joint characteristic function of the pair
`(n^{-1/2}∑ᵢεᵢXᵢ, n^{-1/2}∑ᵢε'ᵢXᵢ)` is the `n`-th power of the four-term sign average of
one-dimensional characteristic functions. -/
private lemma charFun_randPairLaw_signSum (Q : Measure E) [IsProbabilityMeasure Q]
    (n : ℕ) (t : WithLp 2 (E × E)) :
    charFun ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => Q)).map (WithLp.toLp 2)) t
      = ((4 : ℂ)⁻¹ * ∑ s : ℤˣ, ∑ s' : ℤˣ,
          charFun (Q.map (signDir t s s')) (Real.sqrt (n : ℝ))⁻¹) ^ n := by
  classical
  set u : ℝ := (Real.sqrt (n : ℝ))⁻¹ with hudef
  set T : (Fin n → E) → E := fun x => u • ∑ i, x i with hTdef
  set πQ : Measure (Fin n → E) := Measure.pi fun _ : Fin n => Q with hπQ
  -- The bounded test function on the product.
  set F : E × E → ℂ := fun z =>
    Complex.exp (((⟪z.1, (WithLp.ofLp t).1⟫ + ⟪z.2, (WithLp.ofLp t).2⟫ : ℝ) : ℂ) * Complex.I)
    with hFdef
  have hFcont : Continuous F := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      ((continuous_fst.inner continuous_const).add (continuous_snd.inner continuous_const))
  have hFb : ∀ z, ‖F z‖ ≤ 1 := fun z => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  -- Measurability of the action and of the statistic.
  have hsmul : ∀ ε : Fin n → ℤˣ, Measurable fun x : Fin n → E => ε • x := by
    intro ε
    refine measurable_pi_lambda _ fun i => ?_
    simp only [signChange_smul_apply_vec]
    exact (measurable_pi_apply i).const_smul _
  have hTmeas : Measurable T :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul u
  have hTg : ∀ ε : Fin n → ℤˣ, Measurable fun x : Fin n → E => T (ε • x) :=
    fun ε => hTmeas.comp (hsmul ε)
  -- Step 1: the characteristic function as an integral against `randPairLaw`.
  have hcontExp : Continuous fun y : WithLp 2 (E × E) =>
      Complex.exp (((⟪y, t⟫ : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((continuous_id (X := WithLp 2 (E × E))).inner continuous_const)).mul continuous_const)
  have hstep1 : charFun ((randPairLaw (Fin n → ℤˣ) T πQ).map (WithLp.toLp 2)) t
      = ∫ z, F z ∂(randPairLaw (Fin n → ℤˣ) T πQ) := by
    rw [charFun_apply, integral_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
      hcontExp.aestronglyMeasurable]
    rfl
  -- Step 2: unfold the group average.
  have hstep2 := integral_randPairLaw (G := Fin n → ℤˣ) πQ T hTg F hFcont.measurable hFb
  -- Step 3: the per-pattern integrand factorizes across coordinates.
  have hstep3 : ∀ (ε ε' : Fin n → ℤˣ) (x : Fin n → E),
      F (T (ε • x), T (ε' • x)) = ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
    intro ε ε' x
    exact exp_inner_pair_eq_prod n t ε ε' x
  -- Integrability bookkeeping.
  have hprodmeas : ∀ ε ε' : Fin n → ℤˣ,
      Measurable fun x : Fin n → E => ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
    intro ε ε'
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_signFactor n t (ε i) (ε' i)).comp (measurable_pi_apply i)
  have hprodb : ∀ (ε ε' : Fin n → ℤˣ) (x : Fin n → E),
      ‖∏ i, signFactor n t (ε i) (ε' i) (x i)‖ ≤ 1 := by
    intro ε ε' x
    rw [norm_prod]
    simp [norm_signFactor]
  have hprodint : ∀ ε ε' : Fin n → ℤˣ,
      Integrable (fun x : Fin n → E => ∏ i, signFactor n t (ε i) (ε' i) (x i)) πQ := by
    intro ε ε'
    exact Integrable.mono' (integrable_const (1 : ℝ)) (hprodmeas ε ε').aestronglyMeasurable
      (Filter.Eventually.of_forall (hprodb ε ε'))
  have hkint : ∀ s s' : ℤˣ, Integrable (signFactor n t s s') Q :=
    fun s s' => Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_signFactor n t s s').aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_of_eq (norm_signFactor n t s s' y))
  -- Step 4: swap the finite sums with the integral and use Fubini for the product measure.
  have hstep4 : (∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
        ∫ x, F (T (ε • x), T (ε' • x)) ∂πQ)
      = (∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signFactor n t s s' y ∂Q) ^ n := by
    have h1 : (∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ, ∫ x, F (T (ε • x), T (ε' • x)) ∂πQ)
        = ∫ x, ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
            ∏ i, signFactor n t (ε i) (ε' i) (x i) ∂πQ := by
      rw [integral_finset_sum _ (fun ε _ => integrable_finset_sum _ fun ε' _ => hprodint ε ε')]
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [integral_finset_sum _ (fun ε' _ => hprodint ε ε')]
      refine Finset.sum_congr rfl fun ε' _ => ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hstep3 ε ε' x)
    rw [h1]
    have h2 : (fun x : Fin n → E => ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
          ∏ i, signFactor n t (ε i) (ε' i) (x i))
        = fun x : Fin n → E => ∏ i, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' (x i)) := by
      funext x
      exact (prod_sum_signFactor n t x).symm
    have h3 := integral_fintype_prod_eq_pow (ι := Fin n)
      (f := fun y : E => ∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' y) (μ := Q)
    rw [h2, hπQ]
    refine h3.trans ?_
    rw [Fintype.card_fin]
    congr 1
    have hsw1 : ∫ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' y) ∂Q
        = ∑ s : ℤˣ, ∫ y : E, (∑ s' : ℤˣ, signFactor n t s s' y) ∂Q :=
      integral_finset_sum (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, signFactor n t s s' y)
        Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hkint s s')
    have hsw2 : ∀ s : ℤˣ, ∫ y : E, (∑ s' : ℤˣ, signFactor n t s s' y) ∂Q
        = ∑ s' : ℤˣ, ∫ y : E, signFactor n t s s' y ∂Q := fun s =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => signFactor n t s s' y)
        Finset.univ (fun s' _ => hkint s s')
    exact hsw1.trans (Finset.sum_congr rfl fun s _ => hsw2 s)
  -- Step 5: identify the coordinate integrals as one-dimensional characteristic functions.
  have hstep5 : ∀ s s' : ℤˣ,
      ∫ y, signFactor n t s s' y ∂Q = charFun (Q.map (signDir t s s')) u := by
    intro s s'
    have haes : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)) (Q.map (signDir t s s')) :=
      (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map (measurable_signDir t s s').aemeasurable haes]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    unfold signFactor
    rw [Complex.ofReal_mul]
  -- Assemble.
  rw [hstep1, hstep2, hstep4]
  simp_rw [hstep5]
  have hcard : ((Fintype.card (Fin n → ℤˣ) : ℂ) ^ 2)⁻¹ = ((4 : ℂ)⁻¹) ^ n := by
    rw [card_signPattern]
    push_cast
    rw [← pow_mul, mul_comm n 2, pow_mul, ← inv_pow]
    norm_num
  rw [hcard, ← mul_pow]

/-! ### The limit -/

/-- **Second-order Taylor expansion of a one-dimensional characteristic function**, without
the mean-zero / unit-variance normalization of Mathlib's `taylor_charFun_two`. The
sign-averaged expansion below needs the unnormalized form, because the four sign directions
have different (nonzero) means and second moments. -/
private lemma isLittleO_charFun_taylor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : AEMeasurable W P)
    (hint : MemLp id 2 (P.map W)) :
    (fun v : ℝ => charFun (P.map W) v
        - (1 + (P[W] : ℝ) * v * Complex.I - (P[W ^ 2] : ℝ) * v ^ 2 / 2))
      =o[𝓝 0] fun v : ℝ => v ^ 2 := by
  have h := taylor_isLittleO_univ (x₀ := (0 : ℝ)) (contDiff_charFun hint)
  simp only [sub_zero] at h
  refine h.congr' (Filter.Eventually.of_forall fun v => ?_) Filter.EventuallyEq.rfl
  simp only []
  rw [taylorWithinEval_charFun_two_zero hW hint v]

/-- Pairing with a fixed direction is square-integrable when the data is. -/
private lemma memLp_inner_right (Q : Measure E) (hQ2 : MemLp id 2 Q) (v : E) :
    MemLp (fun y : E => ⟪y, v⟫) 2 Q := by
  have hmeas : AEStronglyMeasurable (fun y : E => ⟪y, v⟫) Q :=
    ((continuous_id (X := E)).inner continuous_const).aestronglyMeasurable
  have hdom : MemLp (fun y : E => ‖v‖ * ‖y‖) 2 Q := by
    simpa using hQ2.norm.const_mul ‖v‖
  refine hdom.mono hmeas (Filter.Eventually.of_forall fun y => ?_)
  have hineq : |⟪y, v⟫| ≤ ‖y‖ * ‖v‖ := abs_real_inner_le_norm y v
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm ‖v‖ ‖y‖]
  exact hineq

private lemma memLp_signDir (Q : Measure E) (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E))
    (s s' : ℤˣ) : MemLp (signDir t s s') 2 Q := by
  unfold signDir
  exact ((memLp_inner_right Q hQ2 _).const_mul _).add ((memLp_inner_right Q hQ2 _).const_mul _)

private lemma memLp_id_map_signDir (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    MemLp id 2 (Q.map (signDir t s s')) := by
  rw [memLp_map_measure_iff aestronglyMeasurable_id (measurable_signDir t s s').aemeasurable]
  exact memLp_signDir Q hQ2 t s s'

/-- The four sign directions have vanishing total first moment. -/
private lemma sum_integral_signDir (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) :
    ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signDir t s s' y ∂Q = 0 := by
  classical
  have hint : ∀ s s' : ℤˣ, Integrable (signDir t s s') Q := fun s s' =>
    (memLp_signDir Q hQ2 t s s').integrable (by norm_num)
  have h1 : ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signDir t s s' y ∂Q
      = ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) ∂Q := by
    rw [integral_finset_sum (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, signDir t s s' y)
      Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hint s s')]
    exact (Finset.sum_congr rfl fun s _ =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => signDir t s s' y)
        Finset.univ (fun s' _ => hint s s')).symm
  rw [h1]
  have hzero : ∀ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) = 0 := by
    intro y
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
      Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    unfold signDir
    push_cast
    ring
  have hz : ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) ∂Q = ∫ _y : E, (0 : ℝ) ∂Q :=
    integral_congr_ae (Filter.Eventually.of_forall hzero)
  rw [hz, integral_zero]

/-- The four sign directions have total second moment `4(A+B)`. -/
private lemma sum_integral_signDir_sq (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) :
    ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, (signDir t s s' y) ^ 2 ∂Q
      = 4 * ((∫ y, ⟪y, (WithLp.ofLp t).1⟫ ^ 2 ∂Q) + ∫ y, ⟪y, (WithLp.ofLp t).2⟫ ^ 2 ∂Q) := by
  classical
  have hint : ∀ s s' : ℤˣ, Integrable (fun y => (signDir t s s' y) ^ 2) Q := fun s s' => by
    have := (memLp_signDir Q hQ2 t s s').integrable_sq
    simpa using this
  have hint1 : Integrable (fun y : E => ⟪y, (WithLp.ofLp t).1⟫ ^ 2) Q := by
    simpa using (memLp_inner_right Q hQ2 (WithLp.ofLp t).1).integrable_sq
  have hint2 : Integrable (fun y : E => ⟪y, (WithLp.ofLp t).2⟫ ^ 2) Q := by
    simpa using (memLp_inner_right Q hQ2 (WithLp.ofLp t).2).integrable_sq
  have h1 : ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, (signDir t s s' y) ^ 2 ∂Q
      = ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, (signDir t s s' y) ^ 2) ∂Q := by
    rw [integral_finset_sum
      (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, (signDir t s s' y) ^ 2)
      Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hint s s')]
    exact (Finset.sum_congr rfl fun s _ =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => (signDir t s s' y) ^ 2)
        Finset.univ (fun s' _ => hint s s')).symm
  rw [h1]
  have hpt : ∀ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, (signDir t s s' y) ^ 2)
      = 4 * (⟪y, (WithLp.ofLp t).1⟫ ^ 2 + ⟪y, (WithLp.ofLp t).2⟫ ^ 2) := by
    intro y
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
      Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    unfold signDir
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_add hint1 hint2]

/-! ### The bivariate sign-change central limit theorem -/

/-- **The bivariate sign-change randomization central limit theorem.** For i.i.d. data `Q`
with finite second moments in a finite-dimensional real inner-product space, the normalized
sums recomputed at **two independent uniform sign patterns** converge jointly in law to a
*product* `ν ⊗ ν`, where `ν` is the centred Gaussian whose characteristic function is
`exp(−∫⟪y,v⟫²dQ / 2)`.

No mean-zero assumption is needed: averaging over the sign group symmetrizes each summand,
so the first-order term of the expansion cancels identically and only the second moment
survives. The asymptotic independence of the two components is exact at every finite `n` —
it is the factorization of the four-term sign average, not a limiting phenomenon. -/
theorem weakConverges_randPairLaw_signSum [FiniteDimensional ℝ E]
    (Q : Measure E) [IsProbabilityMeasure Q]
    -- USER-INPUT: finite second moments of the observation
    (hQ2 : MemLp id 2 Q) (ν : Measure E) [IsProbabilityMeasure ν]
    -- USER-INPUT: `ν` is the centred Gaussian with the second-moment form of `Q`
    (hν : ∀ v : E, charFun ν v = Complex.exp (-((∫ y, ⟪y, v⟫ ^ 2 ∂Q : ℝ) : ℂ) / 2)) :
    WeakConverges (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => Q)) (ν.prod ν) := by
  classical
  -- Measurability of the action and of the statistic, so that `randPairLaw` is a probability.
  have hsmul : ∀ (n : ℕ) (ε : Fin n → ℤˣ), Measurable fun x : Fin n → E => ε • x := by
    intro n ε
    refine measurable_pi_lambda _ fun i => ?_
    simp only [signChange_smul_apply_vec]
    exact (measurable_pi_apply i).const_smul _
  have hTmeas : ∀ n : ℕ,
      Measurable fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i := fun n =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul _
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (randPairLaw (Fin n → ℤˣ)
      (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
      (Measure.pi fun _ : Fin n => Q)) := fun n =>
    isProbabilityMeasure_randPairLaw _ _ _ (hTmeas n) (hsmul n)
  refine weakConverges_prod_of_tendsto_charFun (fun t => ?_)
  simp_rw [charFun_randPairLaw_signSum Q]
  -- Notation for the two second moments and the four sign directions.
  set A : ℝ := ∫ y, ⟪y, (WithLp.ofLp t).1⟫ ^ 2 ∂Q with hA
  set B : ℝ := ∫ y, ⟪y, (WithLp.ofLp t).2⟫ ^ 2 ∂Q with hB
  set RR : ℤˣ → ℤˣ → ℝ → ℂ := fun s s' v => charFun (Q.map (signDir t s s')) v
    - (1 + (Q[signDir t s s'] : ℝ) * v * Complex.I
      - (Q[(signDir t s s') ^ 2] : ℝ) * v ^ 2 / 2) with hRR
  -- Identify the limit.
  have hlim : charFun ν (WithLp.ofLp t).1 * charFun ν (WithLp.ofLp t).2
      = Complex.exp (-(((A + B : ℝ)) : ℂ) / 2) := by
    rw [hν, hν, ← Complex.exp_add, ← hA, ← hB]
    push_cast
    ring_nf
  rw [hlim]
  refine Complex.tendsto_pow_exp_of_isLittleO_sub_add_div _ ?_
  -- Each of the four directions has a second-order expansion; compose with `n^{-1/2} → 0`.
  have hu0 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hRo : ∀ s s' : ℤˣ, (fun n : ℕ => RR s s' ((Real.sqrt (n : ℝ))⁻¹)) =o[atTop]
      fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 := by
    intro s s'
    exact (isLittleO_charFun_taylor (measurable_signDir t s s').aemeasurable
      (memLp_id_map_signDir Q hQ2 t s s')).comp_tendsto hu0
  have hsum : (fun n : ℕ => (4 : ℂ)⁻¹ * (RR 1 1 ((Real.sqrt (n : ℝ))⁻¹)
        + RR 1 (-1) ((Real.sqrt (n : ℝ))⁻¹)
        + (RR (-1) 1 ((Real.sqrt (n : ℝ))⁻¹) + RR (-1) (-1) ((Real.sqrt (n : ℝ))⁻¹))))
      =o[atTop] fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 :=
    (((hRo 1 1).add (hRo 1 (-1))).add ((hRo (-1) 1).add (hRo (-1) (-1)))).const_mul_left _
  -- The moment identities, written out over the four sign pairs.
  have hv2 : ∀ n : ℕ, ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
    intro n
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hMeq : ∀ s s' : ℤˣ, Q[(signDir t s s') ^ 2] = ∫ y, (signDir t s s' y) ^ 2 ∂Q :=
    fun s s' => rfl
  have hm4 : Q[signDir t 1 1] + Q[signDir t 1 (-1)]
      + (Q[signDir t (-1) 1] + Q[signDir t (-1) (-1)]) = 0 := by
    rw [← sum_units_int (fun s s' => ∫ y, signDir t s s' y ∂Q)]
    exact sum_integral_signDir Q hQ2 t
  have hM4 : Q[(signDir t 1 1) ^ 2] + Q[(signDir t 1 (-1)) ^ 2]
      + (Q[(signDir t (-1) 1) ^ 2] + Q[(signDir t (-1) (-1)) ^ 2]) = 4 * (A + B) := by
    simp_rw [hMeq]
    rw [← sum_units_int (fun s s' => ∫ y, (signDir t s s' y) ^ 2 ∂Q)]
    exact sum_integral_signDir_sq Q hQ2 t
  -- The algebraic identity: the four remainders reassemble the required difference.
  have key : ∀ n : ℕ,
      (4 : ℂ)⁻¹ * (∑ s : ℤˣ, ∑ s' : ℤˣ, charFun (Q.map (signDir t s s')) ((Real.sqrt (n : ℝ))⁻¹))
          - (1 + -(((A + B : ℝ)) : ℂ) / 2 / (n : ℂ))
        = (4 : ℂ)⁻¹ * (RR 1 1 ((Real.sqrt (n : ℝ))⁻¹) + RR 1 (-1) ((Real.sqrt (n : ℝ))⁻¹)
          + (RR (-1) 1 ((Real.sqrt (n : ℝ))⁻¹) + RR (-1) (-1) ((Real.sqrt (n : ℝ))⁻¹))) := by
    intro n
    have hvsq : (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 = 1 / (n : ℂ) := by
      rw [← Complex.ofReal_pow, hv2 n]
      push_cast
      rw [one_div]
    have hm4' : ((Q[signDir t 1 1] : ℝ) : ℂ) + ((Q[signDir t 1 (-1)] : ℝ) : ℂ)
        + (((Q[signDir t (-1) 1] : ℝ) : ℂ) + ((Q[signDir t (-1) (-1)] : ℝ) : ℂ)) = 0 := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add, hm4]
      simp
    have hM4' : ((Q[(signDir t 1 1) ^ 2] : ℝ) : ℂ) + ((Q[(signDir t 1 (-1)) ^ 2] : ℝ) : ℂ)
        + (((Q[(signDir t (-1) 1) ^ 2] : ℝ) : ℂ)
          + ((Q[(signDir t (-1) (-1)) ^ 2] : ℝ) : ℂ)) = 4 * (((A + B : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add, hM4]
      push_cast
      ring
    rw [sum_units_int (fun s s' => charFun (Q.map (signDir t s s')) ((Real.sqrt (n : ℝ))⁻¹))]
    simp only [hRR]
    rw [hvsq]
    linear_combination ((4 : ℂ)⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ : ℝ) * Complex.I) * hm4'
      - ((4 : ℂ)⁻¹ * (1 / (n : ℂ)) / 2) * hM4'
  -- Transfer the little-o statement along the identity and the comparison function.
  rw [← Asymptotics.isLittleO_norm_right]
  have hnorm : (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ)‖) = fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 := by
    funext n
    rw [hv2 n, norm_div, Complex.norm_natCast, norm_one, one_div]
  rw [hnorm]
  exact hsum.congr' (Filter.Eventually.of_forall fun n => (key n).symm) Filter.EventuallyEq.rfl

end SignSum

end StatLean.HypothesisTesting
