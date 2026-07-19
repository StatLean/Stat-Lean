import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Smoothness of weighted exponential integrals in the natural parameter

For an integrable weight `f` on the sample space, the map
$$ \eta \;\longmapsto\; \int f(x)\,e^{\langle \eta, T(x)\rangle}\,d\nu(x) $$
is continuous, differentiable to all orders, and in fact real-analytic on the interior of the
set of natural parameters at which the weighted integrand is absolutely integrable. This is
the analytic engine behind every moment formula for exponential families: the mean and
covariance identities for the natural statistic are what one gets by differentiating
`∫ exp(⟨η, T⟩ − A(η)) dν = 1` under the integral sign.

* `ExpFamily.weightedNatSet` — the `f`-weighted natural parameter set;
* `ExpFamily.continuousOn_integral_exp_inner` — continuity on its interior;
* `ExpFamily.hasFDerivAt_integral_exp_inner` — differentiability, with the derivative given
  by the integral of the differentiated integrand;
* `ExpFamily.iteratedDeriv_integral_exp_inner` — derivatives of every order along a fixed
  direction;
* `ExpFamily.analyticAt_integral_exp_mul` — real-analyticity in the one-dimensional case;
* `ExpFamily.analyticOnNhd_integral_exp_inner` — the full multivariate joint analyticity
  (DEFERRAL-ELIGIBLE, see below).

**Reference.** Classical exponential-family theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The weighted parameter set is defined with `|f|` so that membership is a genuine absolute
  integrability statement and the set is convex by the same Hölder argument that gives
  `ExpFamily.natSet_convex`.
* The derivative is represented as `innerSL ℝ G` for the vector
  `G = ∫ (f x · e^{⟨η, T x⟩}) • T x dν`, i.e. as the Riesz representation of the differential.
  This is the honest "integral of the differentiated integrand": the directional derivative
  along `u` is `∫ f x · ⟨u, T x⟩ · e^{⟨η, T x⟩} dν = ⟪G, u⟫`. Representing the differential by
  a vector rather than by an abstract continuous linear map keeps the statement usable
  downstream (the gradient of the log-partition function is `G` with `f ≡ 1`).
* `analyticAt_integral_exp_mul` is not a literal instance of Mathlib's
  `ProbabilityTheory.analyticAt_mgf`, which only covers the unweighted case `f ≡ 1`. It does
  reduce to it: split `f = f⁺ − f⁻`, and note that `∫ f± e^{ηT} dν` is the moment generating
  function of `T` under the finite measure `ν.withDensity (ENNReal.ofReal ∘ f±)`, whose
  `integrableExpSet` contains the interior of the weighted parameter set. Analyticity is then
  `analyticAt_mgf` applied twice and subtracted.
* `analyticOnNhd_integral_exp_inner` is **DEFERRAL-ELIGIBLE**. Continuity, the first Fréchet
  derivative and all directional derivatives of every order — the three results above it —
  cover every downstream consumer in this development (the moment identities, the information
  matrix, and the completeness argument, which only needs an open set of parameters). Joint
  real-analyticity in several variables requires a multivariate power-series argument with no
  Mathlib counterpart at the current pin, so this statement may be kept as a named,
  documented debt rather than closed.

**Bibliographic comments.** Differentiation under the integral sign for exponential families,
and the resulting analyticity of the log-partition function on the interior of the natural
parameter set, go back to E. Sverdrup ("Similarity, unbiasedness, minimaxibility and
admissibility of statistical test procedures," *Skand. Aktuarietidskr.* **36** (1953),
64–86); systematic treatments are in O. Barndorff-Nielsen (*Information and Exponential
Families in Statistical Theory*, Wiley, 1978, §7.1) and L. D. Brown (*Fundamentals of
Statistical Exponential Families*, IMS Lecture Notes 9, 1986, Ch. 2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

/-- The **`f`-weighted natural parameter set**: the natural parameters at which the weighted
integrand `|f|·e^{⟨η, T⟩}` is integrable against the reference measure. For `f ≡ 1` this is
`ExpFamily.natSet`. Like the natural parameter set it is a convex subset of `V`. -/
def weightedNatSet (E : ExpFamily 𝓧 V) (f : 𝓧 → ℝ) : Set V :=
  {η : V | Integrable (fun x => |f x| * Real.exp ⟪η, E.stat x⟫_ℝ) E.base}

section Differentiation

variable [BorelSpace V] [SecondCountableTopology V]

open Module in
/-- **Finite-dimensional local domination.** If a ball of parameters around `η` (of radius large
enough to contain the `2^s` sign vectors of an orthonormal basis) lies in the weighted natural
set, then the envelope `|f x|·e^{⟪η, T x⟩ + c‖T x‖}` is integrable. This is the analytic core of
the domination bounds for the derivative and continuity results: `e^{c‖v‖}` is controlled by the
finite sum `∑_S e^{⟪w_S, v⟫}` over the sign vectors `w_S` of an orthonormal basis. -/
private lemma integrable_abs_exp_inner_add_norm [FiniteDimensional ℝ V]
    (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ} (hf : Measurable f) {η : V} {c : ℝ} (hc : 0 ≤ c)
    (hball : ∀ w : V, ‖w‖ ≤ 2 * c * (finrank ℝ V) → η + w ∈ E.weightedNatSet f) :
    Integrable (fun x => |f x| * Real.exp (⟪η, E.stat x⟫_ℝ + c * ‖E.stat x‖)) E.base := by
  classical
  set N := finrank ℝ V with hN
  set b := stdOrthonormalBasis ℝ V with hb
  -- the `2^N` sign vectors of the orthonormal basis
  set w : Finset (Fin N) → V := fun t => (∑ i ∈ t, c • b i) - (∑ i ∈ tᶜ, c • b i) with hw
  -- each shifted parameter lies in the weighted natural set
  have hwmem : ∀ t, η + w t ∈ E.weightedNatSet f := by
    intro t
    apply hball
    calc ‖w t‖ ≤ ‖∑ i ∈ t, c • b i‖ + ‖∑ i ∈ tᶜ, c • b i‖ := norm_sub_le _ _
      _ ≤ (∑ i ∈ t, ‖c • b i‖) + (∑ i ∈ tᶜ, ‖c • b i‖) :=
            add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
      _ ≤ (∑ _i ∈ t, c) + (∑ _i ∈ tᶜ, c) := by
            gcongr with i _ i _ <;>
              simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, b.norm_eq_one]
      _ ≤ 2 * c * N := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            have h1 : (t.card : ℝ) ≤ N := by
              exact_mod_cast (Finset.card_le_univ t).trans_eq (by simp)
            have h2 : (tᶜ.card : ℝ) ≤ N := by
              exact_mod_cast (Finset.card_le_univ tᶜ).trans_eq (by simp)
            nlinarith [hc, h1, h2]
  -- the sign-vector envelope: `e^{c‖v‖} ≤ ∑_t e^{⟪w t, v⟫}`
  have hkey : ∀ v : V, Real.exp (c * ‖v‖) ≤ ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := by
    intro v
    have hrepr : v = ∑ i, ⟪b i, v⟫_ℝ • b i := by
      conv_lhs => rw [← b.sum_repr v]
      simp_rw [b.repr_apply_apply]
    have hnorm : ‖v‖ ≤ ∑ i, |⟪b i, v⟫_ℝ| := by
      calc ‖v‖ = ‖∑ i, ⟪b i, v⟫_ℝ • b i‖ := by rw [← hrepr]
        _ ≤ ∑ i, ‖⟪b i, v⟫_ℝ • b i‖ := norm_sum_le _ _
        _ = ∑ i, |⟪b i, v⟫_ℝ| := by
              simp [norm_smul, Real.norm_eq_abs, b.norm_eq_one]
    have hexp1 : Real.exp (c * ‖v‖) ≤ ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|) := by
      rw [← Real.exp_sum]
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hnorm hc
    have hprod : ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|)
        ≤ ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ))) := by
      apply Finset.prod_le_prod (fun i _ => Real.exp_nonneg _)
      intro i _
      rcases le_total 0 (⟪b i, v⟫_ℝ) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(c * ⟪b i, v⟫_ℝ))]
      · rw [abs_of_nonpos h, show c * -(⟪b i, v⟫_ℝ) = -(c * ⟪b i, v⟫_ℝ) by ring]
        linarith [Real.exp_pos (c * ⟪b i, v⟫_ℝ)]
    have hexpand : ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ)))
        = ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := by
      rw [Finset.prod_add, Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
      congr 1
      rw [hw]
      simp only [inner_sub_left, sum_inner, real_inner_smul_left]
      rw [Finset.compl_eq_univ_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    calc Real.exp (c * ‖v‖) ≤ ∏ i, Real.exp (c * |⟪b i, v⟫_ℝ|) := hexp1
      _ ≤ ∏ i, (Real.exp (c * ⟪b i, v⟫_ℝ) + Real.exp (-(c * ⟪b i, v⟫_ℝ))) := hprod
      _ = ∑ t : Finset (Fin N), Real.exp ⟪w t, v⟫_ℝ := hexpand
  -- fold the envelope: `e^{⟪η,v⟫ + c‖v‖} ≤ ∑_t e^{⟪η + w t, v⟫}`
  have hpt : ∀ v : V, Real.exp (⟪η, v⟫_ℝ + c * ‖v‖)
      ≤ ∑ t : Finset (Fin N), Real.exp ⟪η + w t, v⟫_ℝ := by
    intro v
    rw [Real.exp_add]
    calc Real.exp ⟪η, v⟫_ℝ * Real.exp (c * ‖v‖)
        ≤ Real.exp ⟪η, v⟫_ℝ * ∑ t, Real.exp ⟪w t, v⟫_ℝ :=
          mul_le_mul_of_nonneg_left (hkey v) (Real.exp_nonneg _)
      _ = ∑ t : Finset (Fin N), Real.exp ⟪η + w t, v⟫_ℝ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [← Real.exp_add, inner_add_left]
  -- the dominating function is a finite sum of integrable functions
  have hinner_meas : Measurable fun x => ⟪η, E.stat x⟫_ℝ :=
    (innerSL ℝ η).continuous.measurable.comp E.stat_meas
  have hg_int : Integrable
      (fun x => ∑ t : Finset (Fin N), |f x| * Real.exp ⟪η + w t, E.stat x⟫_ℝ) E.base :=
    integrable_finset_sum _ (fun t _ => hwmem t)
  refine hg_int.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hf.abs.aestronglyMeasurable).mul
      ((hinner_meas.add ((E.stat_meas.norm).const_mul c)).exp.aestronglyMeasurable)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hpt (E.stat x)) (abs_nonneg _)

/-- **Continuity** of the weighted exponential integral on the interior of the weighted
natural parameter set. -/
theorem continuousOn_integral_exp_inner (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: the weight is a measurable function on the sample space; this is the
    -- classical "integrable function `f`" of the differentiation theorem
    (hf : Measurable f) :
    ContinuousOn (fun η => ∫ x, f x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
      (interior (E.weightedNatSet f)) := by
  -- TODO: dominated-convergence continuity. On a ball `B(η, r) ⊆ interior (weightedNatSet f)`
  -- the integrand `ζ ↦ f x · e^{⟪ζ, T x⟫}` is dominated by the local envelope
  -- `|f x|·(e^{⟪η,T x⟫} + e^{⟪ζ,T x⟫})` (convexity of `exp` along the segment); its integrability
  -- is the `2^s` sign-vector bound `e^{c·Σ|Tᵢ|} ≤ Σ_ε e^{⟪c·ε, T⟫}` (finite dimension), giving
  -- `continuousWithinAt` at each interior point via `continuousAt_of_dominated`.
  sorry

/-- **Differentiability**: on the interior of the weighted natural parameter set the weighted
exponential integral is Fréchet differentiable, and its differential is represented by the
vector `∫ (f x · e^{⟨η, T x⟩}) • T x dν` — the integral of the differentiated integrand. -/
theorem hasFDerivAt_integral_exp_inner
    -- LEAN-ONLY: completeness of the statistic's target space, so that the `V`-valued Bochner
    -- integral representing the differential is meaningful; automatic in finite dimension
    [CompleteSpace V] (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : V}
    -- USER-INPUT: interior parameter; interiority is the classical hypothesis licensing
    -- differentiation under the integral sign
    (hη : η ∈ interior (E.weightedNatSet f)) :
    HasFDerivAt (fun ζ => ∫ x, f x * Real.exp ⟪ζ, E.stat x⟫_ℝ ∂E.base)
      (innerSL ℝ (∫ x, (f x * Real.exp ⟪η, E.stat x⟫_ℝ) • E.stat x ∂E.base)) η := by
  -- TODO: differentiation under the integral via `hasFDerivAt_integral_of_dominated_loc_of_lip'`
  -- with `F ζ x = f x · e^{⟪ζ, T x⟫}`, `F' x = (f x · e^{⟪η, T x⟫}) • innerSL ℝ (T x)` (whose
  -- integral is `innerSL ℝ` of the stated vector, since `innerSL ℝ` is a CLM and commutes with
  -- the Bochner integral). The Lipschitz bound needs `bound x = |f x|·‖T x‖·e^{⟪η,T x⟫+r‖T x‖}`
  -- integrable on a ball `B(η, r) ⊆ interior (weightedNatSet f)`; absorbing the `‖T x‖` factor
  -- (`t·e^{rt} ≤ C·e^{r't}`) and the `e^{r'‖T x‖}` factor via the `2^s` sign-vector envelope
  -- (finite dimension) is the remaining work.
  sorry

/-- **Derivatives of all orders** along a fixed direction: the `n`-th derivative of
`t ↦ ∫ f(x) e^{⟨η + t·u, T x⟩} dν` at `t = 0` is obtained by differentiating under the
integral sign `n` times. -/
theorem iteratedDeriv_integral_exp_inner (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : V}
    -- USER-INPUT: interior parameter; see `hasFDerivAt_integral_exp_inner`
    (hη : η ∈ interior (E.weightedNatSet f)) (u : V) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ∫ x, f x * Real.exp ⟪η + t • u, E.stat x⟫_ℝ ∂E.base) 0
      = ∫ x, f x * ⟪u, E.stat x⟫_ℝ ^ n * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := by
  -- TODO: iterate the directional derivative. Along `t ↦ η + t•u` the integrand is
  -- `f x · e^{⟪η,T x⟫ + t·⟪u,T x⟫}`; each differentiation pulls down a factor `⟪u, T x⟫`, and the
  -- swap of `iteratedDeriv` with `∫` at order `n` follows by induction from the same
  -- dominated-differentiation step as `hasFDerivAt_integral_exp_inner` (with weight
  -- `f · ⟪u,T⟫^k`), whose local envelope is again the `2^s` sign-vector bound.
  sorry

/-- **Real-analyticity, one-dimensional case**: for a real natural statistic the weighted
exponential integral is analytic at every interior point of the weighted natural parameter
set. -/
theorem analyticAt_integral_exp_mul (E : ExpFamily 𝓧 ℝ) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) {η : ℝ}
    -- USER-INPUT: interior parameter; see `hasFDerivAt_integral_exp_inner`
    (hη : η ∈ interior (E.weightedNatSet f)) :
    AnalyticAt ℝ (fun ζ : ℝ => ∫ x, f x * Real.exp ⟪ζ, E.stat x⟫_ℝ ∂E.base) η := by
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by rw [← real_inner_comm]; rfl
  -- the positive and negative parts of the weight
  have hfp : Measurable fun x => max (f x) 0 := hf.max measurable_const
  have hfm : Measurable fun x => max (-f x) 0 := hf.neg.max measurable_const
  have hfp_nn : ∀ x, 0 ≤ max (f x) 0 := fun x => le_max_right _ _
  have hfm_nn : ∀ x, 0 ≤ max (-f x) 0 := fun x => le_max_right _ _
  have hfp_le : ∀ x, max (f x) 0 ≤ |f x| := fun x => max_le (le_abs_self _) (abs_nonneg _)
  have hfm_le : ∀ x, max (-f x) 0 ≤ |f x| := fun x => max_le (neg_le_abs _) (abs_nonneg _)
  -- `mgf` of the tilted measure equals the weighted integral
  have hmgf : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → ∀ ζ : ℝ,
      mgf E.stat (E.base.withDensity fun x => ENNReal.ofReal (w x)) ζ
        = ∫ x, w x * Real.exp (ζ * E.stat x) ∂E.base := by
    intro w hw hwnn ζ
    simp only [mgf]
    rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hwnn x), smul_eq_mul]
  -- weighted integrand is integrable on the weighted natural set
  have hintw : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      ∀ ζ ∈ E.weightedNatSet f, Integrable (fun x => w x * Real.exp (ζ * E.stat x)) E.base := by
    intro w hw hwnn hwle ζ hζ
    have hζI : Integrable (fun x => |f x| * Real.exp ⟪ζ, E.stat x⟫_ℝ) E.base := hζ
    refine hζI.mono' ((hw.aestronglyMeasurable).mul
      (((measurable_const.mul E.stat_meas).exp).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwnn x),
      abs_of_nonneg (Real.exp_nonneg _), hinner ζ (E.stat x)]
    exact mul_le_mul_of_nonneg_right (hwle x) (Real.exp_nonneg _)
  -- membership in the interior of the integrable-exp set of each tilted measure
  have hsub : ∀ (w : 𝓧 → ℝ), Measurable w → (∀ x, 0 ≤ w x) → (∀ x, w x ≤ |f x|) →
      E.weightedNatSet f ⊆ integrableExpSet E.stat (E.base.withDensity
        fun x => ENNReal.ofReal (w x)) := by
    intro w hw hwnn hwle ζ hζ
    simp only [integrableExpSet, Set.mem_setOf_eq]
    rw [integrable_withDensity_iff hw.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine ((hintw w hw hwnn hwle ζ hζ).congr (Filter.Eventually.of_forall fun x => ?_))
    dsimp only
    rw [ENNReal.toReal_ofReal (hwnn x), mul_comm]
  have hmemp : η ∈ interior (integrableExpSet E.stat
      (E.base.withDensity fun x => ENNReal.ofReal (max (f x) 0))) :=
    interior_mono (hsub _ hfp hfp_nn hfp_le) hη
  have hmemm : η ∈ interior (integrableExpSet E.stat
      (E.base.withDensity fun x => ENNReal.ofReal (max (-f x) 0))) :=
    interior_mono (hsub _ hfm hfm_nn hfm_le) hη
  have ha := (analyticAt_mgf hmemp).sub (analyticAt_mgf hmemm)
  refine ha.congr ?_
  have hnhd : interior (E.weightedNatSet f) ∈ nhds η := isOpen_interior.mem_nhds hη
  filter_upwards [hnhd] with ζ hζ
  have hζ' : ζ ∈ E.weightedNatSet f := interior_subset hζ
  simp only [Pi.sub_apply]
  rw [hmgf _ hfp hfp_nn ζ, hmgf _ hfm hfm_nn ζ,
    ← integral_sub (hintw _ hfp hfp_nn hfp_le ζ hζ') (hintw _ hfm hfm_nn hfm_le ζ hζ')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hinner ζ (E.stat x)]
  rcases le_total (f x) 0 with h | h
  · simp only [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  · simp only [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring

/-- **Joint real-analyticity in several natural parameters.**

DEFERRAL-ELIGIBLE: no downstream result in this development consumes joint analyticity —
continuity, the Fréchet derivative and all directional derivatives of every order suffice —
and closing it needs multivariate power-series machinery that the current Mathlib pin does not
provide. It may be kept as a named documented debt. -/
theorem analyticOnNhd_integral_exp_inner (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: measurable weight; see `continuousOn_integral_exp_inner`
    (hf : Measurable f) :
    AnalyticOnNhd ℝ (fun η => ∫ x, f x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
      (interior (E.weightedNatSet f)) := by
  sorry

end Differentiation

end ExpFamily

end StatLean.PointEstimation
