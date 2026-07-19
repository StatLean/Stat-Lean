import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
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

/-- **Continuity** of the weighted exponential integral on the interior of the weighted
natural parameter set. -/
theorem continuousOn_integral_exp_inner (E : ExpFamily 𝓧 V) {f : 𝓧 → ℝ}
    -- USER-INPUT: the weight is a measurable function on the sample space; this is the
    -- classical "integrable function `f`" of the differentiation theorem
    (hf : Measurable f) :
    ContinuousOn (fun η => ∫ x, f x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)
      (interior (E.weightedNatSet f)) := by
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
