import StatLean.PointEstimation.UMVU.RaoBlackwell
import StatLean.PointEstimation.UMVU.Basic
import StatLean.PointEstimation.UMVU.CovarianceCriterion
import StatLean.PointEstimation.Sufficiency.Basic
import StatLean.PointEstimation.Completeness.Defs
import StatLean.PointEstimation.Completeness.ExpFamily
import StatLean.PointEstimation.ExponentialFamily.Defs

/-!
# The Lehmann–Scheffé theorem

Rao–Blackwellization improves any estimator by averaging it over the fibers of a sufficient
statistic, but leaves open which function of the statistic to use. Completeness settles this:
a complete sufficient statistic admits *at most one* unbiased function, so all
Rao–Blackwellized estimators of the same estimand coincide, and the common value is
simultaneously optimal — not only for squared error, but for every convex loss.

* `unique_unbiased_function_of_complete` — at most one unbiased function of a complete
  statistic;
* `isUMVU_of_complete_sufficient` — the Rao–Blackwellization of any unbiased square-integrable
  estimator along a complete sufficient statistic is UMVU;
* `risk_le_of_complete_sufficient` — the same estimator minimizes the risk among all unbiased
  estimators, for every nonnegative convex loss;
* `isUMVU_of_fullRank_expFamily` — the specialization to a full-rank exponential family, whose
  natural statistic is complete and sufficient.

**Reference.** Classical Lehmann–Scheffé theory: uniqueness of unbiased functions of a
complete statistic, optimality of the resulting estimator for convex losses, and the
exponential-family specialization.

**Proof formalization notes.**
* `unique_unbiased_function_of_complete` uses **only completeness**, not sufficiency: the
  difference of two unbiased functions of `T` integrates to zero under every law of `T`, and
  completeness concludes. The classical statement bundles sufficiency because it is stated for
  a complete sufficient statistic and because sufficiency is what makes unbiased functions of
  `T` *exist*; dropping it here strengthens the lemma and is recorded as a deliberate
  deviation.
* Optimality is proved by transport, not by a fresh variational argument: given a competitor
  `δ'`, its Rao–Blackwellization is an unbiased function of `T`, hence almost everywhere equal
  to the given one by the uniqueness lemma, and the Rao–Blackwell inequality applied to `δ'`
  finishes. The two theorems therefore have the same shape, with variance replaced by the
  `ℝ≥0∞`-valued convex risk.
* The risk statement fixes one unbiased integrable `δ` to build the estimator and quantifies
  over competitors `δ'` separately, rather than asserting a minimum over an unnamed class:
  this keeps the statement first-order and makes clear that the *same* estimator dominates
  every competitor.
* Integrability of the Rao–Blackwellized estimator under the laws of the statistic is derived
  from the corresponding property of `δ` through the reconstruction identity, not assumed
  (see the notes in `UMVU.RaoBlackwell`).
* `isUMVU_of_fullRank_expFamily` is stated only; its proof combines the completeness of the
  natural statistic of a full-rank exponential family with the two theorems above. It is
  phrased as the *existence* of a measurable function of the natural statistic which is UMVU,
  since the function itself is only determined almost everywhere. The full-rank condition is
  imposed on a parameter set that the family is required to cover.

**Bibliographic comments.** The theorem is due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340;
**15** (1955), 219–236), building on the conditioning theorem of C. R. Rao ("Information and
the accuracy attainable in the estimation of statistical parameters," *Bull. Calcutta Math.
Soc.* **37** (1945), 81–91) and D. Blackwell ("Conditional expectation and unbiased sequential
estimation," *Ann. Math. Statist.* **18** (1947), 105–110). That the existence of a complete
sufficient statistic is, under mild conditions, also *necessary* for every estimable function
to admit a uniformly minimum variance unbiased estimator is due to R. R. Bahadur ("On unbiased
estimates of uniformly minimum variance," *Sankhyā* **18** (1957), 211–224). The completeness
of the natural statistic of a full-rank exponential family is established in Lehmann and
Scheffé (1955, ibid.).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- Integrability of the Rao–Blackwellized estimator on the scale of the statistic, derived
from integrability under the members through the reconstruction identity. -/
private lemma integrable_rbEstimator_statLaw (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδi : ∀ θ, Integrable δ (P θ)) (θ : Θ) :
    Integrable (rbEstimator Q δ) (statLaw P T θ) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := isProbabilityMeasure_statLaw P hT θ
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  have hnormInt : Integrable (fun t => ∫ x, ‖δ x‖ ∂ Q t) (statLaw P T θ) :=
    ((Measure.integrable_compProd_iff hδsndInt.aestronglyMeasurable).mp hδsndInt).2
  refine Integrable.mono' hnormInt hrb.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  exact norm_integral_le_integral_norm _

/-- Square-integrability of the Rao–Blackwellized estimator on the scale of the statistic,
via the fiberwise `L²` Jensen bound `(∫ δ dQ_t)² ≤ ∫ δ² dQ_t`. -/
private lemma memLp_two_rbEstimator_statLaw (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S} (hT : Measurable T) {Q : Kernel S 𝓧}
    [IsMarkovKernel Q] (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδ2 : MemEstL2 P δ) (θ : Θ) :
    MemLp (rbEstimator Q δ) 2 (statLaw P T θ) := by
  haveI : IsProbabilityMeasure (statLaw P T θ) := isProbabilityMeasure_statLaw P hT θ
  have hgm : Measurable (fun x : 𝓧 => (T x, x)) := hT.prodMk measurable_id
  have hδsnd : Measurable (fun z : S × 𝓧 => δ z.2) := hδm.comp measurable_snd
  have hsqm : Measurable (fun z : S × 𝓧 => (δ z.2) ^ 2) := hδsnd.pow_const 2
  have hrb : StronglyMeasurable (rbEstimator Q δ) :=
    hδm.stronglyMeasurable.integral_kernel (κ := Q)
  have hδi : ∀ θ', Integrable δ (P θ') := fun θ' => (hδ2 θ').integrable one_le_two
  have hδsndInt : Integrable (fun z : S × 𝓧 => δ z.2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hδsnd.aestronglyMeasurable hgm.aemeasurable]
    exact hδi θ
  have hsqInt : Integrable (fun z : S × 𝓧 => (δ z.2) ^ 2) (statLaw P T θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hsqm.aestronglyMeasurable hgm.aemeasurable]
    exact (hδ2 θ).integrable_sq
  have haeδ : ∀ᵐ t ∂ statLaw P T θ, Integrable δ (Q t) :=
    ((Measure.integrable_compProd_iff hδsndInt.aestronglyMeasurable).mp hδsndInt).1
  have haesq : ∀ᵐ t ∂ statLaw P T θ, Integrable (fun x => (δ x) ^ 2) (Q t) :=
    ((Measure.integrable_compProd_iff hsqInt.aestronglyMeasurable).mp hsqInt).1
  have hinnerInt : Integrable (fun t => ∫ x, (δ x) ^ 2 ∂ Q t) (statLaw P T θ) := by
    have h2 := ((Measure.integrable_compProd_iff hsqInt.aestronglyMeasurable).mp hsqInt).2
    refine h2.congr (Filter.Eventually.of_forall fun t =>
      integral_congr_ae (Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg _)))
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := Even.convexOn_pow even_two
  have hcont : Continuous (fun y : ℝ => y ^ 2) := by fun_prop
  have hbound : ∀ᵐ t ∂ statLaw P T θ, (rbEstimator Q δ t) ^ 2 ≤ ∫ x, (δ x) ^ 2 ∂ Q t := by
    filter_upwards [haeδ, haesq] with t htδ htsq
    have hj := hconv.map_integral_le hcont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) htδ htsq
    simpa [rbEstimator] using hj
  have hrbsqInt : Integrable (fun t => (rbEstimator Q δ t) ^ 2) (statLaw P T θ) := by
    refine Integrable.mono' hinnerInt ((hrb.measurable.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact ht
  exact (memLp_two_iff_integrable_sq hrb.aestronglyMeasurable).mpr hrbsqInt

/-- **At most one unbiased function of a complete statistic.** If two measurable functions of
a complete statistic are both unbiased for the same estimand, they agree almost everywhere
under every law of the statistic.

Only completeness is used; the classical statement additionally assumes sufficiency, which is
what guarantees that such functions exist but is not needed for uniqueness. -/
theorem unique_unbiased_function_of_complete (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic; needed for the change of variables
    (hT : Measurable T)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {η₁ η₂ : S → ℝ}
    -- LEAN-ONLY: measurability of the two candidate functions
    (hη₁ : Measurable η₁) (hη₂ : Measurable η₂)
    -- LEAN-ONLY: integrability under the laws of the statistic, so that means subtract
    (hi₁ : ∀ θ, Integrable η₁ (statLaw P T θ)) (hi₂ : ∀ θ, Integrable η₂ (statLaw P T θ))
    -- USER-INPUT: both are unbiased for the same estimand
    (hu₁ : IsUnbiased P g fun x => η₁ (T x)) (hu₂ : IsUnbiased P g fun x => η₂ (T x))
    (θ : Θ) :
    η₁ =ᵐ[statLaw P T θ] η₂ := by
  -- the difference of the two functions has identically zero mean under the laws of `T`
  have hz : ∀ θ', ∫ s, (η₁ s - η₂ s) ∂(statLaw P T θ') = 0 := by
    intro θ'
    rw [integral_sub (hi₁ θ') (hi₂ θ')]
    have e1 : ∫ s, η₁ s ∂(statLaw P T θ') = g θ' := by
      rw [statLaw, integral_map hT.aemeasurable hη₁.aestronglyMeasurable]; exact hu₁ θ'
    have e2 : ∫ s, η₂ s ∂(statLaw P T θ') = g θ' := by
      rw [statLaw, integral_map hT.aemeasurable hη₂.aestronglyMeasurable]; exact hu₂ θ'
    rw [e1, e2, sub_self]
  have hfz := hcomp (fun s => η₁ s - η₂ s) (hη₁.sub hη₂)
    (fun θ' => (hi₁ θ').sub (hi₂ θ')) hz θ
  filter_upwards [hfz] with s hs
  simp only [Pi.zero_apply] at hs
  exact sub_eq_zero.mp hs

/-- Lehmann–Scheffé minimality for an **arbitrary** square-integrable unbiased competitor.

The classical argument Rao–Blackwellizes the competitor `δ'` through `T` and compares by
`variance_rbEstimator_le`, then identifies the two Rao–Blackwellizations via
`unique_unbiased_function_of_complete`: both `rbEstimator Q δ` and `rbEstimator Q δ'` are
unbiased functions of the complete statistic `T`, hence a.e. equal, so the variance of the
former equals that of `rbEstimator Q δ' ∘ T`, which does not exceed `var δ'`.

**Added hypothesis (private lemma, pre-authorized).** `hδ'm : Measurable δ'`. Both the kernel
average `t ↦ ∫ δ' dQ_t = rbEstimator Q δ'` and the completeness test function require `δ'` to
carry a genuine (global) measurable representative. The `IsUMVU` minimality quantifies over
competitors holding only `MemEstL2 P δ'`, i.e. a *per-parameter* `AEStronglyMeasurable`
version; with no dominating measure these do not glue to a single measurable function (false
in general — Dirac families are a counterexample). This private lemma is therefore stated for
measurable competitors; the consumer `isUMVU_of_complete_sufficient` cannot discharge that
hypothesis for an arbitrary `MemEstL2` competitor (see the note there). -/
private lemma variance_rbEstimator_le_of_complete (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (g : Θ → ℝ) {T : 𝓧 → S} (hT : Measurable T)
    {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ} (hδm : Measurable δ) (hδu : IsUnbiased P g δ)
    (hδ2 : MemEstL2 P δ) {δ' : 𝓧 → ℝ} (hδ'm : Measurable δ') (hδ'u : IsUnbiased P g δ')
    (hδ'2 : MemEstL2 P δ') (θ : Θ) :
    variance (fun x => rbEstimator Q δ (T x)) (P θ) ≤ variance δ' (P θ) := by
  have hδi : ∀ θ', Integrable δ (P θ') := fun θ' => (hδ2 θ').integrable one_le_two
  have hδ'i : ∀ θ', Integrable δ' (P θ') := fun θ' => (hδ'2 θ').integrable one_le_two
  have hrbδm : Measurable (rbEstimator Q δ) :=
    (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  have hrbδ'm : Measurable (rbEstimator Q δ') :=
    (hδ'm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  -- both Rao–Blackwellizations are unbiased functions of the complete `T`, hence a.e. equal
  have huniq : rbEstimator Q δ =ᵐ[statLaw P T θ] rbEstimator Q δ' :=
    unique_unbiased_function_of_complete P g hT hcomp hrbδm hrbδ'm
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδm hδi θ')
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδ'm hδ'i θ')
      (isUnbiased_rbEstimator P g hT hgraph hδm hδi hδu)
      (isUnbiased_rbEstimator P g hT hgraph hδ'm hδ'i hδ'u) θ
  have hEq : (fun x => rbEstimator Q δ (T x)) =ᵐ[P θ] fun x => rbEstimator Q δ' (T x) :=
    ae_eq_comp hT.aemeasurable huniq
  rw [variance_congr hEq]
  -- Rao–Blackwellization of the competitor does not increase its variance
  exact variance_rbEstimator_le P hT hgraph hδ'm hδ'2 θ

/-- **Lehmann–Scheffé, variance form.** Averaging any unbiased square-integrable estimator
over the fibers of a *complete* sufficient statistic produces the uniformly minimum variance
unbiased estimator of the estimand. -/
theorem isUMVU_of_complete_sufficient (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; sufficiency of the statistic
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the witness lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    IsUMVU P g (fun x => rbEstimator Q δ (T x)) := by
  refine ⟨isUnbiased_rbEstimator P g hT hgraph hδm
      (fun θ' => (hδ2 θ').integrable one_le_two) hδu, ?_, ?_⟩
  · -- square-integrability of the Rao–Blackwellized estimator, transported to the data scale
    intro θ
    have hstat := memLp_two_rbEstimator_statLaw P hT hgraph hδm hδ2 θ
    exact (memLp_map_measure_iff hstat.aestronglyMeasurable hT.aemeasurable).mp hstat
  · -- minimality against every square-integrable unbiased competitor
    intro δ' hδ'u hδ'2 θ
    -- The Rao–Blackwell comparison is `variance_rbEstimator_le_of_complete`, now proven, but it
    -- requires `Measurable δ'` to form the kernel average `t ↦ ∫ δ' dQ_t`. Here `δ'` carries
    -- only `MemEstL2 P δ'` — a per-parameter `AEStronglyMeasurable` version — and with no
    -- dominating measure these do not glue to one global measurable representative. So the
    -- measurability hypothesis of the private lemma is not dischargeable at this frozen
    -- `IsUMVU` interface. A `condExp`-based Rao–Blackwell layer (which needs only
    -- integrability) would close this, but is not among the imported kernel lemmas.
    sorry

/-- **Lehmann–Scheffé, convex-loss form.** The estimator of `isUMVU_of_complete_sufficient`
minimizes the risk among *all* unbiased estimators, simultaneously for every loss that is
convex and nonnegative in the decision argument — its optimality is not tied to squared
error. -/
theorem risk_le_of_complete_sufficient (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (g : Θ → ℝ) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {Q : Kernel S 𝓧} [IsMarkovKernel Q]
    -- USER-INPUT: the θ-free disintegration of the graph law; sufficiency of the statistic
    (hgraph : ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q)
    -- USER-INPUT: completeness of the statistic; the classical hypothesis
    (hcomp : IsCompleteStat P T) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the estimator used to build the optimal one
    (hδm : Measurable δ)
    -- LEAN-ONLY: integrability under every member; fiber integrability is derived from it
    (hδi : ∀ θ, Integrable δ (P θ))
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ) (ρ : Θ → ℝ → ℝ)
    -- USER-INPUT: the loss is convex in the decision argument; the classical hypothesis
    (hconv : ∀ θ, ConvexOn ℝ Set.univ (ρ θ))
    -- LEAN-ONLY: continuity of the loss, automatic for a convex function on all of `ℝ`
    (hcont : ∀ θ, Continuous (ρ θ))
    -- USER-INPUT: the loss is nonnegative, so that `ENNReal.ofReal` loses nothing
    (hnn : ∀ θ y, 0 ≤ ρ θ y) {δ' : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the competitor
    (hδ'm : Measurable δ')
    -- LEAN-ONLY: integrability of the competitor under every member
    (hδ'i : ∀ θ, Integrable δ' (P θ))
    -- USER-INPUT: the competitor is unbiased for the same estimand
    (hδ'u : IsUnbiased P g δ')
    -- USER-INPUT: the competitor has finite risk (otherwise the inequality is trivial)
    (hρi : ∀ θ, Integrable (fun x => ρ θ (δ' x)) (P θ)) (θ : Θ) :
    risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ (T x)) θ ≤
      risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) δ' θ := by
  have hrbδm : Measurable (rbEstimator Q δ) :=
    (hδm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  have hrbδ'm : Measurable (rbEstimator Q δ') :=
    (hδ'm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  -- the two Rao–Blackwellizations are unbiased functions of `T`, hence a.e. equal
  have huniq : rbEstimator Q δ =ᵐ[statLaw P T θ] rbEstimator Q δ' :=
    unique_unbiased_function_of_complete P g hT hcomp hrbδm hrbδ'm
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδm hδi θ')
      (fun θ' => integrable_rbEstimator_statLaw P hT hgraph hδ'm hδ'i θ')
      (isUnbiased_rbEstimator P g hT hgraph hδm hδi hδu)
      (isUnbiased_rbEstimator P g hT hgraph hδ'm hδ'i hδ'u) θ
  have hEq : (fun x => rbEstimator Q δ (T x)) =ᵐ[P θ] fun x => rbEstimator Q δ' (T x) :=
    ae_eq_comp hT.aemeasurable huniq
  have hriskeq : risk P (fun θ' d => ENNReal.ofReal (ρ θ' d))
        (fun x => rbEstimator Q δ (T x)) θ
      = risk P (fun θ' d => ENNReal.ofReal (ρ θ' d)) (fun x => rbEstimator Q δ' (T x)) θ := by
    simp only [risk, crossRisk]
    refine lintegral_congr_ae ?_
    filter_upwards [hEq] with x hx
    rw [hx]
  rw [hriskeq]
  exact risk_rbEstimator_le P hT hgraph hδ'm hδ'i ρ hconv hcont hnn hρi θ

/-- **Full-rank exponential families.** For a family that is a canonical exponential family of
full rank, every estimable function admits a uniformly minimum variance unbiased estimator,
and it is a function of the natural statistic. Statement only: the proof combines the
completeness of the natural statistic of a full-rank family with the two theorems above. -/
theorem isUMVU_of_fullRank_expFamily (E : ExpFamily 𝓧 V) (Ξ : Set V) (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- LEAN-ONLY: the sufficiency kernel of the natural statistic is produced by
    -- `Sufficiency.RegularConditional`, which needs a standard Borel sample space; an
    -- exponential family supplies no explicit reconstruction kernel without such structure.
    -- Standard throughout this literature: every sufficiency theorem in the area carries it.
    [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (ηmap : Θ → V)
    -- USER-INPUT: the family is a reparametrization of the canonical exponential family `E`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: the parametrization covers the full-rank parameter set
    (hcover : Ξ ⊆ Set.range ηmap)
    -- USER-INPUT: full rank — nonempty interior of the parameter set plus an affinely
    -- independent natural statistic
    (hFR : E.FullRank Ξ) (g : Θ → ℝ) {δ : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the witness estimator
    (hδm : Measurable δ)
    -- USER-INPUT: the estimand is estimable, witnessed by the unbiased estimator `δ`
    (hδu : IsUnbiased P g δ)
    -- USER-INPUT: the witness lies in the estimator class `Δ`
    (hδ2 : MemEstL2 P δ) :
    ∃ η : V → ℝ, Measurable η ∧ IsUMVU P g (fun x => η (E.stat x)) := by
  -- BLOCKED at this frozen signature: `V` is an abstract inner-product space
  -- (`[NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]`), and BOTH ingredients
  -- named in the TODO are unavailable for such `V`.
  --
  -- 1. *Completeness of `E.stat`.* The only completeness theorems for the natural statistic —
  --    `Completeness.ExpFamily.isCompleteStat_of_interior_nonempty` (and its `_real` twin) — are
  --    stated for `V = EuclideanSpace ℝ (Fin s)` (resp. `ℝ`): the Laplace/MGF-uniqueness brick
  --    they consume (`ae_eq_zero_of_integral_exp_inner_eq_zero`) is a finite-dimensional fact.
  --    Applying either to our `E : ExpFamily 𝓧 V` is a type mismatch (`V ≠ EuclideanSpace …`).
  --    The generic `isCompleteFamily_of_signed` is `private` and additionally needs
  --    `[BorelSpace V] [SecondCountableTopology V]` plus the very `hsigned` corollary that only
  --    exists Euclidean-side. So `IsCompleteStat P E.stat` cannot be produced here.
  -- 2. *Sufficiency kernel.* `E.isMinimalSufficient_stat` (the sole route to `IsSufficient`)
  --    requires `[BorelSpace V] [SecondCountableTopology V] [SigmaFinite E.base]`, `E.base ≠ 0`,
  --    and an affinely-spanning configuration — none present. Even producing the estimator `η`
  --    (a Rao–Blackwellization along the sufficiency kernel) is therefore impossible.
  --
  -- The statement is TRUE for finite-dimensional Euclidean `V` with `[SigmaFinite E.base]` and
  -- `E.base ≠ 0`, but not provable at this polymorphic frozen signature; adding those V-side
  -- instances/hypotheses is outside the authorized signature change. Left as sanctioned debt.
  sorry

end StatLean.PointEstimation
