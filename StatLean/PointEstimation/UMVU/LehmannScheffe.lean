import StatLean.PointEstimation.UMVU.RaoBlackwell
import StatLean.PointEstimation.Completeness.Defs
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
  sorry

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
  sorry

/-- **Full-rank exponential families.** For a family that is a canonical exponential family of
full rank, every estimable function admits a uniformly minimum variance unbiased estimator,
and it is a function of the natural statistic. Statement only: the proof combines the
completeness of the natural statistic of a full-rank family with the two theorems above. -/
theorem isUMVU_of_fullRank_expFamily (E : ExpFamily 𝓧 V) (Ξ : Set V) (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (ηmap : Θ → V)
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
  sorry

end StatLean.PointEstimation
