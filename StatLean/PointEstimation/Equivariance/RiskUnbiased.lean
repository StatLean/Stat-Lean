import StatLean.PointEstimation.Equivariance.General
import StatLean.PointEstimation.Equivariance.LocationStructure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Risk-unbiasedness of minimum risk equivariant estimators

An estimator is **risk-unbiased** when, on the average, it is at least as close to the
true parameter value as to any false one: `E_θ L(θ, δ(X)) ≤ E_θ L(θ', δ(X))` for every
`θ' ≠ θ`. This is the decision-theoretic extension of unbiasedness — under squared error
it reduces to ordinary unbiasedness, under absolute error to median-unbiasedness.

This file proves that minimum risk equivariant estimators are risk-unbiased, in the
general group setting and in the concrete location setting.

* `isRiskUnbiased_of_equivariant_min` — general form: a transitive induced action on the
  parameter space together with a **commutative** action on the decision space forces a
  risk-minimizing equivariant estimator to be risk-unbiased.
* `isLocRiskUnbiased_of_isLocMRE` / `isRiskUnbiased_of_isLocMRE` — the location
  specialization, where both hypotheses hold automatically (translations act transitively
  on `ℝ` and commutatively on the decisions).
* `locEquivariant_sub_bias` / `integral_eq_zero_of_isLocMRE_sq` — the squared-error
  refinement: recentring an equivariant estimator at its (constant) bias keeps it
  equivariant, makes it unbiased, and strictly improves the risk, whence a
  finite-risk MRE estimator is unbiased.

Both hypotheses of the general theorem are genuinely needed: dropping transitivity or
commutativity produces counterexamples, both of which are exhibited classically by the
normal location-scale problem with a standardized squared-error loss.

**Reference.** Classical equivariance and unbiasedness theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The general proof is three lines and does **not** use model invariance: transitivity
  supplies `g` with `g • θ' = θ`; loss invariance rewrites `L θ' d` as `L θ (g • d)`;
  commutativity of the decision action makes `x ↦ g • δ x` equivariant, so the
  minimality hypothesis applies to it. We therefore state the sharper form, **omitting**
  the invariant-model hypothesis that the classical statement carries. Model invariance
  is what makes the minimality hypothesis `hmin` the natural notion of MRE in the first
  place, but it is not used in the implication.
* `hmin` is stated as an explicit hypothesis rather than through a bundled `IsMRE`
  predicate: the general setting has no canonical constant risk to minimize until
  transitivity has been used, and quantifying over measurable equivariant competitors is
  what the proof consumes.
* In the location case the proof is even shorter and needs no convexity or symmetry of
  the loss: `δ − a` is equivariant whenever `δ` is, so minimality applied to `δ − a`
  *is* risk-unbiasedness. We state that honest form; convexity and evenness of the loss
  enter only the *unbiasedness* (rather than risk-unbiasedness) statements.
* The classical squared-error statement deduces unbiasedness of the MRE estimator from
  its *uniqueness*; the argument in fact needs only finiteness of its risk, which is what
  `integral_eq_zero_of_isLocMRE_sq` assumes. This is a (weakening) deviation.
* The classical third part of the squared-error lemma — an equivariant UMVU estimator is
  MRE — is deliberately omitted here: it belongs to a file that may import the UMVU
  layer, which this area's layering forbids at the equivariance level.

**Bibliographic comments.** Risk-unbiasedness as the decision-theoretic generalization of
unbiasedness is due to E. L. Lehmann, "A general concept of unbiasedness," *Ann. Math.
Statist.* **22** (1951), 587–592. The equivariance framework in which it is proved here
originates with G. A. Hunt and C. Stein (unpublished manuscript, 1946), first reported by
M. A. Girshick and L. J. Savage, "Bayes and minimax estimates for quadratic loss
functions," *Proc. Second Berkeley Symp. Math. Statist. Probab.*, Univ. California Press,
1951, 53–73; the location case goes back to E. J. G. Pitman, "The estimation of the
location and scale parameters of a continuous population of any given form," *Biometrika*
**30** (1939), 391–421.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-! ## The general group setting -/

section General

variable {G Θ 𝓧 D : Type*} [Group G] [MeasurableSpace 𝓧] [MeasurableSpace D]
  [MulAction G 𝓧] [MulAction G Θ] [MulAction G D] [MeasurableConstSMul G D]

/-- Transporting an equivariant estimator by a group element keeps it equivariant, when
the action on the decision space is commutative. This is the step of
`isRiskUnbiased_of_equivariant_min` where commutativity is genuinely used. -/
theorem IsEquivariant.smul {δ : 𝓧 → D}
    -- USER-INPUT: the estimator is equivariant
    (hδeq : IsEquivariant (G := G) δ)
    -- USER-INPUT: the induced action on the decision space is commutative
    (hcomm : ∀ (g g' : G) (d : D), g • g' • d = g' • g • d)
    (g : G) :
    IsEquivariant (G := G) fun x => g • δ x := by
  sorry

/-- **A risk-minimizing equivariant estimator is risk-unbiased**, provided the induced
action on the parameter space is transitive and the action on the decision space is
commutative.

Transitivity lets us move the false parameter value `θ'` onto the true one by some `g`;
loss invariance then converts the cross risk against `θ'` into the risk of the transported
estimator `g • δ`, which commutativity of the decision action keeps equivariant. -/
theorem isRiskUnbiased_of_equivariant_min [MulAction.IsPretransitive G Θ]
    {P : Θ → Measure 𝓧} {L : Θ → D → ℝ≥0∞} {δ : 𝓧 → D}
    -- USER-INPUT: the loss is unchanged by the simultaneous parameter/decision action
    (hL : IsInvariantLoss (G := G) L)
    -- LEAN-ONLY: measurability of the estimator; only needed so that the transported
    -- estimator qualifies as a competitor in `hmin`
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is equivariant
    (hδeq : IsEquivariant (G := G) δ)
    -- USER-INPUT: the induced action on the decision space is commutative
    (hcomm : ∀ (g g' : G) (d : D), g • g' • d = g' • g • d)
    -- USER-INPUT: `δ` minimizes the risk among measurable equivariant estimators (MRE);
    -- under transitivity the risk is constant, so this is minimality of one number
    (hmin : ∀ δ', Measurable δ' → IsEquivariant (G := G) δ' →
      ∀ θ, risk P L δ θ ≤ risk P L δ' θ) :
    IsRiskUnbiased P L δ := by
  sorry

end General

/-! ## The location specialization -/

section Location

variable {n : ℕ}

/-- **A minimum risk equivariant location estimator is risk-unbiased.** Concretely: no
translate `δ − a` of the estimator has smaller expected loss at the base parameter.

No convexity, symmetry or boundedness of the loss is required — the entire content is
that `δ − a` is again equivariant, so equivariant minimality applies to it directly. -/
theorem isLocRiskUnbiased_of_isLocMRE (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ)
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is a minimum risk equivariant estimator for the loss `ρ(d − ξ)`
    (hδ : IsLocMRE f ρ δ)
    (a : ℝ) :
    locRisk f ρ δ ≤ ∫⁻ x, ENNReal.ofReal (ρ (δ x - a)) ∂(locationBase f) := by
  sorry

/-- The same statement in the general vocabulary: a minimum risk equivariant location
estimator is risk-unbiased for the location model with loss `ρ(d − ξ)`. -/
theorem isRiskUnbiased_of_isLocMRE (f : (Fin n → ℝ) → ℝ) (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the change of variables that
    -- transports the cross risk at `ξ` back to the base parameter
    (hρ : Measurable ρ)
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is a minimum risk equivariant estimator
    (hδ : IsLocMRE f ρ δ) :
    IsRiskUnbiased (locationFamily f) (fun ξ d => ENNReal.ofReal (ρ (d - ξ))) δ := by
  sorry

/-! ### Squared error: recentring at the bias -/

/-- **Recentring an equivariant estimator at its bias.** Under squared error, if `δ` is
equivariant and integrable at the base parameter, then subtracting its bias
`b = E₀[δ(X)]` leaves it equivariant, makes it unbiased, and does not increase the risk
(the improvement is exactly `b²`). -/
theorem locEquivariant_sub_bias (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density, so the base member is a probability law
    [IsProbabilityMeasure (locationBase f)]
    {δ : (Fin n → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the estimator
    (hδ : Measurable δ)
    -- USER-INPUT: the estimator is location equivariant
    (heq : IsLocEquivariant δ)
    -- USER-INPUT: the bias exists (finite first moment at the base parameter)
    (hint : Integrable δ (locationBase f)) :
    IsLocEquivariant (fun x => δ x - ∫ y, δ y ∂(locationBase f)) ∧
      (∫ x, (δ x - ∫ y, δ y ∂(locationBase f)) ∂(locationBase f) = 0) ∧
      locRisk f (fun t : ℝ => t ^ 2) (fun x => δ x - ∫ y, δ y ∂(locationBase f)) ≤
        locRisk f (fun t : ℝ => t ^ 2) δ := by
  sorry

/-- **A finite-risk minimum risk equivariant estimator is unbiased under squared error.**

The classical statement derives this from *uniqueness* of the MRE estimator; the argument
in fact only needs its risk to be finite, since recentring improves the risk by exactly
the squared bias. -/
theorem integral_eq_zero_of_isLocMRE_sq (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {δ : (Fin n → ℝ) → ℝ}
    -- USER-INPUT: `δ` is minimum risk equivariant under squared error
    (hMRE : IsLocMRE f (fun t : ℝ => t ^ 2) δ)
    -- USER-INPUT: the bias exists (finite first moment at the base parameter)
    (hint : Integrable δ (locationBase f))
    -- USER-INPUT: the estimator has finite risk; replaces the classical uniqueness
    (hfin : locRisk f (fun t : ℝ => t ^ 2) δ ≠ ∞) :
    ∫ x, δ x ∂(locationBase f) = 0 := by
  sorry

end Location

end StatLean.PointEstimation
