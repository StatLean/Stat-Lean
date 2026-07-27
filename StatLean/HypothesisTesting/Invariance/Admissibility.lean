import StatLean.HypothesisTesting.Tests.Defs
import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Convex.Basic

/-!
# Admissibility of convex acceptance regions in an exponential family

Optimality within a restricted class — invariant tests, say — does not by itself make a
test admissible: a uniformly most powerful invariant test can be beaten uniformly by a
test that is not invariant. Admissibility therefore has to be established separately, and
the classical route for exponential families is *convexity of the acceptance region*.

Two notions are distinguished. A test `φ₀` is **`α`-admissible** against a class of
alternatives when no level-`α` competitor has power at least as large everywhere on that
class without matching it there. It is **d-admissible** when the two-sided comparison —
power at least as large on the alternatives *and* at most as large on the null — forces
equality of the power functions throughout. The second is the decision-theoretic notion;
neither implies the other in general.

The main theorem says: for an exponential family on the natural-statistic scale, if the
acceptance region `A₀` is **closed and convex**, and if every open half-space missing `A₀`
points in a direction along which the alternative class contains an unbounded ray, then
any competing acceptance region that is uniformly no worse than `A₀` on the alternatives
is contained in `A₀` up to a null set. The mechanism is geometric: a competitor
protruding from a closed convex set can be separated from it by a hyperplane, and pushing
the natural parameter to infinity along the direction of that hyperplane makes the
protruding part dominate the likelihood, so the competitor would have to be *strictly*
worse somewhere on the alternatives. Admissibility of `φ₀` follows; if in addition the
size `α` is attained at a point of the closure of the null class, the sharper
`α`-admissibility follows too.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.7
(Admissibility), Theorem 6.7.1 (in an exponential family a test with closed convex acceptance
region is d-admissible) and Corollary 6.7.1 (α-admissibility). (`TSH4 §6.7 Thm 6.7.1, Cor
6.7.1`.)

**Main results.**
* `IsDAdmissible`, `IsAlphaAdmissible` — the two admissibility notions;
* `statScaleFamily`, `statScaleBase` — the induced family and dominating measure on the
  natural-statistic scale;
* `acceptance_subset_of_power_le` — closed convex acceptance region: any uniformly
  no-worse competitor is a.e. contained in it;
* `isDAdmissible_of_convex_acceptance`, `isAlphaAdmissible_of_size_attained` — the two
  admissibility conclusions.

**Proof formalization notes.**
* Everything is stated **on the natural-statistic scale**: acceptance regions are subsets
  of `V = EuclideanSpace ℝ (Fin s)`, the model is the family of laws of the natural
  statistic (`statScaleFamily`), and the null set in the conclusion is measured by the
  image of the reference measure (`statScaleBase`). The source identifies the sample space
  with the statistic scale for this theorem; the sample-space reading is the pullback of
  the statement along the natural statistic.
* The ray condition is transcribed verbatim: *whenever* the open half-space
  `{t : ⟨a, t⟩ > c}` misses `A₀`, there is a point of the alternative class and a sequence
  of scalars tending to infinity keeping `θ* + λₙ a` in the alternative class.
* `IsDAdmissible` quantifies over **all** critical functions, with no level restriction —
  the level enters only in `IsAlphaAdmissible`. This matches the source's two definitions.
* `φ₀` is the **nonrandomized** indicator of the complement of `A₀`. The source notes that
  competitors may be randomized but that nonrandomization of `φ₀` is essential, which is
  why the acceptance region — not merely a critical function — is the primitive here.
* In the `α`-admissibility corollary, `θ₀` is required to lie in the natural parameter set
  as well as in the closure of the null class: this is the content of the source's
  "finite point", i.e. an actual parameter rather than a limit at infinity. Continuity of
  the power function in the natural parameter, used to pass from `θ₀` back into the null
  class, is a property of exponential families and is therefore *not* a hypothesis: it is
  a derivation obligation inside the proof.
* The separation step is the geometric Hahn–Banach theorem for a closed convex set and an
  exterior point (`geometric_hahn_banach_closed_point` in Mathlib's
  `Analysis.LocallyConvex.Separation`).

**Bibliographic comments.** Admissibility of tests with convex acceptance regions in
exponential families, and the ray condition delimiting the alternative classes against
which admissibility holds, come from the work of C. Stein ("The admissibility of Hotelling's
$T^2$-test," *Ann. Math. Statist.* **27** (1956), 616–623) and A. Birnbaum
("Characterizations of complete classes of tests of some multiparametric hypotheses, with
applications to likelihood ratio tests," *Ann. Math. Statist.* **26** (1955), 21–36); the
complete-class theory for such problems was extended by K. Matthes and D. R. Truax
("Tests of composite hypotheses for the multivariate exponential family," *Ann. Math.
Statist.* **38** (1967), 681–697). Admissibility of the one- and two-sided $t$-tests
against all invariant classes of alternatives is due to E. L. Lehmann and C. Stein
(1953), building on their earlier work on non-parametric hypotheses (*Ann. Math. Statist.*
**20** (1949), 28–45).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (ExpFamily)

/-! ## The two admissibility notions -/

section Admissible

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **d-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
if a critical function is at least as powerful as `φ₀` everywhere on `Θ'` and at most as
powerful everywhere on `Θ_H`, then its power function agrees with that of `φ₀` throughout
`Θ_H ∪ Θ'`. No level restriction is imposed on the competitor. -/
def IsDAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    (∀ θ ∈ Θ_H, power P φ θ ≤ power P φ₀ θ) →
    ∀ θ ∈ Θ_H ∪ Θ', power P φ θ = power P φ₀ θ

/-- **`α`-admissibility** of `φ₀` for testing `Θ_H` against a class of alternatives `Θ'`:
every level-`α` competitor that is at least as powerful as `φ₀` everywhere on `Θ'` in fact
has the same power as `φ₀` there. -/
def IsAlphaAdmissible (P : Θ → Measure 𝓧) (Θ_H Θ' : Set Θ) (α : ℝ) (φ₀ : 𝓧 → ℝ) : Prop :=
  ∀ φ : 𝓧 → ℝ, IsCriticalFn φ → IsLevel P Θ_H φ α →
    (∀ θ ∈ Θ', power P φ₀ θ ≤ power P φ θ) →
    ∀ θ ∈ Θ', power P φ θ = power P φ₀ θ

end Admissible

/-! ## The exponential family on the natural-statistic scale -/

section StatScale

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- The **induced family on the natural-statistic scale**: the law of the natural
statistic under the canonical member indexed by `η`. Off the natural parameter set the
member measure is the zero measure, and so is its image. -/
noncomputable def statScaleFamily (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s)) : Measure (EuclideanSpace ℝ (Fin s)) :=
  (E.P η).map E.stat

/-- The **dominating measure on the natural-statistic scale**: the image of the reference
measure of the family under the natural statistic. Null sets for it are the sets the
admissibility conclusion is allowed to ignore. -/
noncomputable def statScaleBase (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) :
    Measure (EuclideanSpace ℝ (Fin s)) :=
  E.base.map E.stat

end StatScale

/-! ## Closed convex acceptance regions are admissible -/

section Convex

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {s : ℕ}

/-- **Separation, in countable form.** If a set has positive measure outside a closed convex
`A₀`, then *some single* open half-space missing `A₀` already carries positive mass of it.

The complement of `A₀` is covered by the open half-spaces produced by
`geometric_hahn_banach_closed_point` at each of its points; a Euclidean space is
second countable, hence Lindelöf, so countably many of them suffice
(`TopologicalSpace.isOpen_iUnion_countable`) and countable subadditivity finishes. -/
private theorem exists_halfspace_of_measure_ne_zero {ρ : Measure (EuclideanSpace ℝ (Fin s))}
    {A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀) (hpos : ρ (A \ A₀) ≠ 0) :
    ∃ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ ∧ ρ (A ∩ {t | c < ⟪a, t⟫_ℝ}) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  refine hpos ?_
  -- a separating open half-space at every point off `A₀`
  have hsep : ∀ p : {q : EuclideanSpace ℝ (Fin s) // q ∉ A₀},
      ∃ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
        A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ ∧ (p : EuclideanSpace ℝ (Fin s)) ∈ {t | c < ⟪a, t⟫_ℝ} := by
    rintro ⟨p, hp⟩
    obtain ⟨f, u, hf, hup⟩ := geometric_hahn_banach_closed_point hA₀convex hA₀closed hp
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin s))).symm f, u, ?_, ?_⟩
    · ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt, InnerProductSpace.toDual_symm_apply]
      exact fun hy => (hf y hy).le
    · simpa only [Set.mem_setOf_eq, InnerProductSpace.toDual_symm_apply] using hup
  choose a c hemp hmem using hsep
  have hopen : ∀ p, IsOpen {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ} := fun p =>
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  obtain ⟨Tc, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable
      (fun p => {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ}) hopen
  have hsub : A \ A₀ ⊆ ⋃ p ∈ Tc, (A ∩ {t | c p < ⟪a p, t⟫_ℝ}) := by
    intro x hx
    have hxU : x ∈ ⋃ p, {t : EuclideanSpace ℝ (Fin s) | c p < ⟪a p, t⟫_ℝ} :=
      Set.mem_iUnion.mpr ⟨⟨x, hx.2⟩, hmem ⟨x, hx.2⟩⟩
    rw [← hTU] at hxU
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxU
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨hx.1, hxp⟩⟩
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff hTc).mpr fun p _ => hcon (a p) (c p) (hemp p))

/-- **A competitor no worse than a closed convex acceptance region is contained in it.**
If `A₀` is closed and convex and every open half-space missing `A₀` points along a
direction in which the alternative class contains an unbounded ray, then any acceptance
region `A` whose acceptance probability is everywhere on the alternatives at most that of
`A₀` satisfies `A ⊆ A₀` up to a null set. -/
theorem acceptance_subset_of_power_le (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ A : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the two acceptance regions, needed to speak of their
    -- probabilities at all
    (hA₀meas : MeasurableSet A₀) (hAmeas : MeasurableSet A)
    -- USER-INPUT: the ray condition — whenever an open half-space misses `A₀`, the
    -- alternative class contains an unbounded ray in the direction of that half-space
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: `A` is nowhere on the alternatives a better acceptance region than `A₀`
    (hpow : ∀ θ ∈ Θ', statScaleFamily E θ A ≤ statScaleFamily E θ A₀) :
    statScaleBase E (A \ A₀) = 0 := by
  classical
  by_contra hne
  -- **Step 1.** Some open half-space missing `A₀` carries base mass of `A`.
  obtain ⟨a, c, hemp, hmass⟩ := exists_halfspace_of_measure_ne_zero hA₀closed hA₀convex hne
  -- **Step 2.** Shrink it to a *strictly* separated half-space, still of positive mass.
  have hunion : A ∩ {t | c < ⟪a, t⟫_ℝ}
      = ⋃ k : ℕ, A ∩ {t | c + 1 / ((k : ℝ) + 1) < ⟪a, t⟫_ℝ} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    refine ⟨fun ⟨ht, hlt⟩ => ?_, fun ⟨k, ht, hlt⟩ => ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact ⟨k, ht, by linarith⟩
    · have hp : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      exact ⟨ht, by linarith⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      statScaleBase E (A ∩ {t | c + 1 / ((k : ℝ) + 1) < ⟪a, t⟫_ℝ}) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hmass (by rw [hunion]; exact measure_iUnion_null hall)
  set δ : ℝ := 1 / ((k : ℝ) + 1) with hδdef
  have hδpos : (0:ℝ) < δ := by rw [hδdef]; positivity
  -- **Step 3.** The ray along which the natural parameter is pushed to infinity.
  obtain ⟨θs, hθs, lam, hlamtop, hlamΘ⟩ := hray a c hemp
  have hTm : Measurable E.stat := E.stat_meas
  have hinnermeas : ∀ v : EuclideanSpace ℝ (Fin s),
      Measurable fun t : EuclideanSpace ℝ (Fin s) => ⟪v, t⟫_ℝ := fun v =>
    (continuous_const.inner continuous_id).measurable
  have hHmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin s) | c + δ < ⟪a, t⟫_ℝ} :=
    measurableSet_lt measurable_const (hinnermeas a)
  set W : Set 𝓧 := E.stat ⁻¹' (A ∩ {t | c + δ < ⟪a, t⟫_ℝ}) with hWdef
  have hWmeas : MeasurableSet W := (hAmeas.inter hHmeas).preimage hTm
  have hWpos : E.base W ≠ 0 := by
    rw [hWdef, ← Measure.map_apply hTm (hAmeas.inter hHmeas)]
    exact hk
  have hbase0 : E.base ≠ 0 := fun h => hWpos (by rw [h]; rfl)
  -- The `θ*`-weight and its total / partial masses.
  set F : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp ⟪θs, E.stat x⟫_ℝ) with hFdef
  have hFmeas : Measurable F :=
    (Real.measurable_exp.comp ((hinnermeas θs).comp hTm)).ennreal_ofReal
  set M : ℝ≥0∞ := ∫⁻ x, F x ∂E.base with hMdef
  set m : ℝ≥0∞ := ∫⁻ x in W, F x ∂E.base with hmdef
  have hMfin : M ≠ ⊤ := by
    rw [hMdef, hFdef, ← ofReal_integral_eq_lintegral_ofReal (hΘ' hθs)
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  have hmM : m ≤ M := setLIntegral_le_lintegral _ _
  have hmfin : m ≠ ⊤ := ne_top_of_le_ne_top hMfin hmM
  have hmpos : m ≠ 0 := by
    intro h0
    have h1 : ∀ᵐ x ∂(E.base.restrict W), F x = 0 := (lintegral_eq_zero_iff hFmeas).mp h0
    rw [ae_iff] at h1
    have h3 : {x : 𝓧 | ¬ F x = 0} = Set.univ := by
      ext x
      simp only [hFdef, Set.mem_setOf_eq, Set.mem_univ, iff_true, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    rw [h3, Measure.restrict_apply_univ] at h1
    exact hWpos h1
  -- **Step 4.** Pick the index at which the tilt already dominates.
  set r : ℝ := M.toReal / m.toReal with hrdef
  have hmtoReal : 0 < m.toReal := ENNReal.toReal_pos hmpos hmfin
  have hrnn : (0:ℝ) ≤ r := by rw [hrdef]; positivity
  obtain ⟨n, hn⟩ :=
    (hlamtop.eventually_ge_atTop (max 0 ((Real.log (r + 1) + 1) / δ))).exists
  have hlam0 : 0 ≤ lam n := le_trans (le_max_left _ _) hn
  have hlarge : r + 1 < Real.exp (lam n * δ) := by
    have h1 : (Real.log (r + 1) + 1) / δ ≤ lam n := le_trans (le_max_right _ _) hn
    rw [div_le_iff₀ hδpos] at h1
    calc r + 1 = Real.exp (Real.log (r + 1)) := (Real.exp_log (by linarith)).symm
      _ < Real.exp (lam n * δ) := Real.exp_lt_exp.mpr (by linarith)
  -- **Step 5.** The analytic core: the tilted comparison at that index.
  have hfinal : m * ENNReal.ofReal (Real.exp (lam n * δ)) ≤ M := by
    set η : EuclideanSpace ℝ (Fin s) := θs + lam n • a with hηdef
    have hηnat : η ∈ E.natSet := hΘ' (hlamΘ n)
    have hsplit : ∀ x : 𝓧,
        ⟪η, E.stat x⟫_ℝ = ⟪θs, E.stat x⟫_ℝ + lam n * ⟪a, E.stat x⟫_ℝ := by
      intro x; rw [hηdef, inner_add_left, real_inner_smul_left]
    have hZpos : 0 < ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base := by
      rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hηnat]
      have hsupp : Function.support (fun x => Real.exp ⟪η, E.stat x⟫_ℝ) = Set.univ := by
        ext x; simp [Function.mem_support, (Real.exp_pos _).ne']
      rw [hsupp, Measure.measure_univ_pos]
      exact hbase0
    -- the normalizer factors out of both sides
    have hexpand : ∀ B : Set (EuclideanSpace ℝ (Fin s)), MeasurableSet B →
        statScaleFamily E η B
          = (∫⁻ x in E.stat ⁻¹' B, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
            * ENNReal.ofReal (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)⁻¹ := by
      intro B hB
      rw [statScaleFamily, Measure.map_apply hTm hB]
      simp only [ExpFamily.P]
      rw [tilted_apply' _ _ (hB.preimage hTm),
        ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hκ0 : ENNReal.ofReal (∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base)⁻¹ ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.mpr hZpos
    have hIle :
        (∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
          ≤ ∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base := by
      have h := hpow η (hlamΘ n)
      rw [hexpand A hAmeas, hexpand A₀ hA₀meas] at h
      exact (ENNReal.mul_le_mul_right hκ0 ENNReal.ofReal_ne_top).mp h
    -- upper bound on the `A₀` side
    have hupper :
        (∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base)
          ≤ M * ENNReal.ofReal (Real.exp (lam n * c)) := by
      have hpt : ∀ x ∈ E.stat ⁻¹' A₀,
          ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ)
            ≤ F x * ENNReal.ofReal (Real.exp (lam n * c)) := by
        intro x hx
        have hle : ⟪a, E.stat x⟫_ℝ ≤ c := by
          by_contra hgt
          push_neg at hgt
          have hmem : E.stat x ∈ A₀ ∩ {t | c < ⟪a, t⟫_ℝ} := ⟨hx, hgt⟩
          rw [hemp] at hmem
          exact hmem
        rw [hsplit x, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, hFdef]
        exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hle hlam0))) _
      calc ∫⁻ x in E.stat ⁻¹' A₀, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base
          ≤ ∫⁻ x in E.stat ⁻¹' A₀, F x * ENNReal.ofReal (Real.exp (lam n * c)) ∂E.base :=
            lintegral_mono_ae
              ((ae_restrict_iff' (hA₀meas.preimage hTm)).mpr (ae_of_all _ hpt))
        _ ≤ ∫⁻ x, F x * ENNReal.ofReal (Real.exp (lam n * c)) ∂E.base :=
            setLIntegral_le_lintegral _ _
        _ = M * ENNReal.ofReal (Real.exp (lam n * c)) := by
            rw [hMdef, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    -- lower bound on the `A` side
    have hlower : m * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
        ≤ ∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base := by
      have hpt : ∀ x ∈ W, F x * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
          ≤ ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) := by
        intro x hx
        have hgt : c + δ < ⟪a, E.stat x⟫_ℝ := hx.2
        rw [hsplit x, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, hFdef]
        exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hgt.le hlam0))) _
      calc m * ENNReal.ofReal (Real.exp (lam n * (c + δ)))
          = ∫⁻ x in W, F x * ENNReal.ofReal (Real.exp (lam n * (c + δ))) ∂E.base := by
            rw [hmdef, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ∫⁻ x in W, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base :=
            lintegral_mono_ae ((ae_restrict_iff' hWmeas).mpr (ae_of_all _ hpt))
        _ ≤ ∫⁻ x in E.stat ⁻¹' A, ENNReal.ofReal (Real.exp ⟪η, E.stat x⟫_ℝ) ∂E.base :=
            lintegral_mono' (Measure.restrict_mono (fun x hx => hx.1) le_rfl) le_rfl
    -- cancel the common factor `e^{λc}`
    have hchain : (m * ENNReal.ofReal (Real.exp (lam n * δ)))
        * ENNReal.ofReal (Real.exp (lam n * c)) ≤ M * ENNReal.ofReal (Real.exp (lam n * c)) := by
      refine le_trans (le_of_eq ?_) (le_trans hlower (le_trans hIle hupper))
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    refine (ENNReal.mul_le_mul_right ?_ ENNReal.ofReal_ne_top).mp hchain
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  -- **Step 6.** But the chosen index makes the left-hand side strictly bigger.
  have hcontra : M < m * ENNReal.ofReal (Real.exp (lam n * δ)) := by
    have hMr : M.toReal < m.toReal * (r + 1) := by
      rw [hrdef, mul_add, mul_one, mul_div_cancel₀ _ hmtoReal.ne']
      linarith
    calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMfin).symm
      _ < ENNReal.ofReal (m.toReal * (r + 1)) := by
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.mpr hMr
      _ ≤ ENNReal.ofReal (m.toReal * Real.exp (lam n * δ)) := by
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hlarge.le hmtoReal.le)
      _ = m * ENNReal.ofReal (Real.exp (lam n * δ)) := by
          rw [ENNReal.ofReal_mul hmtoReal.le, ENNReal.ofReal_toReal hmfin]
  exact absurd hfinal (not_le.mpr hcontra)

/-- **A closed convex acceptance region is d-admissible.** -/
theorem isDAdmissible_of_convex_acceptance (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ') :
    IsDAdmissible (statScaleFamily E) Θ_H Θ'
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  -- TODO: Birnbaum–Stein convexity criterion, not yet formalized. A randomized competitor
  -- `φ` two-sidedly dominating `φ₀ = 1_{A₀ᶜ}` is first reduced (via the Neyman–Pearson
  -- structure of the domination) to an acceptance-region comparison, then
  -- `acceptance_subset_of_power_le` nests the regions and the separating-hyperplane /
  -- tilt-asymptotic argument makes the power comparison strict unless the power functions
  -- coincide. Depends on `acceptance_subset_of_power_le` above plus the reduction of the
  -- randomized competitor to a set. No false hypothesis; statement is TRUE.
  sorry

/-- **A closed convex acceptance region whose size is attained is `α`-admissible.** If in
addition the size of the test is `α` and there is an actual parameter point in the closure
of the null class at which the power equals `α`, then the test is `α`-admissible. -/
theorem isAlphaAdmissible_of_size_attained (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {Θ_H Θ' A₀ : Set (EuclideanSpace ℝ (Fin s))} {α : ℝ}
    {θ₀ : EuclideanSpace ℝ (Fin s)}
    -- USER-INPUT: null and alternative classes sit inside the natural parameter set,
    -- are nonempty and disjoint
    (hΘH : Θ_H ⊆ E.natSet) (hΘ' : Θ' ⊆ E.natSet)
    (hHne : Θ_H.Nonempty) (h'ne : Θ'.Nonempty) (hdisj : Disjoint Θ_H Θ')
    -- USER-INPUT: the acceptance region is closed and convex
    (hA₀closed : IsClosed A₀) (hA₀convex : Convex ℝ A₀)
    -- LEAN-ONLY: measurability of the acceptance region
    (hA₀meas : MeasurableSet A₀)
    -- USER-INPUT: the ray condition
    (hray : ∀ (a : EuclideanSpace ℝ (Fin s)) (c : ℝ),
      A₀ ∩ {t | c < ⟪a, t⟫_ℝ} = ∅ →
        ∃ θstar ∈ Θ', ∃ lam : ℕ → ℝ,
          Filter.Tendsto lam Filter.atTop Filter.atTop ∧ ∀ n, θstar + lam n • a ∈ Θ')
    -- USER-INPUT: the test has level `α` on the null class
    (hlevel : IsLevel (statScaleFamily E) Θ_H (A₀ᶜ.indicator fun _ => (1 : ℝ)) α)
    -- USER-INPUT: the size is attained at a point of the closure of the null class which
    -- is an actual parameter (the source's "finite point")
    (hθ₀closure : θ₀ ∈ closure Θ_H) (hθ₀nat : θ₀ ∈ E.natSet)
    (hθ₀size : power (statScaleFamily E) (A₀ᶜ.indicator fun _ => (1 : ℝ)) θ₀ = α) :
    IsAlphaAdmissible (statScaleFamily E) Θ_H Θ' α
      (A₀ᶜ.indicator fun _ => (1 : ℝ)) := by
  -- TODO: `α`-admissibility, not yet formalized. Reuses `isDAdmissible_of_convex_acceptance`
  -- but additionally needs continuity of the power function
  -- `θ ↦ power (statScaleFamily E) φ₀ θ` at the finite point `θ₀ ∈ closure Θ_H ∩ natSet`
  -- (an exponential-family regularity property, a *derivation* obligation) to turn the
  -- level-`α` hypothesis and size-attainment at `θ₀` into the two-sided power domination on
  -- `Θ_H` required by the d-admissibility theorem. Depends on the two results above plus
  -- exp-family power-continuity. No false hypothesis; statement is TRUE.
  sorry

end Convex

end StatLean.HypothesisTesting
