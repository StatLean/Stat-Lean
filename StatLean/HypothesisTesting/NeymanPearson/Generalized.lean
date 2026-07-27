import StatLean.HypothesisTesting.NeymanPearson.Lemma
import StatLean.HypothesisTesting.ForMathlib.TestsWeakCompact
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The generalized fundamental lemma: maximization under several side conditions

Given integrable `f₁, …, f_{m+1}` and constants `c₁, …, c_m`, consider the class `𝒞` of
critical functions `φ` obeying the `m` side conditions
$$ \int \varphi f_i \, d\mu \;=\; c_i, \qquad i = 1, \dots, m, $$
and the problem of maximizing `∫ φ f_{m+1} dμ` over `𝒞`. A maximizer exists as soon as
`𝒞` is nonempty; it is characterized — sufficiently always, necessarily at inner points
of the attainable-moment set — by the undetermined-multiplier shape
$$ \varphi(x) = 1 \ \text{ when } f_{m+1}(x) > \textstyle\sum_i k_i f_i(x), \qquad
   \varphi(x) = 0 \ \text{ when } f_{m+1}(x) < \textstyle\sum_i k_i f_i(x). $$

Contents:
* `momentSet μ f` — the attainable-moment set `{(∫φf₁dμ, …, ∫φf_mdμ) : φ critical}`;
* `HasMultiplierShape μ f k φ` — the multiplier shape above, `μ`-a.e.;
* `exists_test_max_integral_of_constraints` — existence of a maximizer over `𝒞`;
* `isMax_of_multiplier_form` — sufficiency of the multiplier shape;
* `isMax_le_of_multiplier_form_nonneg` — with `kᵢ ≥ 0`, maximality also against the
  larger class defined by the *inequality* constraints `∫φfᵢdμ ≤ cᵢ`;
* `convex_isClosed_momentSet`, `exists_multipliers_of_max` — the geometry of the moment
  set, and the existence *and* necessity of the multipliers at an inner point;
* `exists_test_with_prescribed_sizes` — a test of prescribed size `α` against `m`
  distributions whose power against the `(m+1)`-st strictly exceeds `α`;
* `isMax_of_lagrangian` — the abstract Lagrangian sufficiency principle behind all of it.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.6 (A Generalization of the Fundamental Lemma), Theorem 3.6.1 (the
generalized fundamental lemma with `m` side conditions), Corollary 3.6.1 and Lemma 3.6.1
(Lagrangian sufficiency). (`TSH4 §3.6 Thm 3.6.1, Cor 3.6.1, Lem 3.6.1`.)

**Proof formalization notes.**
* The classical statement is set on a Euclidean sample space; the only role of that
  assumption is to support the weak compactness theorem for critical functions, which
  holds for a σ-finite dominating measure. We therefore work with a general measurable
  space and `[SigmaFinite μ]`, which is a strict generalization of the printed form.
* The `m` side conditions are indexed by `Fin m` embedded into `Fin (m+1)` via
  `Fin.castSucc`, and the objective is the last coordinate `Fin.last m`. This keeps a
  single function family `f : Fin (m+1) → 𝓧 → ℝ` rather than a pair.
* `HasMultiplierShape` is stated `μ`-a.e. rather than pointwise. This makes the
  sufficiency statements strictly stronger than the printed pointwise form, and makes the
  necessity statement land exactly on the printed conclusion ("(3.30) holds a.e. μ").
* `exists_multipliers_of_max` bundles both halves of the inner-point clause under a
  single `∃ k`: the multipliers exhibited by the supporting hyperplane are the same ones
  that every maximizer is forced to use. Splitting them would silently weaken the result.
* The inner-point hypothesis is transcribed as membership in the ambient `interior` of the
  moment set inside `Fin m → ℝ`. The classical statement is available in two readings:
  ambient interior, or interior relative to the smallest linear space containing the
  moment set. The relative reading is the *weaker hypothesis*, hence the stronger theorem,
  and is the one classically proved. We state only the ambient version here; upgrading to
  the relative-interior hypothesis is a deliberate, documented gap.

**Bibliographic comments.** The extension of the fundamental lemma to several side
conditions is due to J. Neyman and E. S. Pearson ("Contributions to the theory of testing
statistical hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37); its definitive
measure-theoretic form, including the discussion of what happens when the inner-point
condition fails, is due to G. B. Dantzig and A. Wald ("On the fundamental lemma of Neyman
and Pearson," *Ann. Math. Statist.* **22** (1951), 87–93). The use of the resulting
multipliers to construct optimal tests of composite hypotheses is developed in
E. L. Lehmann ("On the existence of least favorable distributions," *Ann. Math. Statist.*
**23** (1952), 408–416).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Integrability of a critical function times an integrable function. -/
private lemma integrable_crit_mul {μ : Measure 𝓧} {p φ : 𝓧 → ℝ} (hp : Integrable p μ)
    (hφ : IsCriticalFn φ) : Integrable (fun x => φ x * p x) μ :=
  hp.bdd_mul hφ.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2)

/-- The **attainable-moment set**: the set of vectors `(∫φf₁dμ, …, ∫φf_mdμ)` obtained as
`φ` ranges over all critical functions. It is convex and closed (`convex_isClosed_momentSet`),
and the constraint vector being one of its inner points is the hypothesis under which
undetermined multipliers exist. For `m = 0` it is the one-point set `{()}`. -/
def momentSet {m : ℕ} (μ : Measure 𝓧) (f : Fin m → 𝓧 → ℝ) : Set (Fin m → ℝ) :=
  {u | ∃ φ, IsCriticalFn φ ∧ ∀ i, ∫ x, φ x * f i x ∂μ = u i}

/-- The **undetermined-multiplier shape** with multipliers `k`: `φ` rejects `μ`-a.e. where
`f_{m+1} > ∑ kᵢfᵢ` and accepts `μ`-a.e. where `f_{m+1} < ∑ kᵢfᵢ`, with no constraint on
the boundary set `{f_{m+1} = ∑ kᵢfᵢ}`. This is the `m`-constraint analogue of the
likelihood-ratio shape; the pointwise form of the classical statement implies it. -/
def HasMultiplierShape {m : ℕ} (μ : Measure 𝓧) (f : Fin (m + 1) → 𝓧 → ℝ) (k : Fin m → ℝ)
    (φ : 𝓧 → ℝ) : Prop :=
  (∀ᵐ x ∂μ, ∑ i, k i * f i.castSucc x < f (Fin.last m) x → φ x = 1) ∧
    (∀ᵐ x ∂μ, f (Fin.last m) x < ∑ i, k i * f i.castSucc x → φ x = 0)

/-! ### Change of measure into `L²`

The analytic engine for both the existence theorem and the closedness of the moment set is
weak compactness of the class of critical functions. `ForMathlib/TestsWeakCompact` supplies
it for `L²` over a **finite** measure; the three private lemmas below transport the problem
there. The classical route via `L^∞(μ) ≅ (L¹(μ))*` is *not* needed: because only finitely
many integrable functions are paired against the tests, one may reweight `μ` so that the
`L¹` pairing becomes an `L²` pairing over a finite measure. -/

/-- **The reweighting.** For finitely many integrable `fᵢ` over a σ-finite `μ` there are a
finite measure `ν` with `μ ≪ ν` and elements `gᵢ ∈ L²(ν)` such that pairing a test against
`gᵢ` in `L²(ν)` computes its `fᵢ`-moment under `μ`.

Concretely: pick a strictly positive integrable `h` (`exists_pos_lintegral_lt_of_sigmaFinite`),
set `w = (∑ᵢ|fᵢ|) + h > 0` (integrable) and `ν = μ.withDensity (ENNReal.ofReal ∘ w)`, a finite
measure with the same null sets as `μ`. The functions `gᵢ = fᵢ / w` lie in `L²(ν)` — the weight
dominates each `fᵢ`, so `∫ gᵢ² dν = ∫ fᵢ²/w dμ ≤ ∫ |fᵢ| dμ < ∞` — and the pairing is preserved,
`∫ φ gᵢ dν = ∫ φ fᵢ dμ`. -/
private lemma exists_l2_reduction {n : ℕ} (μ : Measure 𝓧) [SigmaFinite μ]
    (f : Fin n → 𝓧 → ℝ) (hmeas : ∀ i, Measurable (f i)) (hint : ∀ i, Integrable (f i) μ) :
    ∃ (ν : Measure 𝓧) (g : Fin n → Lp ℝ 2 ν), IsFiniteMeasure ν ∧ μ ≪ ν ∧
      ∀ (φ : 𝓧 → ℝ) (φ' : Lp ℝ 2 ν), ⇑φ' =ᵐ[ν] φ → ∀ i,
        ⟪g i, φ'⟫_ℝ = ∫ x, φ x * f i x ∂μ := by
  classical
  -- A strictly positive integrable weight (σ-finiteness).
  obtain ⟨g0, hg0pos, hg0meas, hg0int⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  let h : 𝓧 → ℝ := fun x => (g0 x : ℝ)
  have hhpos : ∀ x, 0 < h x := fun x => by exact_mod_cast hg0pos x
  have hhmeas : Measurable h := hg0meas.coe_nnreal_real
  have hhint : Integrable h μ :=
    ⟨hhmeas.aestronglyMeasurable, hasFiniteIntegral_iff_ofNNReal.mpr (hg0int.trans_le le_top)⟩
  -- The dominating weight `w = (∑ᵢ |fᵢ|) + h` and the reweighted finite measure `ν`.
  let S : 𝓧 → ℝ := fun x => ∑ i, |f i x|
  have hSmeas : Measurable S :=
    Finset.measurable_sum Finset.univ fun i _ => _root_.continuous_abs.measurable.comp (hmeas i)
  have hSint : Integrable S μ := integrable_finset_sum Finset.univ fun i _ => (hint i).abs
  let w : 𝓧 → ℝ := fun x => S x + h x
  have hwval : ∀ x, w x = S x + h x := fun _ => rfl
  have hwpos : ∀ x, 0 < w x := fun x =>
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => abs_nonneg _) (hhpos x)
  have hwmeas : Measurable w := hSmeas.add hhmeas
  have hwint : Integrable w μ := hSint.add hhint
  set ν : Measure 𝓧 := μ.withDensity (fun x => ENNReal.ofReal (w x)) with hν
  haveI : IsFiniteMeasure ν := by rw [hν]; exact isFiniteMeasure_withDensity_ofReal hwint.2
  have hμν : μ ≪ ν := by
    rw [hν]
    exact withDensity_absolutelyContinuous' hwmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hwpos x)
  -- Each `gᵢ = fᵢ / w` lies in `L²(ν)`.
  have hgmemLp : ∀ i, MemLp (fun x => f i x / w x) 2 ν := by
    intro i
    have hgmeas : Measurable (fun x => f i x / w x) := (hmeas i).div hwmeas
    rw [memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable, hν,
      integrable_withDensity_iff hwmeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine Integrable.mono' (hint i).abs
      (((hgmeas.pow_const 2).mul hwmeas.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable) ?_
    filter_upwards with x
    have hwx := hwpos x
    rw [Real.norm_eq_abs, ENNReal.toReal_ofReal hwx.le,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) hwx.le)]
    have hkey : (f i x / w x) ^ 2 * w x = (f i x) ^ 2 / w x := by
      field_simp
    rw [hkey, div_le_iff₀ hwx]
    have hfw : |f i x| ≤ w x := by
      have hSi : |f i x| ≤ S x :=
        Finset.single_le_sum (f := fun j => |f j x|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      exact hSi.trans (by rw [hwval]; linarith [(hhpos x)])
    calc (f i x) ^ 2 = |f i x| * |f i x| := by rw [← sq_abs]; ring
      _ ≤ |f i x| * w x := mul_le_mul_of_nonneg_left hfw (abs_nonneg _)
  refine ⟨ν, fun i => (hgmemLp i).toLp _, inferInstance, hμν, ?_⟩
  -- The reduction identity: pairing in `L²(ν)` equals the moment in `μ`.
  intro φ φ' hφ' i
  rw [real_inner_comm, ← toWeakDualL2_apply, toWeakDualL2_apply_eq_integral]
  have hφμ : ⇑φ' =ᵐ[μ] φ := hμν.ae_eq hφ'
  have hgμ : ⇑((hgmemLp i).toLp _) =ᵐ[μ] (fun x => f i x / w x) :=
    hμν.ae_eq (MemLp.coeFn_toLp (hgmemLp i))
  -- Abstract the integrand to hide `ν` from the coercions' types before rewriting `ν`.
  set F : 𝓧 → ℝ := fun x => ⇑φ' x * ⇑((hgmemLp i).toLp _) x with hF
  rw [hν, integral_withDensity_eq_integral_toReal_smul hwmeas.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) F]
  refine integral_congr_ae ?_
  filter_upwards [hφμ, hgμ] with x hx hgx
  have hwx := hwpos x
  simp only [hF]
  rw [ENNReal.toReal_ofReal hwx.le, smul_eq_mul, hx, hgx]
  field_simp

/-- A critical function lies in `L²` of any finite measure. -/
private lemma memLp_two_of_isCriticalFn {ν : Measure 𝓧} [IsFiniteMeasure ν] {φ : 𝓧 → ℝ}
    (hφ : IsCriticalFn φ) : MemLp φ 2 ν :=
  MemLp.of_bound hφ.1.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2)

/-- …and its class lands in the `L²` test class. -/
private lemma toLp_mem_testClassL2 {ν : Measure 𝓧} [IsFiniteMeasure ν] {φ : 𝓧 → ℝ}
    (hφ : IsCriticalFn φ) : (memLp_two_of_isCriticalFn hφ).toLp φ ∈ testClassL2 ν := by
  constructor
  · filter_upwards [MemLp.coeFn_toLp (memLp_two_of_isCriticalFn hφ)] with x hx
    rw [Pi.zero_apply, hx]; exact (hφ.2 x).1
  · filter_upwards [MemLp.coeFn_toLp (memLp_two_of_isCriticalFn hφ)] with x hx
    rw [hx]; exact (hφ.2 x).2

/-- Conversely, every member of the `L²` test class has an honest critical function as an
a.e. representative: truncate a strongly measurable representative to `[0,1]`. -/
private lemma exists_isCriticalFn_aeEq {ν : Measure 𝓧} {φ' : Lp ℝ 2 ν}
    (hφ' : φ' ∈ testClassL2 ν) : ∃ φ, IsCriticalFn φ ∧ ⇑φ' =ᵐ[ν] φ := by
  have hae : AEStronglyMeasurable (⇑φ') ν := Lp.aestronglyMeasurable φ'
  refine ⟨fun x => max 0 (min 1 (hae.mk _ x)),
    ⟨measurable_const.max (measurable_const.min hae.measurable_mk),
      fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩, ?_⟩
  filter_upwards [hae.ae_eq_mk, hφ'.1, hφ'.2] with x hmk hpos hle
  simp only [← hmk]
  rw [min_eq_right (by exact hle), max_eq_right (by exact hpos)]

/-- **Existence (i).** If some critical function satisfies the `m` side conditions, then
one of them maximizes `∫ φ f_{m+1} dμ` over the whole class.

**Proof.** Transport the problem into `L²(ν)` along `exists_l2_reduction`; the constraint
class becomes `constrainedTestClassL2 ν (g ∘ Fin.castSucc) c`, which is nonempty by
hypothesis and weak-* compact (`ForMathlib/TestsWeakCompact`), so the moment functional
`⟪g_{m+1}, ·⟫` attains its maximum there (`exists_max_inner_of_constraints`). Truncating an
`L²` representative of the maximizer back to `[0,1]` produces the critical function. -/
theorem exists_test_max_integral_of_constraints {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite (replaces the Euclidean-space assumption)
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    (f : Fin (m + 1) → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data (needed for the integrals to be meaningful)
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data — the printed hypothesis "integrable μ"
    (hint : ∀ i, Integrable (f i) μ)
    -- USER-INPUT: the prescribed values of the side conditions
    (c : Fin m → ℝ)
    -- USER-INPUT: the constraint class is nonempty (printed as "there exists a critical
    -- function φ satisfying (3.29)"); without it the conclusion is false for `m ≥ 1`
    (hne : ∃ φ, IsCriticalFn φ ∧ ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) :
    ∃ φ, IsCriticalFn φ ∧ (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) ∧
      ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
        ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  classical
  obtain ⟨ν, g, hνfin, hμν, hred⟩ := exists_l2_reduction μ f hmeas hint
  haveI := hνfin
  -- A critical function meeting the side conditions is a member of the constrained class.
  have hmemb : ∀ (φ : 𝓧 → ℝ) (hφ : IsCriticalFn φ),
      (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) →
        (memLp_two_of_isCriticalFn hφ).toLp φ ∈
          constrainedTestClassL2 ν (fun i : Fin m => g i.castSucc) c := by
    intro φ hφ hcon
    refine ⟨toLp_mem_testClassL2 hφ, fun i => ?_⟩
    rw [hred φ _ (MemLp.coeFn_toLp (memLp_two_of_isCriticalFn hφ)) i.castSucc]
    exact hcon i
  obtain ⟨φ₀, hφ₀c, hφ₀con⟩ := hne
  obtain ⟨F, hF, hFmax⟩ := exists_max_inner_of_constraints ν (fun i : Fin m => g i.castSucc) c
    (g (Fin.last m)) ⟨_, hmemb φ₀ hφ₀c hφ₀con⟩
  obtain ⟨φ, hφc, hφeq⟩ := exists_isCriticalFn_aeEq hF.1
  refine ⟨φ, hφc, fun i => ?_, fun ψ hψ hψcon => ?_⟩
  · rw [← hred φ F hφeq i.castSucc]
    exact hF.2 i
  · have hmax := hFmax _ (hmemb ψ hψ hψcon)
    rwa [hred ψ _ (MemLp.coeFn_toLp (memLp_two_of_isCriticalFn hψ)) (Fin.last m),
      hred φ F hφeq (Fin.last m)] at hmax

/-- **Sufficiency (ii).** A member of the constraint class that has the multiplier shape
for *some* multipliers `k` maximizes `∫ φ f_{m+1} dμ` over that class. No sign condition
on `k` is needed here. -/
theorem isMax_of_multiplier_form {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    {f : Fin (m + 1) → 𝓧 → ℝ}
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ} {k : Fin m → ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the candidate satisfies the side conditions
    (hcon : ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i)
    -- USER-INPUT: the candidate has the multiplier shape for the given `k`
    (hshape : HasMultiplierShape μ f k φ) :
    ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
      ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  intro ψ hψ hψcon
  obtain ⟨hsp1, hsp0⟩ := hshape
  set S : 𝓧 → ℝ := fun x => ∑ i, k i * f i.castSucc x with hSdef
  -- Pointwise `(φ − ψ)(f_last − S) ≥ 0`.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * (f (Fin.last m) x - S x) := by
    filter_upwards [hsp1, hsp0] with x hx1 hx0
    have hφ1 := (hφ.2 x).2; have hψ0 := (hψ.2 x).1; have hψ1 := (hψ.2 x).2
    rcases lt_trichotomy (S x) (f (Fin.last m) x) with hlt | heq | hgt
    · rw [hx1 hlt]; exact mul_nonneg (by linarith) (by linarith)
    · have hz : f (Fin.last m) x - S x = 0 := by linarith
      simp [hz]
    · rw [hx0 hgt]
      have hrw : (0 - ψ x) * (f (Fin.last m) x - S x) = ψ x * (S x - f (Fin.last m) x) := by ring
      rw [hrw]; exact mul_nonneg (by linarith) (by linarith)
  have hnn := integral_nonneg_of_ae hpt
  -- Integrability data.
  have hfi : ∀ i, Integrable (fun x => φ x * f i x) μ := fun i => integrable_crit_mul (hint i) hφ
  have hgi : ∀ i, Integrable (fun x => ψ x * f i x) μ := fun i => integrable_crit_mul (hint i) hψ
  have hSint : Integrable S μ := by
    refine integrable_finset_sum Finset.univ fun i _ => ?_
    exact ((hint i.castSucc).const_mul (k i))
  have hφlast := hfi (Fin.last m)
  have hψlast := hgi (Fin.last m)
  have hφS : Integrable (fun x => φ x * S x) μ := integrable_crit_mul hSint hφ
  have hψS : Integrable (fun x => ψ x * S x) μ := integrable_crit_mul hSint hψ
  -- Expand the nonnegative integral.
  have hexpand : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
      = (∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ)
        - ∑ i, k i * (∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ) := by
    have hφSeq : ∫ x, φ x * S x ∂μ = ∑ i, k i * ∫ x, φ x * f i.castSucc x ∂μ := by
      rw [hSdef]
      rw [show (fun x => φ x * ∑ i, k i * f i.castSucc x)
          = fun x => ∑ i, k i * (φ x * f i.castSucc x) from by
        funext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      rw [integral_finset_sum Finset.univ
        (fun i _ => (integrable_crit_mul (hint i.castSucc) hφ).const_mul (k i))]
      refine Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    have hψSeq : ∫ x, ψ x * S x ∂μ = ∑ i, k i * ∫ x, ψ x * f i.castSucc x ∂μ := by
      rw [hSdef]
      rw [show (fun x => ψ x * ∑ i, k i * f i.castSucc x)
          = fun x => ∑ i, k i * (ψ x * f i.castSucc x) from by
        funext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      rw [integral_finset_sum Finset.univ
        (fun i _ => (integrable_crit_mul (hint i.castSucc) hψ).const_mul (k i))]
      refine Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    have hAB : ∫ x, (φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x) ∂μ
        = ∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ :=
      integral_sub hφlast hψlast
    have hDE : ∫ x, (φ x * S x - ψ x * S x) ∂μ
        = ∫ x, φ x * S x ∂μ - ∫ x, ψ x * S x ∂μ :=
      integral_sub hφS hψS
    have hADBE : ∫ x, ((φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x)
          - (φ x * S x - ψ x * S x)) ∂μ
        = ∫ x, (φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x) ∂μ
          - ∫ x, (φ x * S x - ψ x * S x) ∂μ :=
      integral_sub (hφlast.sub hψlast) (hφS.sub hψS)
    have hstep : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
        = (∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ)
          - (∫ x, φ x * S x ∂μ - ∫ x, ψ x * S x ∂μ) := by
      have he1 : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
          = ∫ x, ((φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x)
              - (φ x * S x - ψ x * S x)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [he1, hADBE, hAB, hDE]
    rw [hstep, hφSeq, hψSeq, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexpand] at hnn
  -- Each constraint difference vanishes.
  have hzero : ∀ i : Fin m,
      ∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ = 0 := by
    intro i; rw [hcon i, hψcon i, sub_self]
  have hsumzero : ∑ i, k i * (∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ) = 0 := by
    refine Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]
  rw [hsumzero, sub_zero] at hnn
  linarith

/-- **Sufficiency (iii), nonnegative multipliers.** If the multipliers are nonnegative,
the same test is maximal against the *larger* competitor class defined by the inequality
constraints `∫ψfᵢdμ ≤ cᵢ`. -/
theorem isMax_le_of_multiplier_form_nonneg {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    {f : Fin (m + 1) → 𝓧 → ℝ}
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ} {k : Fin m → ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the candidate is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the candidate satisfies the side conditions with equality
    (hcon : ∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i)
    -- USER-INPUT: the multipliers are nonnegative — exactly what upgrades the competitor
    -- class from equality to inequality constraints
    (hk : ∀ i, 0 ≤ k i)
    -- USER-INPUT: the candidate has the multiplier shape for the given `k`
    (hshape : HasMultiplierShape μ f k φ) :
    ∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ ≤ c i) →
      ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ := by
  intro ψ hψ hψcon
  obtain ⟨hsp1, hsp0⟩ := hshape
  set S : 𝓧 → ℝ := fun x => ∑ i, k i * f i.castSucc x with hSdef
  -- Pointwise `(φ − ψ)(f_last − S) ≥ 0`.
  have hpt : 0 ≤ᵐ[μ] fun x => (φ x - ψ x) * (f (Fin.last m) x - S x) := by
    filter_upwards [hsp1, hsp0] with x hx1 hx0
    have hφ1 := (hφ.2 x).2; have hψ0 := (hψ.2 x).1; have hψ1 := (hψ.2 x).2
    rcases lt_trichotomy (S x) (f (Fin.last m) x) with hlt | heq | hgt
    · rw [hx1 hlt]; exact mul_nonneg (by linarith) (by linarith)
    · have hz : f (Fin.last m) x - S x = 0 := by linarith
      simp [hz]
    · rw [hx0 hgt]
      have hrw : (0 - ψ x) * (f (Fin.last m) x - S x) = ψ x * (S x - f (Fin.last m) x) := by ring
      rw [hrw]; exact mul_nonneg (by linarith) (by linarith)
  have hnn := integral_nonneg_of_ae hpt
  -- Integrability data.
  have hfi : ∀ i, Integrable (fun x => φ x * f i x) μ := fun i => integrable_crit_mul (hint i) hφ
  have hgi : ∀ i, Integrable (fun x => ψ x * f i x) μ := fun i => integrable_crit_mul (hint i) hψ
  have hSint : Integrable S μ := by
    refine integrable_finset_sum Finset.univ fun i _ => ?_
    exact ((hint i.castSucc).const_mul (k i))
  have hφlast := hfi (Fin.last m)
  have hψlast := hgi (Fin.last m)
  have hφS : Integrable (fun x => φ x * S x) μ := integrable_crit_mul hSint hφ
  have hψS : Integrable (fun x => ψ x * S x) μ := integrable_crit_mul hSint hψ
  -- Expand the nonnegative integral.
  have hexpand : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
      = (∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ)
        - ∑ i, k i * (∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ) := by
    have hφSeq : ∫ x, φ x * S x ∂μ = ∑ i, k i * ∫ x, φ x * f i.castSucc x ∂μ := by
      rw [hSdef]
      rw [show (fun x => φ x * ∑ i, k i * f i.castSucc x)
          = fun x => ∑ i, k i * (φ x * f i.castSucc x) from by
        funext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      rw [integral_finset_sum Finset.univ
        (fun i _ => (integrable_crit_mul (hint i.castSucc) hφ).const_mul (k i))]
      refine Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    have hψSeq : ∫ x, ψ x * S x ∂μ = ∑ i, k i * ∫ x, ψ x * f i.castSucc x ∂μ := by
      rw [hSdef]
      rw [show (fun x => ψ x * ∑ i, k i * f i.castSucc x)
          = fun x => ∑ i, k i * (ψ x * f i.castSucc x) from by
        funext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      rw [integral_finset_sum Finset.univ
        (fun i _ => (integrable_crit_mul (hint i.castSucc) hψ).const_mul (k i))]
      refine Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    have hAB : ∫ x, (φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x) ∂μ
        = ∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ :=
      integral_sub hφlast hψlast
    have hDE : ∫ x, (φ x * S x - ψ x * S x) ∂μ
        = ∫ x, φ x * S x ∂μ - ∫ x, ψ x * S x ∂μ :=
      integral_sub hφS hψS
    have hADBE : ∫ x, ((φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x)
          - (φ x * S x - ψ x * S x)) ∂μ
        = ∫ x, (φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x) ∂μ
          - ∫ x, (φ x * S x - ψ x * S x) ∂μ :=
      integral_sub (hφlast.sub hψlast) (hφS.sub hψS)
    have hstep : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
        = (∫ x, φ x * f (Fin.last m) x ∂μ - ∫ x, ψ x * f (Fin.last m) x ∂μ)
          - (∫ x, φ x * S x ∂μ - ∫ x, ψ x * S x ∂μ) := by
      have he1 : ∫ x, (φ x - ψ x) * (f (Fin.last m) x - S x) ∂μ
          = ∫ x, ((φ x * f (Fin.last m) x - ψ x * f (Fin.last m) x)
              - (φ x * S x - ψ x * S x)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [he1, hADBE, hAB, hDE]
    rw [hstep, hφSeq, hψSeq, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexpand] at hnn
  -- Each constraint difference is nonnegative, and `kᵢ ≥ 0`, so the sum is nonnegative.
  have hdiffnn : ∀ i : Fin m,
      0 ≤ ∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ := by
    intro i
    rw [hcon i]; linarith [hψcon i]
  have hsumnn : 0 ≤ ∑ i, k i * (∫ x, φ x * f i.castSucc x ∂μ - ∫ x, ψ x * f i.castSucc x ∂μ) := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hk i) (hdiffnn i)
  linarith

/-! ### The Lagrangian characterization of the multiplier shape -/

/-- Expanding the Lagrangian integral of a critical function into its moments. -/
private lemma integral_lagrangian {m : ℕ} {μ : Measure 𝓧} {f : Fin (m + 1) → 𝓧 → ℝ}
    (hint : ∀ i, Integrable (f i) μ) (k : Fin m → ℝ) {ψ : 𝓧 → ℝ} (hψ : IsCriticalFn ψ) :
    ∫ x, ψ x * (f (Fin.last m) x - ∑ i, k i * f i.castSucc x) ∂μ
      = ∫ x, ψ x * f (Fin.last m) x ∂μ - ∑ i, k i * ∫ x, ψ x * f i.castSucc x ∂μ := by
  have hlast := integrable_crit_mul (hint (Fin.last m)) hψ
  have hi : ∀ i : Fin m, Integrable (fun x => k i * (ψ x * f i.castSucc x)) μ :=
    fun i => (integrable_crit_mul (hint i.castSucc) hψ).const_mul (k i)
  have hsum : Integrable (fun x => ∑ i, k i * (ψ x * f i.castSucc x)) μ :=
    integrable_finset_sum _ fun i _ => hi i
  rw [show (fun x => ψ x * (f (Fin.last m) x - ∑ i, k i * f i.castSucc x))
      = fun x => ψ x * f (Fin.last m) x - ∑ i, k i * (ψ x * f i.castSucc x) from by
    funext x
    rw [mul_sub, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)]
  rw [integral_sub hlast hsum, integral_finset_sum _ fun i _ => hi i]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => integral_const_mul _ _)

/-- **The multiplier shape is exactly Lagrangian optimality.** A critical function that
maximizes the Lagrangian `∫ φ (f_{m+1} − ∑ kᵢfᵢ) dμ` over *all* critical functions has the
multiplier shape for `k`.

The supremum is `∫ G⁺ dμ` with `G = f_{m+1} − ∑ kᵢfᵢ`, attained by the indicator of
`{G > 0}`; the difference `G⁺ − φG` is pointwise nonnegative for `φ ∈ [0,1]`, so a maximizer
makes it vanish a.e., which is `φ = 1` on `{G > 0}` and `φ = 0` on `{G < 0}`. -/
private lemma hasMultiplierShape_of_lagrangian_max {m : ℕ} {μ : Measure 𝓧}
    {f : Fin (m + 1) → 𝓧 → ℝ} (hmeas : ∀ i, Measurable (f i)) (hint : ∀ i, Integrable (f i) μ)
    (k : Fin m → ℝ) {φ : 𝓧 → ℝ} (hφ : IsCriticalFn φ)
    (hmax : ∀ ψ, IsCriticalFn ψ →
      ∫ x, ψ x * (f (Fin.last m) x - ∑ i, k i * f i.castSucc x) ∂μ
        ≤ ∫ x, φ x * (f (Fin.last m) x - ∑ i, k i * f i.castSucc x) ∂μ) :
    HasMultiplierShape μ f k φ := by
  classical
  set G : 𝓧 → ℝ := fun x => f (Fin.last m) x - ∑ i, k i * f i.castSucc x with hGdef
  have hGmeas : Measurable G :=
    (hmeas _).sub (Finset.measurable_sum Finset.univ fun i _ => (hmeas i.castSucc).const_mul (k i))
  have hGint : Integrable G μ :=
    (hint _).sub (integrable_finset_sum Finset.univ fun i _ => (hint i.castSucc).const_mul (k i))
  -- The indicator of `{G > 0}` is a critical function attaining the supremum.
  set ind : 𝓧 → ℝ := fun x => if 0 < G x then 1 else 0 with hinddef
  have hindc : IsCriticalFn ind := by
    refine ⟨Measurable.ite (measurableSet_lt measurable_const hGmeas)
      measurable_const measurable_const, fun x => ?_⟩
    simp only [hinddef]
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hpt : ∀ x, φ x * G x ≤ ind x * G x := by
    intro x
    simp only [hinddef]
    split_ifs with hx
    · rw [one_mul]; nlinarith [(hφ.2 x).2]
    · rw [zero_mul]; push_neg at hx; nlinarith [(hφ.2 x).1]
  have hnn : 0 ≤ᵐ[μ] fun x => ind x * G x - φ x * G x :=
    Filter.Eventually.of_forall fun x => sub_nonneg.mpr (hpt x)
  have hi1 : Integrable (fun x => ind x * G x) μ := integrable_crit_mul hGint hindc
  have hi2 : Integrable (fun x => φ x * G x) μ := integrable_crit_mul hGint hφ
  have hz : ∫ x, (ind x * G x - φ x * G x) ∂μ = 0 :=
    le_antisymm (by rw [integral_sub hi1 hi2]; linarith [hmax ind hindc])
      (integral_nonneg_of_ae hnn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hi1.sub hi2)).mp hz
  constructor
  · filter_upwards [hae] with x hx hgt
    have hG : 0 < G x := by simp only [hGdef]; linarith
    simp only [Pi.zero_apply, hinddef, if_pos hG, one_mul] at hx
    have hfac : G x * (1 - φ x) = 0 := by linear_combination hx
    have := (mul_eq_zero.mp hfac).resolve_left (ne_of_gt hG)
    linarith
  · filter_upwards [hae] with x hx hlt
    have hG : G x < 0 := by simp only [hGdef]; linarith
    simp only [Pi.zero_apply, hinddef, if_neg (not_lt.mpr hG.le), zero_mul, zero_sub,
      neg_eq_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_right (ne_of_lt hG)

/-- **Closedness of the attainable-moment set** — the hard half of `convex_isClosed_momentSet`.

Closedness is the weak-* compactness of the class of critical functions, transported through the
bounded moment map `φ ↦ (∫ φ fᵢ dμ)` into `Fin m → ℝ`.

**Proof.** Move to `L²` of a finite measure with `exists_l2_reduction`. There `momentSet μ f`
becomes the continuous image, under `L ↦ (L gᵢ)ᵢ`, of the weak-* compact class of `[0,1]`-valued
`L²(ν)` functions (`isCompact_toWeakDualL2_image_testClass`). A continuous image of a compact
set is compact, and a compact subset of `ℝᵐ` is closed. -/
private lemma isClosed_momentSet {m : ℕ} (μ : Measure 𝓧) [SigmaFinite μ]
    (f : Fin m → 𝓧 → ℝ) (hmeas : ∀ i, Measurable (f i)) (hint : ∀ i, Integrable (f i) μ) :
    IsClosed (momentSet μ f) := by
  classical
  obtain ⟨ν, gL, hνfin, hμν, hred⟩ := exists_l2_reduction μ f hmeas hint
  haveI := hνfin
  -- Restate the reduction in weak-dual form.
  have reduction : ∀ (φ : 𝓧 → ℝ) (φ' : Lp ℝ 2 ν), ⇑φ' =ᵐ[ν] φ → ∀ i,
      toWeakDualL2 ν φ' (gL i) = ∫ x, φ x * f i x ∂μ := by
    intro φ φ' hφ' i
    rw [toWeakDualL2_apply, real_inner_comm]
    exact hred φ φ' hφ' i
  -- The continuous moment map `Φ : WeakDual ℝ (L²(ν)) → ℝᵐ`.
  set Φ : WeakDual ℝ (Lp ℝ 2 ν) → (Fin m → ℝ) := fun L i => L (gL i) with hΦ
  have hΦcont : Continuous Φ := continuous_pi fun i => continuous_eval_weakDual ν (gL i)
  -- `momentSet μ f` is the continuous image of the weak-* compact test class.
  have hset : momentSet μ f = Φ '' (toWeakDualL2 ν '' testClassL2 ν) := by
    ext u
    constructor
    · rintro ⟨φ, hφcrit, hφmom⟩
      refine ⟨toWeakDualL2 ν ((memLp_two_of_isCriticalFn hφcrit).toLp φ),
        ⟨_, toLp_mem_testClassL2 hφcrit, rfl⟩, ?_⟩
      funext i
      change toWeakDualL2 ν ((memLp_two_of_isCriticalFn hφcrit).toLp φ) (gL i) = u i
      rw [reduction φ _ (MemLp.coeFn_toLp (memLp_two_of_isCriticalFn hφcrit)) i, hφmom i]
    · rintro ⟨L, ⟨φ', hφ'test, rfl⟩, rfl⟩
      obtain ⟨φ, hφcrit, hφφ'⟩ := exists_isCriticalFn_aeEq hφ'test
      exact ⟨φ, hφcrit, fun i => (reduction φ φ' hφφ' i).symm⟩
  rw [hset]
  exact (((isCompact_toWeakDualL2_image_testClass ν).image hΦcont)).isClosed

/-- **Geometry of the moment set (iv, first clause).** The attainable-moment set is convex
and closed. Convexity is immediate from convexity of the class of critical functions;
closedness is the weak compactness theorem for critical functions (lifted to the named private
lemma `isClosed_momentSet`; see its docstring for the exact missing Mathlib brick). -/
theorem convex_isClosed_momentSet {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the constraint functions
    (f : Fin m → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ) :
    Convex ℝ (momentSet μ f) ∧ IsClosed (momentSet μ f) := by
  refine ⟨?_, ?_⟩
  · -- Convexity: a convex combination of critical functions is critical, and its moments
    -- are the convex combination of the moments (linearity of the integral).
    rintro u ⟨φ, hφc, hφm⟩ v ⟨ψ, hψc, hψm⟩ a b ha hb hab
    have hfi : ∀ i, Integrable (fun x => φ x * f i x) μ :=
      fun i => integrable_crit_mul (hint i) hφc
    have hgi : ∀ i, Integrable (fun x => ψ x * f i x) μ :=
      fun i => integrable_crit_mul (hint i) hψc
    refine ⟨fun x => a * φ x + b * ψ x, ⟨?_, fun x => ?_⟩, fun i => ?_⟩
    · exact (hφc.1.const_mul a).add (hψc.1.const_mul b)
    · have hφx := hφc.2 x; have hψx := hψc.2 x
      constructor
      · have := mul_nonneg ha hφx.1
        have := mul_nonneg hb hψx.1
        linarith
      · have h1 : a * φ x ≤ a * 1 := mul_le_mul_of_nonneg_left hφx.2 ha
        have h2 : b * ψ x ≤ b * 1 := mul_le_mul_of_nonneg_left hψx.2 hb
        have : a * φ x + b * ψ x ≤ a * 1 + b * 1 := by linarith
        rw [mul_one, mul_one] at this; linarith [this, hab]
    · change ∫ x, (a * φ x + b * ψ x) * f i x ∂μ = (a • u + b • v) i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hφm i, ← hψm i]
      rw [show (fun x => (a * φ x + b * ψ x) * f i x)
          = fun x => a * (φ x * f i x) + b * (ψ x * f i x) from by funext x; ring]
      rw [integral_add ((hfi i).const_mul a) ((hgi i).const_mul b),
        integral_const_mul, integral_const_mul]
  · -- Closedness is lifted to the named private lemma `isClosed_momentSet`; its docstring
    -- pins the exact missing Mathlib brick (`L^∞ = (L¹)*`). Convexity above is complete.
    exact isClosed_momentSet μ f hmeas hint

/-- **Multipliers exist, and are forced (iv, second clause).** If the constraint vector is
an inner point of the attainable-moment set, then there are multipliers `k` such that

* some critical function satisfies the side conditions *and* has the multiplier shape;
* **every** maximizer in the constraint class has that same shape `μ`-a.e.

The two halves share one `∃ k`: the multipliers produced by the supporting hyperplane are
the ones every maximizer must use. -/
theorem exists_multipliers_of_max {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` real-valued functions of the problem
    (f : Fin (m + 1) → 𝓧 → ℝ)
    -- USER-INPUT: measurability of the data
    (hmeas : ∀ i, Measurable (f i))
    -- USER-INPUT: integrability of the data
    (hint : ∀ i, Integrable (f i) μ)
    {c : Fin m → ℝ}
    -- USER-INPUT: the constraint vector is an *inner point* of the attainable-moment set
    -- (ambient interior in `Fin m → ℝ`); this is the printed hypothesis, and it cannot be
    -- dropped: on the boundary the multiplier characterization genuinely fails
    (hc : c ∈ interior (momentSet μ fun i => f i.castSucc)) :
    ∃ k : Fin m → ℝ,
      (∃ φ, IsCriticalFn φ ∧ (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) ∧
        HasMultiplierShape μ f k φ) ∧
      ∀ φ, IsCriticalFn φ → (∀ i, ∫ x, φ x * f i.castSucc x ∂μ = c i) →
        (∀ ψ, IsCriticalFn ψ → (∀ i, ∫ x, ψ x * f i.castSucc x ∂μ = c i) →
          ∫ x, ψ x * f (Fin.last m) x ∂μ ≤ ∫ x, φ x * f (Fin.last m) x ∂μ) →
        HasMultiplierShape μ f k φ := by
  -- OBSTRUCTION (deep debt). This is the necessity/existence half of the inner-point clause
  -- and it needs two ingredients neither of which is available. (1) The attainable-moment set
  -- must be convex AND closed; convexity is proved in `convex_isClosed_momentSet`, but its
  -- closedness is the open weak-sequential-compactness theorem `ForMathlib/TestsWeakCompact`.
  -- (2) Given a convex closed set with `c` in its interior, one lifts `c` along the objective
  -- to the boundary of the augmented moment body in `Fin (m+1) → ℝ` and applies a
  -- separating-/supporting-hyperplane argument (`geometric_hahn_banach`/`Convex.exists_ge`);
  -- the hyperplane's normal supplies the multipliers `k`, and every maximizer is then forced
  -- onto the multiplier shape a.e. by the complementary-slackness of that hyperplane. Both the
  -- compactness input and the hyperplane-to-a.e.-shape bridge are missing, so no honest proof
  -- is available without `ForMathlib/TestsWeakCompact`.
  sorry

/-- **A test with prescribed sizes.** Given `m + 1` probability densities and a level
`0 < α < 1`, there is a test whose size against each of the first `m` distributions is
exactly `α` and whose power against the last strictly exceeds `α` — unless the last
density is a linear combination of the others almost everywhere, in which case no such
test can exist. -/
theorem exists_test_with_prescribed_sizes {m : ℕ}
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the `m+1` distributions, given as probability measures
    (P : Fin (m + 1) → Measure 𝓧) [∀ i, IsProbabilityMeasure (P i)]
    -- USER-INPUT: their densities with respect to `μ`
    (p : Fin (m + 1) → 𝓧 → ℝ) (hp : ∀ i, HasDensity μ (p i) (P i))
    -- USER-INPUT: nondegenerate level; at `α ∈ {0,1}` the strict inequality fails
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (∃ k : Fin m → ℝ, ∀ᵐ x ∂μ, p (Fin.last m) x = ∑ i, k i * p i.castSucc x) ∨
      ∃ φ, IsCriticalFn φ ∧ (∀ i : Fin m, powerAgainst (P i.castSucc) φ = α) ∧
        α < powerAgainst (P (Fin.last m)) φ := by
  -- OBSTRUCTION (deep debt). This is the applied form of the inner-point clause. The vector
  -- `c ≡ α` is an inner point of the moment set precisely when the last density is NOT an a.e.
  -- linear combination of the others (the excluded left disjunct); in that case one invokes
  -- `exists_multipliers_of_max` to obtain the multiplier test that maximizes the power against
  -- `P_{m+1}`, and strict unbiasedness upgrades `α ≤` to `α <`. This routes entirely through
  -- `exists_multipliers_of_max`, hence inherits its dependency on the open weak-compactness
  -- theorem `ForMathlib/TestsWeakCompact` and the supporting-hyperplane argument. No honest
  -- proof is available without them.
  sorry

/-- **Lagrangian sufficiency.** Abstract form of the multiplier argument, on an arbitrary
space `U`: a point satisfying the side conditions which maximizes the Lagrangian
`F_{m+1} - ∑ kᵢFᵢ` over *all* of `U`, for some multipliers `k`, maximizes `F_{m+1}` over
the points satisfying the side conditions.

Applied with `U` the class of critical functions and `Fᵢ(φ) = ∫ φ fᵢ dμ`, this is exactly
the sufficiency half of the generalized lemma; in practice one maximizes for arbitrary
`k` and then chooses `k` to meet the side conditions. -/
theorem isMax_of_lagrangian {U : Type*} {m : ℕ}
    -- USER-INPUT: the objective (last index) and the `m` constrained functionals
    (F : Fin (m + 1) → U → ℝ)
    -- USER-INPUT: the prescribed values of the side conditions
    (c : Fin m → ℝ)
    -- USER-INPUT: the multipliers, a free choice
    (k : Fin m → ℝ) {u₀ : U}
    -- USER-INPUT: the candidate satisfies the side conditions
    (hu₀ : ∀ i, F i.castSucc u₀ = c i)
    -- USER-INPUT: the candidate maximizes the Lagrangian over the *whole* space
    (hlag : ∀ u, F (Fin.last m) u - ∑ i, k i * F i.castSucc u ≤
      F (Fin.last m) u₀ - ∑ i, k i * F i.castSucc u₀) :
    ∀ u, (∀ i, F i.castSucc u = c i) → F (Fin.last m) u ≤ F (Fin.last m) u₀ := by
  intro u hu
  have hsum : ∑ i, k i * F i.castSucc u = ∑ i, k i * F i.castSucc u₀ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, hu₀ i]
  have hl := hlag u
  linarith [hl, hsum]

end StatLean.HypothesisTesting
