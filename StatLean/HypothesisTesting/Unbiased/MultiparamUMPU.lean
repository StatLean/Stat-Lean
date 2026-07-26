import StatLean.HypothesisTesting.Unbiased.ConditionalExpFamily
import StatLean.HypothesisTesting.Unbiased.PowerContinuity
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# UMP unbiased tests for multiparameter exponential families

For a canonical `(U, T)` exponential family
`dP^{U,T}_{θ,ϑ}(u,t) = C(θ,ϑ)·exp(θu + ⟪ϑ,t⟫)·dν(u,t)` on a convex parameter set `Ω` that is
not contained in a proper linear subspace, the four testing problems about the parameter of
interest `θ` (the nuisance parameters `ϑ` being unspecified),

| null | alternative | test |
|---|---|---|
| `θ ≤ θ₀` | `θ > θ₀` | reject for large `u` |
| `θ ≤ θ₁` or `θ ≥ θ₂` | `θ₁ < θ < θ₂` | reject *inside* an interval in `u` |
| `θ₁ ≤ θ ≤ θ₂` | `θ < θ₁` or `θ > θ₂` | reject *outside* an interval in `u` |
| `θ = θ₀` | `θ ≠ θ₀` | reject *outside* an interval in `u` |

all admit UMP unbiased level-`α` tests, obtained by solving the corresponding one-parameter
problem **conditionally on `T = t`** and reinterpreting the result as a test of `(U, T)`.
The names `_inside` / `_outside` refer to the shape of the rejection region in `u`, not to
the shape of the null set.

**⚠ The four optimality theorems are FALSE in the frozen form transcribed here** — not
because the classical result fails, but because the transcription drops the source's
standing convention that the observation *is* the sufficient statistic. Explicit
counterexamples are formalized in the section
`ConditionalUMPUCounterexample` below, one per theorem; the diagnosis and the minimal repair
are stated there.

The constants are functions of `t`, determined by conditional size equations; the point-null
case carries in addition the conditional derivative condition
`E_{θ₀}[U·φ ∣ t] = α·E_{θ₀}[U ∣ t]`, which is what unbiasedness contributes and which may
not be dropped.

Contents:

* `condOneSidedTest`, `condInsideTest`, `condOutsideTest` — the three conditional critical
  functions, as functions of `(u, t)`;
* `isUMPU_conditional_oneSided` / `_inside` / `_outside` / `_point` — the four optimality
  theorems;
* `exists_measurable_conditional_constants` — measurable selection of the constants;
* `ConditionalUMPUCounterexample.not_isUMPU_conditional_*_counterexample` — the four
  refutations of the frozen optimality statements;
* `reparamUT`, `statTransformUT`, `inner_exponent_reparam`, `isCanonicalUT_reparam` — the
  reduction to canonical form for a parameter of interest `θ* = a₀θ + ⟪a, ϑ⟫`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.4 (UMP Unbiased Tests for Multiparameter Exponential Families),
Theorem 4.4.1 (the UMP unbiased tests `φ₁`–`φ₄` for a multiparameter exponential family).
(`TSH4 §4.4 Thm 4.4.1`.)

**Proof formalization notes.**
* "The parameter set is not contained in a linear space of dimension less than `k+1`" is
  transcribed as `Submodule.span ℝ Ω = ⊤` in the ambient `ℝ × Ξ`: for a `k`-dimensional
  nuisance space `Ξ` the ambient dimension is `k+1`, so spanning the ambient space is
  exactly the stated non-degeneracy. Together with convexity it is what makes each boundary
  slice `ω_j = {(θ,ϑ) ∈ Ω : θ = θ_j}` contain a `k`-dimensional rectangle, hence makes the
  family of laws of `T` on `ω_j` complete — the input that upgrades similarity to Neyman
  structure.
* The conditional size conditions are imposed for **almost every** `t` rather than for every
  `t`. This is the weaker hypothesis (hence the stronger theorem), it is all the averaging
  identity `integral_eq_integral_condDistrib` consumes, and it is what the measurable
  selection actually delivers, since the conditional distributions themselves are only
  determined up to null sets.
* The size conditions are imposed at *every* parameter of `Ω` whose coordinate of interest
  equals the relevant `θ_j`; by `condDistrib_eq_of_fst_eq` this is no stronger than
  imposing them at one such parameter, but stating it this way keeps the theorems
  independent of that derivation.
* The constants `C(·)`, `γ(·)` and their defining equations are *data*: they are supplied by
  the caller and their existence is the separate theorem
  `exists_measurable_conditional_constants`.
* Only members of `P` with parameter in `Ω` are evaluated: both the null and the alternative
  sets in the conclusions are subsets of `Ω`.

**Bibliographic comments.** The construction of UMP unbiased tests for multiparameter
exponential families by conditioning on the sufficient statistic for the nuisance parameters
is due to J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37) and J. Neyman ("Outline of a
theory of statistical estimation based on the classical theory of probability," *Phil.
Trans. R. Soc. A* **236** (1937), 333–380); the completeness theory underlying the step from
similar tests to tests with Neyman structure is due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340;
**15** (1955), 219–236).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 Ξ : Type*} [MeasurableSpace 𝓧]
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [MeasurableSpace Ξ]

/-! ## The conditional critical functions -/

/-- **One-sided conditional test**: on the surface `T = t`, reject when `u` exceeds the
critical value `C₀(t)`, randomize with probability `γ₀(t)` when `u = C₀(t)`.

Edge behaviour: the value at `u = C₀(t)` is `γ₀(t)` regardless of whether `γ₀ t ∈ [0,1]`;
the membership is a hypothesis of the theorems, not of the definition. -/
noncomputable def condOneSidedTest (C₀ γ₀ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if C₀ z.2 < z.1 then 1 else if z.1 = C₀ z.2 then γ₀ z.2 else 0

/-- **Inside-interval conditional test**: on the surface `T = t`, reject when `u` lies
strictly between `C₁(t)` and `C₂(t)`, randomizing at the two endpoints.

Edge behaviour: if `C₁ t = C₂ t` the lower randomization value `γ₁ t` takes precedence. -/
noncomputable def condInsideTest (C₁ C₂ γ₁ γ₂ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if C₁ z.2 < z.1 ∧ z.1 < C₂ z.2 then 1
    else if z.1 = C₁ z.2 then γ₁ z.2
    else if z.1 = C₂ z.2 then γ₂ z.2 else 0

/-- **Outside-interval conditional test**: on the surface `T = t`, reject when `u` lies
outside `[C₁(t), C₂(t)]`, randomizing at the two endpoints.

Edge behaviour: if `C₁ t = C₂ t` the lower randomization value `γ₁ t` takes precedence. -/
noncomputable def condOutsideTest (C₁ C₂ γ₁ γ₂ : Ξ → ℝ) : ℝ × Ξ → ℝ :=
  fun z => if z.1 < C₁ z.2 ∨ C₂ z.2 < z.1 then 1
    else if z.1 = C₁ z.2 then γ₁ z.2
    else if z.1 = C₂ z.2 then γ₂ z.2 else 0

/-! ## ⚠ The four optimality statements are FALSE as stated: an explicit counterexample

`IsCanonicalUT P Ω U T ν C` constrains **only the law of the pair `(U, T)`**; it says nothing
about the rest of the sample space `𝓧`. `IsUMPU`, on the other hand, demands optimality
against *every* critical function on `𝓧`. So as soon as `𝓧` carries information about the
parameter of interest that `(U, T)` does not see, a test built from `(U, T)` alone loses.
Taking `U` and `T` **constant** makes `IsCanonicalUT` hold vacuously (with `ν` a Dirac mass
and `C ≡ 1`) while leaving `P` completely free, which is the counterexample below:

* `𝓧 = Bool`, `Ξ = ℝ`, `U ≡ 0`, `T ≡ 0`, `ν = δ₍₀,₀₎`, `C ≡ 1`, `Ω = univ`, `α = 1/2`;
* `P p =` the Dirac mass at `true` when `p` is in the alternative set, the fair coin
  otherwise;
* the conditional test with `C₀ ≡ 0` and boundary weight `γ₀ ≡ 1/2` is the **constant**
  `1/2`, and its conditional size is `1/2 = α` on every surface, so all hypotheses hold;
* but `ψ = 1{bit = true}` is a critical function, unbiased at level `1/2` (power `1/2` on the
  null set, power `1` on the alternative), and strictly beats the conditional test.

The construction is uniform in the alternative set, so the *same* family refutes all four
theorems (`_oneSided`, `_inside`, `_outside`, `_point`); the four refutations are
`not_isUMPU_conditional_oneSided_counterexample` and its siblings below.

**REPAIR.** The source (TSH4 §4.4 Thm 4.4.1) states the theorem for the model *of the
sufficient statistic*: there `𝓧` **is** the range of `(U, T)`. The minimal repair is either
to specialize `𝓧 = ℝ × Ξ` with `U = Prod.fst`, `T = Prod.snd`, or to add the hypothesis that
`(U, T)` is sufficient for `P` on `Ω` (and then transport optimality along the sufficiency
reduction). The repair is *not* applied here: public signatures are frozen for this pass.

Two further gaps would remain even after that repair, and are recorded at the theorems: the
boundary device needs the power functions to be continuous, which for exponential families
requires finite-dimensionality of `Ξ` (see the counterexample in
`PowerContinuity.continuous_power_expFamily`) and `Ω` inside the interior of the natural
parameter set; and the step from similarity to Neyman structure needs completeness of the
laws of `T` on each boundary slice, available in the repository only for
`EuclideanSpace ℝ (Fin s)` (`PointEstimation.Completeness.ExpFamily`).
-/

namespace ConditionalUMPUCounterexample

/-- Interest statistic of the counterexample: constant, hence carrying no information. -/
def cxU : Bool → ℝ := fun _ => 0

/-- Nuisance statistic of the counterexample: constant. -/
def cxT : Bool → ℝ := fun _ => 0

lemma measurable_cxU : Measurable cxU := measurable_const

lemma measurable_cxT : Measurable cxT := measurable_const

/-- The fair coin on `Bool`. -/
noncomputable def cxCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure cxCoin := by
  refine ⟨?_⟩
  simp only [cxCoin, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

lemma cxCoin_true : cxCoin {true} = 1 / 2 := by simp [cxCoin]

open Classical in
/-- The model: an auxiliary bit which is deterministically `true` on the alternative set `K`
and a fair coin elsewhere. The statistic `(U, T)` is blind to it. -/
noncomputable def cxP (K : Set (ℝ × ℝ)) : ℝ × ℝ → Measure Bool :=
  fun p => if p ∈ K then Measure.dirac true else cxCoin

instance cxP_isProbabilityMeasure (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    IsProbabilityMeasure (cxP K p) := by
  rw [cxP]; split <;> infer_instance

/-- The base measure of the counterexample: the Dirac mass at the only value `(U, T)`
takes. -/
noncomputable def cxν : Measure (ℝ × ℝ) := Measure.dirac (0, 0)

/-- The competitor: reject exactly when the auxiliary bit is `true`. -/
def cxψ : Bool → ℝ := fun b => if b then 1 else 0

/-- **The canonical form holds vacuously.** With a constant statistic the law of `(U, T)` is
a Dirac mass for every parameter, and the canonical density evaluates to `1` there. -/
theorem isCanonicalUT_cx (K : Set (ℝ × ℝ)) :
    IsCanonicalUT (cxP K) Set.univ cxU cxT cxν (fun _ => 1) := by
  intro p _
  have hmap : (cxP K p).map (fun x => (cxU x, cxT x)) = Measure.dirac ((0 : ℝ), (0 : ℝ)) := by
    simp only [cxU, cxT]
    rw [Measure.map_const, measure_univ, one_smul]
  have hae : (fun z : ℝ × ℝ => ENNReal.ofReal (1 * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ)))
      =ᵐ[Measure.dirac ((0 : ℝ), (0 : ℝ))] 1 := by
    rw [ae_dirac_eq]
    refine Filter.eventually_pure.mpr ?_
    simp
  rw [hmap, cxν, withDensity_congr_ae hae, withDensity_one]

/-- **The conditional size of any test is its value at the single atom.** The disintegration
identity `integral_eq_integral_condDistrib` computes the conditional size without identifying
the conditional distribution: the law of `T` is a Dirac mass, so the average of the
conditional sizes *is* the conditional size, and it equals the (constant) unconditional
power. -/
theorem condSize_cx (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) (ψ : ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (v : ℝ) (hv : ψ (0, 0) = v) :
    ∀ᵐ t ∂((cxP K p).map cxT),
      ∫ u, ψ (u, t) ∂(condDistrib cxU cxT (cxP K p) t) = v := by
  have hcxT : cxT = fun _ : Bool => (0 : ℝ) := rfl
  have hmapT : (cxP K p).map cxT = Measure.dirac (0 : ℝ) := by
    rw [hcxT, Measure.map_const, measure_univ, one_smul]
  have hdis := integral_eq_integral_condDistrib (P := cxP K) (U := cxU) (T := cxT) (p := p)
    (φ := ψ) measurable_cxU measurable_cxT hψ
    (by simp only [cxU, cxT]; exact integrable_const _)
  have hLHS : ∫ x, ψ (cxU x, cxT x) ∂(cxP K p) = v := by
    simp only [cxU, cxT, hv]
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hmapT] at hdis ⊢
  rw [integral_dirac] at hdis
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.mpr (hdis.symm.trans hLHS)

/-- On the alternative set the competitor has power `1`. -/
theorem power_cxψ_mem {K : Set (ℝ × ℝ)} {p : ℝ × ℝ} (h : p ∈ K) :
    power (cxP K) cxψ p = 1 := by
  have hP : cxP K p = Measure.dirac true := by simp only [cxP, if_pos h]
  rw [power, hP, integral_dirac]
  simp [cxψ]

/-- Off the alternative set the competitor has power `1/2`. -/
theorem power_cxψ_notMem {K : Set (ℝ × ℝ)} {p : ℝ × ℝ} (h : p ∉ K) :
    power (cxP K) cxψ p = 1 / 2 := by
  have hP : cxP K p = cxCoin := by simp only [cxP, if_neg h]
  have hint : Integrable cxψ cxCoin := Integrable.of_finite
  rw [power, hP, integral_fintype hint]
  simp only [Fintype.sum_bool, cxψ, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
    add_zero]
  rw [measureReal_def, cxCoin_true]
  norm_num

/-- A constant test has constant power. -/
theorem power_const_cx (K : Set (ℝ × ℝ)) (v : ℝ) (p : ℝ × ℝ) :
    power (cxP K) (fun _ => v) p = v := by
  rw [power, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- **The refutation engine.** In the counterexample family, a conditional test that is
constantly equal to the level `α < 1` cannot be UMP unbiased: the auxiliary-bit test is
unbiased and has power `1` on the alternative. -/
theorem not_isUMPU_cx {K Θ₀ Θ₁ : Set (ℝ × ℝ)} {α : ℝ} {φ : Bool → ℝ}
    (hα : α = 1 / 2) (hφc : ∀ x, φ x = α)
    (hnull : ∀ q ∈ Θ₀, q ∉ K) (halt : Θ₁ ⊆ K) {q₁ : ℝ × ℝ} (hq₁ : q₁ ∈ Θ₁) :
    ¬ IsUMPU (cxP K) Θ₀ Θ₁ α φ := by
  classical
  intro h
  have hψcrit : IsCriticalFn cxψ :=
    ⟨Measurable.of_discrete, fun b => by cases b <;> norm_num [cxψ]⟩
  have hψunb : IsUnbiasedTest (cxP K) Θ₀ Θ₁ α cxψ := by
    constructor
    · intro q hq
      rw [power_cxψ_notMem (hnull q hq)]
      linarith
    · intro q hq
      rw [power_cxψ_mem (halt hq)]
      linarith
  have hcmp := h.2.2 cxψ hψcrit hψunb q₁ hq₁
  rw [power_cxψ_mem (halt hq₁)] at hcmp
  have hpow : power (cxP K) φ q₁ = α := by
    have : φ = fun _ => α := funext hφc
    rw [this, power_const_cx]
  rw [hpow] at hcmp
  linarith

/-! ### The constants of the counterexample and the four refutations -/

/-- Threshold of the counterexample's conditional test. -/
def cxC₀ : ℝ → ℝ := fun _ => 0

/-- Boundary weight of the counterexample's conditional test. -/
noncomputable def cxγ₀ : ℝ → ℝ := fun _ => 1 / 2

lemma measurable_cxC₀ : Measurable cxC₀ := measurable_const

lemma measurable_cxγ₀ : Measurable cxγ₀ := measurable_const

lemma cxγ₀_mem (t : ℝ) : cxγ₀ t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num [cxγ₀]

lemma cxC₀_le (t : ℝ) : cxC₀ t ≤ cxC₀ t := le_rfl

private lemma measurableSet_cx_pos : MeasurableSet {z : ℝ × ℝ | (0 : ℝ) < z.1} :=
  measurableSet_lt measurable_const measurable_fst

private lemma measurableSet_cx_neg : MeasurableSet {z : ℝ × ℝ | z.1 < (0 : ℝ)} :=
  measurableSet_lt measurable_fst measurable_const

private lemma measurableSet_cx_eq : MeasurableSet {z : ℝ × ℝ | z.1 = (0 : ℝ)} :=
  measurableSet_eq_fun measurable_fst measurable_const

lemma measurable_cxOneSided : Measurable (condOneSidedTest cxC₀ cxγ₀) := by
  have h : condOneSidedTest cxC₀ cxγ₀
      = fun z : ℝ × ℝ => if (0 : ℝ) < z.1 then 1 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite measurableSet_cx_pos measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const measurable_const)

lemma measurable_cxInside : Measurable (condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀) := by
  have h : condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀
      = fun z : ℝ × ℝ => if (0 : ℝ) < z.1 ∧ z.1 < 0 then 1
        else if z.1 = 0 then 1 / 2 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite (measurableSet_cx_pos.inter measurableSet_cx_neg) measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const
      (Measurable.ite measurableSet_cx_eq measurable_const measurable_const))

lemma measurable_cxOutside : Measurable (condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀) := by
  have h : condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀
      = fun z : ℝ × ℝ => if z.1 < 0 ∨ (0 : ℝ) < z.1 then 1
        else if z.1 = 0 then 1 / 2 else if z.1 = 0 then 1 / 2 else 0 := rfl
  rw [h]
  exact Measurable.ite (measurableSet_cx_neg.union measurableSet_cx_pos) measurable_const
    (Measurable.ite measurableSet_cx_eq measurable_const
      (Measurable.ite measurableSet_cx_eq measurable_const measurable_const))

lemma cxOneSided_val : condOneSidedTest cxC₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condOneSidedTest, cxC₀, cxγ₀]

lemma cxInside_val : condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condInsideTest, cxC₀, cxγ₀]

lemma cxOutside_val : condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ ((0 : ℝ), (0 : ℝ)) = 1 / 2 := by
  norm_num [condOutsideTest, cxC₀, cxγ₀]

/-- **`isUMPU_conditional_oneSided` is false as stated.** Every hypothesis of that theorem is
satisfied by the counterexample family (with `θ₀ = 0`, `α = 1/2`, `Ω = univ`), yet the
conclusion fails. -/
theorem not_isUMPU_conditional_oneSided_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | 0 < p.1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | 0 < p.1} p).map cxT),
          ∫ u, condOneSidedTest cxC₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | 0 < p.1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | 0 < p.1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≤ 0}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) < p.1} (1 / 2)
          (fun x => condOneSidedTest cxC₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    ⟨(-1, 0), Set.mem_univ _, by norm_num⟩, ⟨(1, 0), Set.mem_univ _, by norm_num⟩,
    by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOneSided _ cxOneSided_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOneSided_val
  · simpa using not_lt.mpr hq.2

/-- **`isUMPU_conditional_inside` is false as stated**, by the same counterexample family
(here with `θ₁ = 0 < θ₂ = 1`, `α = 1/2`; the alternative set is `{0 < θ < 1}`). -/
theorem not_isUMPU_conditional_inside_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (0 : ℝ) < 1 ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (1 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 ∨ p.1 = 1 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} p).map cxT),
          ∫ u, condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≤ 0 ∨ 1 ≤ p.1}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) < p.1 ∧ p.1 < 1} (1 / 2)
          (fun x => condInsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    by norm_num, ⟨(-1, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(1, 0), Set.mem_univ _, by norm_num⟩, ⟨(0, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(2, 0), Set.mem_univ _, by norm_num⟩, by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxInside _ cxInside_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1 / 2, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxInside_val
  · rcases hq.2 with h | h
    · exact fun hmem => absurd hmem.1 (not_lt.mpr h)
    · exact fun hmem => absurd hmem.2 (not_lt.mpr h)

/-- **`isUMPU_conditional_outside` is false as stated**, by the same counterexample family
(here with `θ₁ = 0 < θ₂ = 1`, `α = 1/2`; the alternative set is `{θ < 0 ∨ 1 < θ}`). -/
theorem not_isUMPU_conditional_outside_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (0 : ℝ) < 1 ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 1) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (1 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 ∨ p.1 = 1 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1} p).map cxT),
          ∫ u, condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1} p) t) = 1 / 2) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | p.1 < 0 ∨ 1 < p.1})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | (0 : ℝ) ≤ p.1 ∧ p.1 ≤ 1}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 < 0 ∨ 1 < p.1} (1 / 2)
          (fun x => condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    by norm_num, ⟨(-1, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(1, 0), Set.mem_univ _, by norm_num⟩, ⟨(0, 0), Set.mem_univ _, by norm_num⟩,
    ⟨(2, 0), Set.mem_univ _, by norm_num⟩, by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOutside _ cxOutside_val, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (2, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOutside_val
  · rintro (h | h)
    · exact absurd hq.2.1 (not_le.mpr h)
    · exact absurd hq.2.2 (not_le.mpr h)

/-- **`isUMPU_conditional_point` is false as stated**, by the same counterexample family
(here `θ₀ = 0`, `α = 1/2`); note that the conditional derivative condition `hderiv` also
holds, both sides being `0` because the interest statistic is constant `0`. -/
theorem not_isUMPU_conditional_point_counterexample :
    Measurable cxU ∧ Measurable cxT ∧
      IsCanonicalUT (cxP {p : ℝ × ℝ | p.1 ≠ 0}) Set.univ cxU cxT cxν (fun _ => 1) ∧
      Convex ℝ (Set.univ : Set (ℝ × ℝ)) ∧
      Submodule.span ℝ (Set.univ : Set (ℝ × ℝ)) = ⊤ ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 < 0) ∧
      (∃ p ∈ (Set.univ : Set (ℝ × ℝ)), (0 : ℝ) < p.1) ∧
      (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧
      Measurable cxC₀ ∧ Measurable cxγ₀ ∧ (∀ t, cxγ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, cxC₀ t ≤ cxC₀ t) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
          ∫ u, condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
            ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t) = 1 / 2) ∧
      (∀ p ∈ (Set.univ : Set (ℝ × ℝ)), p.1 = 0 →
        ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
          ∫ u, u * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
              ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)
            = 1 / 2 * ∫ u, u ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)) ∧
      ¬ IsUMPU (cxP {p : ℝ × ℝ | p.1 ≠ 0})
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 = 0}
          {p ∈ (Set.univ : Set (ℝ × ℝ)) | p.1 ≠ 0} (1 / 2)
          (fun x => condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (cxU x, cxT x)) := by
  have hderiv : ∀ p : ℝ × ℝ, ∀ᵐ t ∂((cxP {p : ℝ × ℝ | p.1 ≠ 0} p).map cxT),
      ∫ u, u * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ (u, t)
          ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t)
        = 1 / 2 * ∫ u, u ∂(condDistrib cxU cxT (cxP {p : ℝ × ℝ | p.1 ≠ 0} p) t) := by
    intro p
    have h₁ := condSize_cx {p : ℝ × ℝ | p.1 ≠ 0} p
      (fun z => z.1 * condOutsideTest cxC₀ cxC₀ cxγ₀ cxγ₀ z)
      (measurable_fst.mul measurable_cxOutside) 0 (by simp)
    have h₂ := condSize_cx {p : ℝ × ℝ | p.1 ≠ 0} p (fun z => z.1) measurable_fst 0 rfl
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    rw [ht₁, ht₂, mul_zero]
  refine ⟨measurable_cxU, measurable_cxT, isCanonicalUT_cx _, convex_univ, by simp,
    ⟨(-1, 0), Set.mem_univ _, by norm_num⟩, ⟨(1, 0), Set.mem_univ _, by norm_num⟩,
    by norm_num, by norm_num,
    measurable_cxC₀, measurable_cxγ₀, cxγ₀_mem, cxC₀_le, fun p _ _ =>
      condSize_cx _ p _ measurable_cxOutside _ cxOutside_val, fun p _ _ => hderiv p, ?_⟩
  refine not_isUMPU_cx rfl (fun x => ?_) (fun q hq => ?_) (fun q hq => hq.2)
    (q₁ := (1, 0)) ⟨Set.mem_univ _, by norm_num⟩
  · simpa [cxU, cxT] using cxOutside_val
  · simpa using hq.2

end ConditionalUMPUCounterexample

/-! ## The four UMP unbiased tests -/

/-- **One-sided null.** For `H : θ ≤ θ₀` against `K : θ > θ₀`, the conditional one-sided test
with conditional size `α` on the boundary surface `θ = θ₀` is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_oneSided
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₀ γ₀ : Ξ → ℝ} {θ₀ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT: the parameter set reaches below and above the null value
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical value and randomization probability
    (hC₀ : Measurable C₀) (hγ₀ : Measurable γ₀)
    -- USER-INPUT: the randomization probability is a probability
    (hγ₀_mem : ∀ t, γ₀ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: conditional size `α` on the boundary surface `θ = θ₀`
    (hsize : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | p.1 ≤ θ₀} {p ∈ Ω | θ₀ < p.1} α
      (fun x => condOneSidedTest C₀ γ₀ (U x, T x)) := by
  -- FALSE AS STATED — refuted by the formalized counterexample
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_oneSided_counterexample`, which
  -- exhibits data satisfying *every* hypothesis above (with `θ₀ = 0`, `α = 1/2`, `Ω = univ`)
  -- and disproves the conclusion. Diagnosis: `IsCanonicalUT` constrains only the law of
  -- `(U, T)`, while `IsUMPU` demands optimality against every critical function on `𝓧`; with
  -- `U`, `T` constant the hypothesis holds vacuously and the auxiliary randomness of `𝓧` beats
  -- the conditional test. See the file's counterexample section for the diagnosis and the
  -- minimal repair (state the theorem for the model of the sufficient statistic, or assume
  -- `(U, T)` sufficient). Two further gaps survive the repair and are NOT addressed here:
  -- `PowerContinuity.isUMPU_of_isUMP_on_boundary` needs power continuity, which for
  -- exponential families is false without `[FiniteDimensional ℝ Ξ]` and `Ω ⊆ interior natSet`
  -- (see the counterexample in `continuous_power_expFamily`), and the similar ⟹ Neyman
  -- structure step needs completeness of the `T`-laws on the boundary slice, available in the
  -- repository (`PointEstimation.Completeness.ExpFamily.isCompleteStat_of_interior_nonempty`)
  -- only for `EuclideanSpace ℝ (Fin s)`. Both earlier cited blockers are now CLOSED:
  -- `ConditionalExpFamily.condDistrib_expFamily_of_isCanonicalUT` and
  -- `PowerContinuity.continuous_power_expFamily`.
  sorry

/-- **Null outside an interval.** For `H : θ ≤ θ₁ or θ ≥ θ₂` against `K : θ₁ < θ < θ₂`, the
conditional test rejecting *inside* an interval in `u`, with conditional size `α` on both
boundary surfaces `θ = θ₁` and `θ = θ₂`, is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_inside
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₁ θ₂ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT: the two endpoints are ordered
    (hθ : θ₁ < θ₂)
    -- USER-INPUT: the parameter set reaches below and above each endpoint
    (hΩ_lt₁ : ∃ p ∈ Ω, p.1 < θ₁) (hΩ_gt₁ : ∃ p ∈ Ω, θ₁ < p.1)
    (hΩ_lt₂ : ∃ p ∈ Ω, p.1 < θ₂) (hΩ_gt₂ : ∃ p ∈ Ω, θ₂ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size `α` on both boundary surfaces
    (hsize : ∀ p ∈ Ω, p.1 = θ₁ ∨ p.1 = θ₂ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condInsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | p.1 ≤ θ₁ ∨ θ₂ ≤ p.1} {p ∈ Ω | θ₁ < p.1 ∧ p.1 < θ₂} α
      (fun x => condInsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- FALSE AS STATED — refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_inside_counterexample`
  -- (`θ₁ = 0 < θ₂ = 1`, `α = 1/2`, `Ω = univ`), same diagnosis and same repair as
  -- `isUMPU_conditional_oneSided`.
  sorry

/-- **Interval null.** For `H : θ₁ ≤ θ ≤ θ₂` against `K : θ < θ₁ or θ > θ₂`, the conditional
test rejecting *outside* an interval in `u`, with conditional size `α` on both boundary
surfaces `θ = θ₁` and `θ = θ₂`, is UMP unbiased at level `α`. -/
theorem isUMPU_conditional_outside
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₁ θ₂ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT: the two endpoints are ordered
    (hθ : θ₁ < θ₂)
    -- USER-INPUT: the parameter set reaches below and above each endpoint
    (hΩ_lt₁ : ∃ p ∈ Ω, p.1 < θ₁) (hΩ_gt₁ : ∃ p ∈ Ω, θ₁ < p.1)
    (hΩ_lt₂ : ∃ p ∈ Ω, p.1 < θ₂) (hΩ_gt₂ : ∃ p ∈ Ω, θ₂ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size `α` on both boundary surfaces
    (hsize : ∀ p ∈ Ω, p.1 = θ₁ ∨ p.1 = θ₂ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α) :
    IsUMPU P {p ∈ Ω | θ₁ ≤ p.1 ∧ p.1 ≤ θ₂} {p ∈ Ω | p.1 < θ₁ ∨ θ₂ < p.1} α
      (fun x => condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- FALSE AS STATED — refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_outside_counterexample`
  -- (`θ₁ = 0 < θ₂ = 1`, `α = 1/2`, `Ω = univ`), same diagnosis and same repair as
  -- `isUMPU_conditional_oneSided`.
  sorry

/-- **Point null.** For `H : θ = θ₀` against `K : θ ≠ θ₀`, the conditional test rejecting
*outside* an interval in `u` is UMP unbiased at level `α`, provided its constants satisfy
**both** conditional conditions on the boundary surface `θ = θ₀`:

* the conditional size condition `E_{θ₀}[φ ∣ t] = α`, and
* the conditional derivative condition `E_{θ₀}[U·φ ∣ t] = α·E_{θ₀}[U ∣ t]`,

the second being the analytic content of unbiasedness (the power function of the conditional
problem has a minimum at `θ₀`). -/
theorem isUMPU_conditional_point
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {C₁ C₂ γ₁ γ₂ : Ξ → ℝ} {θ₀ α : ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the parameter set is convex
    (hΩ_convex : Convex ℝ Ω)
    -- USER-INPUT: the parameter set is not contained in a proper linear subspace
    (hΩ_span : Submodule.span ℝ Ω = ⊤)
    -- USER-INPUT: the parameter set reaches below and above the null value
    (hΩ_lt : ∃ p ∈ Ω, p.1 < θ₀) (hΩ_gt : ∃ p ∈ Ω, θ₀ < p.1)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: measurable selection of the critical values and randomization
    -- probabilities
    (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (hγ₁ : Measurable γ₁) (hγ₂ : Measurable γ₂)
    -- USER-INPUT: the randomization probabilities are probabilities
    (hγ₁_mem : ∀ t, γ₁ t ∈ Set.Icc (0 : ℝ) 1) (hγ₂_mem : ∀ t, γ₂ t ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the critical values are ordered
    (hC : ∀ t, C₁ t ≤ C₂ t)
    -- USER-INPUT: conditional size condition on the boundary surface `θ = θ₀`
    (hsize : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t) = α)
    -- USER-INPUT: conditional derivative (unbiasedness) condition on the same surface
    (hderiv : ∀ p ∈ Ω, p.1 = θ₀ → ∀ᵐ t ∂((P p).map T),
      ∫ u, u * condOutsideTest C₁ C₂ γ₁ γ₂ (u, t) ∂(condDistrib U T (P p) t)
        = α * ∫ u, u ∂(condDistrib U T (P p) t)) :
    IsUMPU P {p ∈ Ω | p.1 = θ₀} {p ∈ Ω | p.1 ≠ θ₀} α
      (fun x => condOutsideTest C₁ C₂ γ₁ γ₂ (U x, T x)) := by
  -- FALSE AS STATED — refuted by
  -- `ConditionalUMPUCounterexample.not_isUMPU_conditional_point_counterexample` (`θ₀ = 0`,
  -- `α = 1/2`, `Ω = univ`); there the conditional derivative condition `hderiv` also holds,
  -- both sides being `0` because the interest statistic is constant. Same diagnosis and same
  -- repair as `isUMPU_conditional_oneSided`.
  sorry

/-! ## Measurable selection of the conditional constants -/

/-- The conditional critical value at level `α`: the `(1−α)`-quantile of the distribution
function of `μ`. Explicit — this is what makes the selection measurable in the conditioning
variable, `t ↦ critC (κ t) α` being a quantile of a measurable family of CDFs. -/
private noncomputable def critC (μ : Measure ℝ) (α : ℝ) : ℝ := quantile (⇑(cdf μ)) (1 - α)

/-- The matching randomization weight: the fraction of the atom at `critC μ α` needed to make
the size exactly `α`. Division by zero returns `0`, which is precisely the correct value when
there is no atom (there the size is already exactly `α`). -/
private noncomputable def critGamma (μ : Measure ℝ) (α : ℝ) : ℝ :=
  (α - (μ {x : ℝ | critC μ α < x}).toReal) / (μ {x : ℝ | x = critC μ α}).toReal

/-- The `(1−α)`-sublevel set of a distribution function is nonempty (the CDF tends to `1`)
and bounded below (it tends to `0`), for `0 < α < 1`. -/
private lemma cdf_sublevel_nonempty_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    {y : ℝ | 1 - α ≤ cdf μ y}.Nonempty ∧ BddBelow {y : ℝ | 1 - α ≤ cdf μ y} := by
  constructor
  · obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt
      (show 1 - α < 1 by linarith)).exists
    exact ⟨y, le_of_lt hy⟩
  · obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp
      ((tendsto_cdf_atBot μ).eventually_lt_const (show (0 : ℝ) < 1 - α by linarith))
    refine ⟨b, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy
    by_contra hcon
    exact absurd (hb y (not_le.mp hcon).le) (not_lt.mpr hy)

/-- **Galois property of the conditional critical value.** `critC μ α ≤ x` iff the CDF has
already reached `1 − α` at `x`. This is what turns the measurability of `t ↦ cdf (κ t) x`
into the measurability of `t ↦ critC (κ t) α`. -/
private lemma critC_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (x : ℝ) : critC μ α ≤ x ↔ 1 - α ≤ cdf μ x :=
  quantile_le_iff (monotone_cdf (μ := μ)) (fun y => (cdf μ).right_continuous y)
    (cdf_sublevel_nonempty_bddBelow μ hα0 hα1).1 (cdf_sublevel_nonempty_bddBelow μ hα0 hα1).2

/-- **The explicit constants attain the level exactly.** The one-sided test with threshold
`critC μ α` and boundary weight `critGamma μ α` has size exactly `α`, and the weight is a
probability. Same computation as `QuantileFunction.exists_critical_constants`, carried out
for the *named* constants rather than existentially. -/
private lemma critical_constants_explicit (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ critGamma μ α ∧ critGamma μ α ≤ 1 ∧
      (μ {x : ℝ | critC μ α < x}).toReal
        + critGamma μ α * (μ {x : ℝ | x = critC μ α}).toReal = α := by
  have hmono : Monotone (⇑(cdf μ)) := monotone_cdf (μ := μ)
  set C := critC μ α with hCdef
  set L := Function.leftLim (⇑(cdf μ)) C with hLdef
  have hA : 1 - α ≤ cdf μ C := (critC_le_iff μ hα0 hα1 C).mp le_rfl
  have hB : ∀ y, y < C → cdf μ y < 1 - α := by
    intro y hy
    by_contra h
    exact absurd ((critC_le_iff μ hα0 hα1 y).mpr (not_lt.mp h)) (not_le.mpr hy)
  have hLle : L ≤ cdf μ C := Monotone.leftLim_le hmono le_rfl
  have hLbound : L ≤ 1 - α := by
    have htend : Filter.Tendsto (⇑(cdf μ)) (nhdsWithin C (Set.Iio C)) (nhds L) :=
      hmono.tendsto_leftLim C
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hB y hy).le
  have hg : (μ {x : ℝ | C < x}).toReal = 1 - cdf μ C := by
    have hIoi := (cdf μ).measure_Ioi (tendsto_cdf_atTop μ) C
    rw [measure_cdf] at hIoi
    have hset : {x : ℝ | C < x} = Set.Ioi C := rfl
    rw [hset, hIoi, ENNReal.toReal_ofReal (by linarith [cdf_le_one (μ := μ) C])]
  have hj : (μ {x : ℝ | x = C}).toReal = cdf μ C - L := by
    have hsing := (cdf μ).measure_singleton C
    rw [measure_cdf] at hsing
    have hset : {x : ℝ | x = C} = {C} := by ext x; simp
    rw [hset, hsing, ENNReal.toReal_ofReal (by linarith [hLle])]
  have hgle : 1 - cdf μ C ≤ α := by linarith [hA]
  have hgnn : 0 ≤ 1 - cdf μ C := by linarith [cdf_le_one (μ := μ) C]
  have hjnn : 0 ≤ cdf μ C - L := by linarith [hLle]
  have hαle : α ≤ (1 - cdf μ C) + (cdf μ C - L) := by linarith [hLbound]
  have hγ : critGamma μ α = (α - (1 - cdf μ C)) / (cdf μ C - L) := by
    rw [critGamma, hg, hj]
  rcases eq_or_lt_of_le hjnn with hj0 | hjpos
  · -- no atom: the size is already exactly `α` and the weight is `0`
    have hval : (1 - cdf μ C) = α := le_antisymm hgle (by linarith [hαle, hj0])
    have hγ0 : critGamma μ α = 0 := by rw [hγ, ← hj0, div_zero]
    refine ⟨by rw [hγ0], by rw [hγ0]; norm_num, ?_⟩
    rw [hg, hj, hγ0, hval]
    ring
  · refine ⟨by rw [hγ]; exact div_nonneg (by linarith [hgle]) (le_of_lt hjpos), ?_, ?_⟩
    · rw [hγ, div_le_one hjpos]; linarith [hαle]
    · rw [hg, hj, hγ, div_mul_cancel₀ _ (ne_of_gt hjpos)]; ring

/-- The distribution function of a Markov kernel is measurable in the conditioning variable,
for each fixed argument. -/
private lemma measurable_cdf_kernel (κ : Kernel Ξ ℝ) [IsMarkovKernel κ] (x : ℝ) :
    Measurable fun t => cdf (κ t) x := by
  simp only [cdf_eq_real, measureReal_def]
  exact ENNReal.measurable_toReal.comp (κ.measurable_coe measurableSet_Iic)

/-- The one-sided conditional test integrates to `size = tail + weight · atom`. -/
private lemma integral_condOneSidedTest (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C₀ γ₀ : Ξ → ℝ) (t : Ξ) :
    ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂μ
      = (μ {x : ℝ | C₀ t < x}).toReal + γ₀ t * (μ {x : ℝ | x = C₀ t}).toReal := by
  have hs₁ : MeasurableSet {x : ℝ | C₀ t < x} := measurableSet_Ioi
  have hs₂ : MeasurableSet {x : ℝ | x = C₀ t} := by
    have : {x : ℝ | x = C₀ t} = {C₀ t} := by ext x; simp
    rw [this]; exact measurableSet_singleton _
  have hfun : (fun u => condOneSidedTest C₀ γ₀ (u, t))
      = fun u => ({x : ℝ | C₀ t < x}.indicator (fun _ => (1 : ℝ)) u
          + γ₀ t * {x : ℝ | x = C₀ t}.indicator (fun _ => (1 : ℝ)) u) := by
    funext u
    simp only [condOneSidedTest]
    by_cases h1 : C₀ t < u
    · have hm1 : u ∈ {x : ℝ | C₀ t < x} := h1
      have hn2 : u ∉ {x : ℝ | x = C₀ t} := by
        simp only [Set.mem_setOf_eq]; linarith
      rw [if_pos h1, Set.indicator_of_mem hm1, Set.indicator_of_notMem hn2]
      ring
    · have hn1 : u ∉ {x : ℝ | C₀ t < x} := h1
      rw [if_neg h1, Set.indicator_of_notMem hn1]
      by_cases h2 : u = C₀ t
      · have hm2 : u ∈ {x : ℝ | x = C₀ t} := h2
        rw [if_pos h2, Set.indicator_of_mem hm2]
        ring
      · have hn2 : u ∉ {x : ℝ | x = C₀ t} := h2
        rw [if_neg h2, Set.indicator_of_notMem hn2]
        ring
  rw [hfun, integral_add ((integrable_const (1 : ℝ)).indicator hs₁)
    (((integrable_const (1 : ℝ)).indicator hs₂).const_mul _), integral_const_mul,
    integral_indicator_const _ hs₁, integral_indicator_const _ hs₂]
  simp [measureReal_def]

/-- **Existence of measurable conditional constants (one-sided case).**

There is a measurable choice of critical value `C₀(t)` and randomization probability `γ₀(t)`
achieving conditional size `α` on the surface `T = t`, for almost every `t`.

Construction: with `F_t(u) = P_{θ₀}{U ≤ u ∣ t}` the conditional distribution function (the
`cdf` of the Markov kernel `condDistrib U T (P p₀)` evaluated at `t`), the size equation
reads `[1 − F_t(C)] + γ·[F_t(C) − F_t(C−)] = α`, solved by the conditional quantile
`C₀(t) = inf {u | F_t(u) ≥ 1 − α}` (`critC`) together with the matching interpolation weight
`γ₀(t) = (α − P_t(C₀(t), ∞)) / P_t{C₀(t)}` (`critGamma`; the junk value `x / 0 = 0` is the
correct one, since with no atom the tail already has mass exactly `α`).

The two measurability steps are, in this proof, both cheap, and *no* joint measurability of
`(u, t) ↦ F_t(u)` is needed:

* `C₀` is measurable because its sublevel sets are superlevel sets of a fixed-argument CDF:
  `C₀(t) ≤ x ↔ 1 − α ≤ F_t(x)` (the Galois property `quantile_le_iff`, here `critC_le_iff`),
  and `t ↦ F_t(x) = (κ t (Iic x)).toReal` is measurable for each fixed `x` because `κ` is a
  kernel;
* the tail and the atom at the *varying* threshold `C₀(t)` are measurable because
  `{(t,u) | C₀(t) < u}` and `{(t,u) | u = C₀(t)}` are measurable subsets of the product and
  a kernel evaluated on the sections of a measurable set is measurable
  (`Kernel.measurable_kernel_prodMk_left`).

The conclusion is in fact obtained for *every* `t`, not just almost every `t`: the
conditional laws are probability measures for every `t` since `condDistrib` is a Markov
kernel. Neither the exponential-family form `hUT` nor the measurability of `U` and `T` is
used; they are kept in the signature as stated. -/
theorem exists_measurable_conditional_constants
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {α : ℝ} {p₀ : ℝ × Ξ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the reference parameter belongs to the parameter set
    (hp₀ : p₀ ∈ Ω)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C₀ γ₀ : Ξ → ℝ, Measurable C₀ ∧ Measurable γ₀ ∧
      (∀ t, γ₀ t ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ t ∂((P p₀).map T),
        ∫ u, condOneSidedTest C₀ γ₀ (u, t) ∂(condDistrib U T (P p₀) t) = α := by
  classical
  set κ : Kernel Ξ ℝ := condDistrib U T (P p₀) with hκ
  -- the critical value is measurable because its sublevel sets are CDF superlevel sets
  have hC₀m : Measurable fun t => critC (κ t) α := by
    refine measurable_of_Iic fun x => ?_
    have hset : (fun t => critC (κ t) α) ⁻¹' Set.Iic x = {t | 1 - α ≤ cdf (κ t) x} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      exact critC_le_iff (κ t) hα₀ hα₁ x
    rw [hset]
    exact measurableSet_le measurable_const (measurable_cdf_kernel κ x)
  -- the tail and the atom at a *varying* threshold are measurable, by the joint
  -- measurability of a kernel on sections of a measurable set of the product
  have htail : Measurable fun t => (κ t {x : ℝ | critC (κ t) α < x}).toReal :=
    ENNReal.measurable_toReal.comp (Kernel.measurable_kernel_prodMk_left
      (measurableSet_lt (hC₀m.comp measurable_fst) measurable_snd))
  have hatom : Measurable fun t => (κ t {x : ℝ | x = critC (κ t) α}).toReal :=
    ENNReal.measurable_toReal.comp (Kernel.measurable_kernel_prodMk_left
      (measurableSet_eq_fun measurable_snd (hC₀m.comp measurable_fst)))
  refine ⟨fun t => critC (κ t) α, fun t => critGamma (κ t) α, hC₀m, ?_, ?_, ?_⟩
  · simp only [critGamma]
    exact (measurable_const.sub htail).div hatom
  · exact fun t => ⟨(critical_constants_explicit (κ t) hα₀ hα₁).1,
      (critical_constants_explicit (κ t) hα₀ hα₁).2.1⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [integral_condOneSidedTest (κ t) _ _ t]
    exact (critical_constants_explicit (κ t) hα₀ hα₁).2.2

/-! ## Reduction to canonical form -/

/-- Reparametrization of the parameter of interest: `(θ, ϑ) ↦ (a₀θ + ⟪a, ϑ⟫, ϑ)`. -/
def reparamUT (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun p => (a₀ * p.1 + ⟪a, p.2⟫_ℝ, p.2)

/-- Inverse reparametrization `(θ*, ϑ) ↦ ((θ* − ⟪a, ϑ⟫)/a₀, ϑ)`; for `a₀ = 0` it degenerates
to the junk value `0` in the first coordinate. -/
noncomputable def reparamUTInv (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun q => ((q.1 - ⟪a, q.2⟫_ℝ) / a₀, q.2)

/-- The matching transformation of the sufficient statistic: `(u, t) ↦ (u/a₀, t − (u/a₀)·a)`;
for `a₀ = 0` it degenerates to the junk value `(0, t)`. -/
noncomputable def statTransformUT (a₀ : ℝ) (a : Ξ) : ℝ × Ξ → ℝ × Ξ :=
  fun z => (z.1 / a₀, z.2 - (z.1 / a₀) • a)

/-- **The exponent identity behind the reduction to canonical form.**

`θ·u + ⟪ϑ, t⟫ = (a₀θ + ⟪a, ϑ⟫)·(u/a₀) + ⟪ϑ, t − (u/a₀)·a⟫`: the canonical exponent is
unchanged when the parameter of interest is replaced by the linear combination
`θ* = a₀θ + ⟪a, ϑ⟫` and the statistic by `U* = U/a₀`, `T* = T − (U/a₀)·a`. -/
theorem inner_exponent_reparam {a₀ : ℝ} (a : Ξ) (θ : ℝ) (ϑ : Ξ) (u : ℝ) (t : Ξ)
    -- USER-INPUT: the coefficient of the parameter of interest is nonzero
    (ha₀ : a₀ ≠ 0) :
    θ * u + ⟪ϑ, t⟫_ℝ
      = (a₀ * θ + ⟪a, ϑ⟫_ℝ) * (u / a₀) + ⟪ϑ, t - (u / a₀) • a⟫_ℝ := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_comm a ϑ]
  field_simp
  ring

/-- Push-forward of a `withDensity` along a measurable map whose density is a pull-back:
if the density on the source is `D ∘ S`, then `S`-image of the tilt is the `D`-tilt of the
`S`-image. No injectivity of `S` is needed — only that the source density factors through
`S`. Change-of-variables for `withDensity`, proved set by set with `setLIntegral_map`. -/
private lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {S : α → β} {D : β → ℝ≥0∞} (hS : Measurable S) (hD : Measurable D) :
    (μ.withDensity fun z => D (S z)).map S = (μ.map S).withDensity D := by
  ext B hB
  rw [Measure.map_apply hS hB, withDensity_apply _ (hS hB), withDensity_apply _ hB,
    setLIntegral_map hB hD hS]

/-- Measurability of the canonical exponential density on `ℝ × Ξ` (local copy of the
namesake in `ConditionalExpFamily`, which is `private` to that file). -/
private lemma measurable_canonicalDensity' [OpensMeasurableSpace Ξ] (c θ : ℝ) (ϑ : Ξ) :
    Measurable fun z : ℝ × Ξ => ENNReal.ofReal (c * Real.exp (θ * z.1 + ⟪ϑ, z.2⟫_ℝ)) := by
  have h : Measurable fun z : ℝ × Ξ => ⟪ϑ, z.2⟫_ℝ :=
    ((innerSL ℝ ϑ).continuous.measurable).comp measurable_snd
  exact (((measurable_const.mul measurable_fst).add h).exp.const_mul c).ennreal_ofReal

/-- **Reduction to canonical form.**

A canonical `(U, T)` family is again canonical after the change of parameter of interest
`θ* = a₀θ + ⟪a, ϑ⟫` (`a₀ ≠ 0`), with statistic `U* = U/a₀`, `T* = T − (U/a₀)·a` and base
measure the image of `ν` under the same transformation. Consequently the four optimality
theorems above apply verbatim to hypotheses about `θ*`.

The proof is the change of variables `map_withDensity_comp` along `S = statTransformUT a₀ a`
— whose defining property is exactly `inner_exponent_reparam`, i.e. the reparametrized
density pulled back along `S` is the original density — together with `map_map` to move `S`
past the statistic. The measurability of `(U, T)` is *not* a hypothesis, and is not needed:
if it fails, the left-hand side is the zero measure by `Measure.map_of_not_aemeasurable`, and
so is the right-hand side, because `S` has a measurable left inverse `(v,s) ↦ (a₀v, s + v·a)`
(so `S ∘ (U,T)` is no more measurable than `(U,T)`) and the change of variables identifies
the right-hand side with the `S`-image of `(P p).map (U,T) = 0`.

**FLAGGED SIGNATURE AMENDMENT.** The instances `[BorelSpace Ξ]` and
`[SecondCountableTopology Ξ]` were *added*. They are what makes the shear
`S : (u,t) ↦ (u/a₀, t − (u/a₀)·a)` — a continuous map `ℝ × Ξ → ℝ × Ξ` — measurable: the
frozen `[MeasurableSpace Ξ]` is unrelated to the topology of `Ξ`, and even with
`[BorelSpace Ξ]` alone the product σ-algebra of `ℝ × Ξ` need not contain the Borel sets of
the product topology, which is what second countability supplies (`Prod.borelSpace`). Both
hold for every intended instantiation `Ξ = EuclideanSpace ℝ (Fin k)`. Nothing else in the
statement changes. -/
theorem isCanonicalUT_reparam
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {a₀ : ℝ} {a : Ξ}
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of `Ξ` is the Borel one and `Ξ` is second
    -- countable, so that the continuous shear `statTransformUT a₀ a` is measurable
    [BorelSpace Ξ] [SecondCountableTopology Ξ]
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the coefficient of the parameter of interest is nonzero
    (ha₀ : a₀ ≠ 0) :
    IsCanonicalUT (fun q => P (reparamUTInv a₀ a q)) (reparamUT a₀ a '' Ω)
      (fun x => U x / a₀) (fun x => T x - (U x / a₀) • a)
      (ν.map (statTransformUT a₀ a)) (fun q => C (reparamUTInv a₀ a q)) := by
  -- the shear and its left inverse are continuous, hence measurable
  have hScont : Continuous (statTransformUT a₀ a) := by
    unfold statTransformUT; fun_prop
  have hS : Measurable (statTransformUT a₀ a) := hScont.measurable
  have hS' : Measurable fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a) :=
    (by fun_prop : Continuous fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)).measurable
  have hSS' : ∀ z : ℝ × Ξ,
      (fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)) (statTransformUT a₀ a z) = z := by
    intro z
    have h1 : a₀ * (z.1 / a₀) = z.1 := by field_simp
    have h2 : z.2 - (z.1 / a₀) • a + (z.1 / a₀) • a = z.2 := by abel
    simp only [statTransformUT, h1, h2]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hinv : reparamUTInv a₀ a (reparamUT a₀ a p) = p := by
    have h1 : (a₀ * p.1 + ⟪a, p.2⟫_ℝ - ⟪a, p.2⟫_ℝ) / a₀ = p.1 := by
      rw [add_sub_cancel_right]; field_simp
    simp only [reparamUTInv, reparamUT, h1]
  simp only [hinv]
  -- the reparametrized density pulled back along the shear is the original density
  have hD : Measurable fun z : ℝ × Ξ => ENNReal.ofReal (C p *
      Real.exp ((reparamUT a₀ a p).1 * z.1 + ⟪(reparamUT a₀ a p).2, z.2⟫_ℝ)) :=
    measurable_canonicalDensity' _ _ _
  have hdens : ∀ z : ℝ × Ξ, ENNReal.ofReal (C p *
      Real.exp ((reparamUT a₀ a p).1 * (statTransformUT a₀ a z).1
        + ⟪(reparamUT a₀ a p).2, (statTransformUT a₀ a z).2⟫_ℝ))
      = ENNReal.ofReal (C p * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ)) := by
    intro z
    simp only [reparamUT, statTransformUT]
    rw [← inner_exponent_reparam a p.1 p.2 z.1 z.2 ha₀]
  have hkey : (ν.map (statTransformUT a₀ a)).withDensity (fun z => ENNReal.ofReal (C p *
        Real.exp ((reparamUT a₀ a p).1 * z.1 + ⟪(reparamUT a₀ a p).2, z.2⟫_ℝ)))
      = ((P p).map fun x => (U x, T x)).map (statTransformUT a₀ a) := by
    rw [hUT p hp, ← map_withDensity_comp ν hS hD]
    congr 1
    congr 1
    funext z
    exact hdens z
  rw [hkey]
  -- move the shear past the statistic; both sides vanish if the statistic is not measurable
  by_cases hf : AEMeasurable (fun x => (U x, T x)) (P p)
  · rw [AEMeasurable.map_map_of_aemeasurable hS.aemeasurable hf]
    rfl
  · have hf' : ¬ AEMeasurable (fun x => (U x / a₀, T x - (U x / a₀) • a)) (P p) := by
      intro hc
      have hcomp : ((fun w : ℝ × Ξ => (a₀ * w.1, w.2 + w.1 • a)) ∘
          fun x => (U x / a₀, T x - (U x / a₀) • a)) = fun x => (U x, T x) := by
        funext x
        exact hSS' (U x, T x)
      have := hS'.comp_aemeasurable hc
      rw [hcomp] at this
      exact hf this
    rw [Measure.map_of_not_aemeasurable hf, Measure.map_of_not_aemeasurable hf']
    simp

end StatLean.HypothesisTesting
