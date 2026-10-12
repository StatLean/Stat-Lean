import StatLean.ConcentrationInequalities.EfronStein.Defs
import StatLean.ConcentrationInequalities.ForMathlib.PiMix

/-!
# Block averages and the variance recursion behind the Efron–Stein inequality

This file builds the machinery for the tensorization of the variance: for a block
`S : Finset ι` of coordinates, `avgOn S f` averages `f` over the coordinates in `S` and
`varOn S f` is the variance of `f` in those coordinates, both read as functions of the
remaining coordinates. The two facts that drive the induction are

* `avgOn_insert` — averaging over `insert i S` is averaging over `S` followed by
  `condMeanAt i`, so blocks grow one coordinate at a time; and
* `integral_varOn_insert` — the corresponding **law of total variance**, which says
  that growing the block by `i` adds exactly the variance of the block average in the
  `i`-th coordinate, and is pure algebra once `avgOn_insert` is available.

The file ends with `variance_le_efronSteinBound`, the Efron–Stein inequality itself.

**Reference.** Stéphane Boucheron, Gábor Lugosi and Pascal Massart, *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, 2013
(ISBN 978-0-19-953525-5), §3.1. The book runs the argument through the Doob martingale of
the natural filtration; this file realizes the same variance decomposition and Jensen
step as a block recursion on the canonical product space.

**Proof formalization notes.** `avgOn S f x` integrates the *whole* product measure but
only uses the `S`-coordinates of the integrating variable (see `ForMathlib/PiMix`), which
keeps all objects in one type. Statements about `avgOn` are almost-everywhere statements,
not pointwise ones: for a fixed `x` the slice `z ↦ f (mixAt S x z)` need not be
integrable, only for almost every `x`. `memLp_avgOn` is the contraction property of the
averaging operator, proved exactly as `memLp_condMeanAt`: Jensen dominates
`(avgOn S f)²` by `avgOn S (f²)`, whose integral is `∫ f²` by `integral_integral_mixAt`.
For the suffix block $S = \{i+1,\ldots,n\}$, `avgOn S f` is $\mathbf{E}_i Z$;
`avgOn_condMeanAt_insert` realizes equation (3.1), `integral_varOn_insert` supplies the
variance-increment decomposition, and `integral_avgOn_sub_condMeanAt_sq_le` is the Jensen
step.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝓧 : ι → Type*}
  [∀ i, MeasurableSpace (𝓧 i)] (μ : ∀ i, Measure (𝓧 i))
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **Block average.** `avgOn S f` averages `f` over the coordinates in `S`, leaving the
coordinates outside `S` fixed. -/
noncomputable def avgOn (S : Finset ι) (f : (Π j, 𝓧 j) → ℝ) (x : Π j, 𝓧 j) : ℝ :=
  ∫ z, f (mixAt S x z) ∂(Measure.pi μ)

variable {f : (Π j, 𝓧 j) → ℝ}

@[simp] theorem avgOn_empty : avgOn μ ∅ f = f := by
  funext x; simp [avgOn]

omit [∀ i, IsProbabilityMeasure (μ i)] in
@[simp] theorem avgOn_univ (x : Π j, 𝓧 j) :
    avgOn μ Finset.univ f x = ∫ z, f z ∂(Measure.pi μ) := by
  simp [avgOn]

/-- A block average is strongly measurable in the remaining coordinates. -/
theorem stronglyMeasurable_avgOn (S : Finset ι) (hfm : Measurable f) :
    StronglyMeasurable (avgOn μ S f) :=
  ((hfm.comp (measurable_mixAt S)).stronglyMeasurable).integral_prod_right'

/-- Averaging a block does not change the expectation. -/
theorem integral_avgOn (S : Finset ι) (hf : Integrable f (Measure.pi μ)) :
    ∫ x, avgOn μ S f x ∂(Measure.pi μ) = ∫ x, f x ∂(Measure.pi μ) :=
  integral_integral_mixAt μ S hf

/-- Almost every block slice of an integrable function is integrable. -/
theorem ae_integrable_mixAt (S : Finset ι) (hf : Integrable f (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), Integrable (fun z => f (mixAt S x z)) (Measure.pi μ) :=
  ((measurePreserving_mixAt μ S).integrable_comp_of_integrable hf).prod_right_ae

/-- **The block average is an L² contraction.** -/
theorem memLp_avgOn (S : Finset ι) (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    MemLp (avgOn μ S f) 2 (Measure.pi μ) := by
  have hsm := stronglyMeasurable_avgOn μ S hfm
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => f (mixAt S p.1 p.2) ^ 2)
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    (measurePreserving_mixAt μ S).integrable_comp_of_integrable hf.integrable_sq
  have hdom : Integrable (fun x => ∫ z, f (mixAt S x z) ^ 2 ∂(Measure.pi μ))
      (Measure.pi μ) := hcomp.integral_prod_left
  refine (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 ?_
  refine hdom.mono' ((hsm.measurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_memLp_mixAt μ S hfm hf] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_integral_le_integral_sq hx

omit [Fintype ι] [∀ i, MeasurableSpace (𝓧 i)] [∀ i, IsProbabilityMeasure (μ i)] in
/-- Mixing over `S` after updating a coordinate `i ∉ S` is the same as updating that
coordinate after mixing over `insert i S`. This is the combinatorial heart of
`avgOn_insert`. -/
theorem mixAt_update_of_notMem (S : Finset ι) {i : ι} (hi : i ∉ S)
    (x z : Π j, 𝓧 j) (y : 𝓧 i) :
    mixAt S (Function.update x i y) z
      = Function.update (mixAt (insert i S) x z) i y := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [mixAt, hi]
  · by_cases hjS : j ∈ S
    · simp [mixAt, hjS, Finset.mem_insert_of_mem hjS, Function.update_of_ne hj]
    · simp [mixAt, hjS, hj, Finset.mem_insert]

omit [Fintype ι] [∀ i, MeasurableSpace (𝓧 i)] [∀ i, IsProbabilityMeasure (μ i)] in
/-- Mixing over `insert i S` at an updated `i`-th coordinate of the *integrating*
variable. -/
theorem mixAt_insert_update (S : Finset ι) {i : ι}
    (x z : Π j, 𝓧 j) (y : 𝓧 i) :
    mixAt (insert i S) x (Function.update z i y)
      = Function.update (mixAt (insert i S) x z) i y := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [mixAt]
  · by_cases hjS : j ∈ insert i S
    · simp [mixAt, hjS, Function.update_of_ne hj]
    · simp [mixAt, hjS, Function.update_of_ne hj]

/-- Resampling the `i`-th coordinate of the integrating variable is measure preserving in
the order needed by Fubini. -/
theorem measurePreserving_updateAt_swap (i : ι) :
    MeasurePreserving (fun q : 𝓧 i × (Π j, 𝓧 j) => Function.update q.2 i q.1)
      ((μ i).prod (Measure.pi μ)) (Measure.pi μ) :=
  (measurePreserving_updateAt μ i).comp (Measure.measurePreserving_swap)

/-- **Blocks grow one coordinate at a time.** For `i ∉ S`, averaging over `insert i S`
is averaging over `S` followed by the leave-one-out mean at `i`. -/
theorem avgOn_insert (S : Finset ι) {i : ι} (hi : i ∉ S)
    (hf : Integrable f (Measure.pi μ)) :
    avgOn μ (insert i S) f =ᵐ[Measure.pi μ] condMeanAt μ i (avgOn μ S f) := by
  filter_upwards [ae_integrable_mixAt μ (insert i S) hf] with x hx
  set G : (Π j, 𝓧 j) → ℝ := fun z => f (mixAt (insert i S) x z) with hG
  have hswap : Integrable (Function.uncurry fun (y : 𝓧 i) (z : Π j, 𝓧 j) =>
      G (Function.update z i y)) ((μ i).prod (Measure.pi μ)) :=
    (measurePreserving_updateAt_swap μ i).integrable_comp_of_integrable hx
  have hcm : condMeanAt μ i (avgOn μ S f) x
      = ∫ y, ∫ z, G (Function.update z i y) ∂(Measure.pi μ) ∂(μ i) := by
    simp only [condMeanAt, avgOn]
    refine integral_congr_ae (.of_forall fun y => ?_)
    refine integral_congr_ae (.of_forall fun z => ?_)
    change f (mixAt S (Function.update x i y) z) = G (Function.update z i y)
    rw [mixAt_update_of_notMem S hi x z y]
    simp only [hG, mixAt_insert_update]
  rw [hcm, integral_integral_swap hswap, integral_integral_update μ i hx]
  simp only [avgOn, hG]


omit [Fintype ι] [∀ i, MeasurableSpace (𝓧 i)] [∀ i, IsProbabilityMeasure (μ i)] in
/-- Updating the `i`-th coordinate wipes out the difference between mixing over `S` and
mixing over `insert i S`. -/
theorem update_mixAt_insert (S : Finset ι) {i : ι} (x z : Π j, 𝓧 j) (y : 𝓧 i) :
    Function.update (mixAt S x z) i y = Function.update (mixAt (insert i S) x z) i y := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [mixAt, hj]

/-- The companion of `avgOn_insert` with the two operations in the other order. Unlike
`avgOn_insert` this one needs no Fubini swap. -/
theorem avgOn_condMeanAt_insert (S : Finset ι) {i : ι}
    (hf : Integrable f (Measure.pi μ)) :
    avgOn μ S (condMeanAt μ i f) =ᵐ[Measure.pi μ] avgOn μ (insert i S) f := by
  filter_upwards [ae_integrable_mixAt μ (insert i S) hf] with x hx
  set G : (Π j, 𝓧 j) → ℝ := fun z => f (mixAt (insert i S) x z) with hG
  have hstep : avgOn μ S (condMeanAt μ i f) x
      = ∫ z, ∫ y, G (Function.update z i y) ∂(μ i) ∂(Measure.pi μ) := by
    simp only [avgOn, condMeanAt]
    refine integral_congr_ae (.of_forall fun z => ?_)
    refine integral_congr_ae (.of_forall fun y => ?_)
    change f (Function.update (mixAt S x z) i y) = G (Function.update z i y)
    rw [update_mixAt_insert S x z y]
    simp only [hG, mixAt_insert_update]
  rw [hstep, integral_integral_update μ i hx]
  simp only [avgOn, hG]

/-- **The block average commutes with the leave-one-out mean** at a coordinate outside
the block. -/
theorem condMeanAt_avgOn_comm (S : Finset ι) {i : ι} (hi : i ∉ S)
    (hf : Integrable f (Measure.pi μ)) :
    condMeanAt μ i (avgOn μ S f) =ᵐ[Measure.pi μ] avgOn μ S (condMeanAt μ i f) :=
  (avgOn_insert μ S hi hf).symm.trans (avgOn_condMeanAt_insert μ S hf).symm

/-- Block averaging is linear, almost everywhere. -/
theorem avgOn_sub (S : Finset ι) {f₁ f₂ : (Π j, 𝓧 j) → ℝ}
    (hf₁ : Integrable f₁ (Measure.pi μ)) (hf₂ : Integrable f₂ (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ),
      avgOn μ S (fun w => f₁ w - f₂ w) x = avgOn μ S f₁ x - avgOn μ S f₂ x := by
  filter_upwards [ae_integrable_mixAt μ S hf₁, ae_integrable_mixAt μ S hf₂] with x h1 h2
  simp only [avgOn]
  exact integral_sub h1 h2

/-- A block average of an integrable function is integrable. -/
theorem integrable_avgOn (S : Finset ι) (hf : Integrable f (Measure.pi μ)) :
    Integrable (avgOn μ S f) (Measure.pi μ) :=
  ((measurePreserving_mixAt μ S).integrable_comp_of_integrable hf).integral_prod_left

/-- **Jensen for the block average.** -/
theorem sq_avgOn_le (S : Finset ι) (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ),
      (avgOn μ S f x) ^ 2 ≤ avgOn μ S (fun w => f w ^ 2) x := by
  filter_upwards [ae_memLp_mixAt μ S hfm hf] with x hx
  exact sq_integral_le_integral_sq hx

/-- **Block variance.** `varOn S f x` is the variance of `f` in the coordinates of `S`,
the coordinates outside `S` being held fixed at `x`. -/
noncomputable def varOn (S : Finset ι) (f : (Π j, 𝓧 j) → ℝ) (x : Π j, 𝓧 j) : ℝ :=
  Var[fun z => f (mixAt S x z); Measure.pi μ]

@[simp] theorem varOn_empty : varOn μ ∅ f = 0 := by
  funext x
  simp only [varOn, mixAt, Finset.piecewise_empty]
  rw [variance_eq_integral aemeasurable_const]
  simp

theorem varOn_ae_eq (S : Finset ι) (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ),
      varOn μ S f x = avgOn μ S (fun w => f w ^ 2) x - (avgOn μ S f x) ^ 2 := by
  filter_upwards [ae_memLp_mixAt μ S hfm hf] with x hx
  simpa [avgOn] using variance_eq_sub hx

theorem integral_varOn (S : Finset ι) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, varOn μ S f x ∂(Measure.pi μ)
      = (∫ x, f x ^ 2 ∂(Measure.pi μ))
        - ∫ x, (avgOn μ S f x) ^ 2 ∂(Measure.pi μ) := by
  rw [integral_congr_ae (varOn_ae_eq μ S hfm hf),
    integral_sub (integrable_avgOn μ S hf.integrable_sq)
      (memLp_avgOn μ S hfm hf).integrable_sq,
    integral_avgOn μ S hf.integrable_sq]

/-- **`E^{(i)}` is a self-adjoint projection in L²**: it absorbs the inner product. -/
theorem integral_mul_condMeanAt (i : ι) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, f x * condMeanAt μ i f x ∂(Measure.pi μ)
      = ∫ x, (condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) := by
  have hcm := memLp_condMeanAt μ i hfm hf
  have hprod : Integrable (fun x => f x * condMeanAt μ i f x) (Measure.pi μ) :=
    hf.integrable_mul hcm
  rw [← integral_integral_update μ i hprod]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [condMeanAt_update]
  rw [integral_mul_const, sq]
  rfl

/-- **Pythagoras** for the leave-one-out projection. -/
theorem integral_sub_condMeanAt_sq_eq (i : ι) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ)
      = (∫ x, f x ^ 2 ∂(Measure.pi μ))
        - ∫ x, (condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) := by
  have hcm := memLp_condMeanAt μ i hfm hf
  have hprod : Integrable (fun x => f x * condMeanAt μ i f x) (Measure.pi μ) :=
    hf.integrable_mul hcm
  have e : ∀ x, (f x - condMeanAt μ i f x) ^ 2
      = (f x ^ 2 - 2 * (f x * condMeanAt μ i f x)) + (condMeanAt μ i f x) ^ 2 := by
    intro x; ring
  have h2 : Integrable (fun x => 2 * (f x * condMeanAt μ i f x)) (Measure.pi μ) :=
    hprod.const_mul 2
  have h1 : Integrable (fun x => f x ^ 2 - 2 * (f x * condMeanAt μ i f x))
      (Measure.pi μ) := hf.integrable_sq.sub h2
  have h3 : Integrable (fun x => (condMeanAt μ i f x) ^ 2) (Measure.pi μ) :=
    hcm.integrable_sq
  simp_rw [e]
  rw [integral_add h1 h3, integral_sub hf.integrable_sq h2, integral_const_mul,
    integral_mul_condMeanAt μ i hfm hf]
  ring

/-- **The law of total variance, one coordinate at a time.** Growing the block by `i`
adds exactly the variance of the block average in the `i`-th coordinate. -/
theorem integral_varOn_insert (S : Finset ι) {i : ι} (hi : i ∉ S) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, varOn μ (insert i S) f x ∂(Measure.pi μ)
      = (∫ x, varOn μ S f x ∂(Measure.pi μ))
        + ∫ x, (avgOn μ S f x - condMeanAt μ i (avgOn μ S f) x) ^ 2 ∂(Measure.pi μ) := by
  have hgm := (stronglyMeasurable_avgOn μ S hfm).measurable
  have hg := memLp_avgOn μ S hfm hf
  have hins : ∫ x, (avgOn μ (insert i S) f x) ^ 2 ∂(Measure.pi μ)
      = ∫ x, (condMeanAt μ i (avgOn μ S f) x) ^ 2 ∂(Measure.pi μ) := by
    refine integral_congr_ae ?_
    filter_upwards [avgOn_insert μ S hi (hf.integrable one_le_two)] with x hx
    rw [hx]
  rw [integral_varOn μ (insert i S) hfm hf, integral_varOn μ S hfm hf,
    integral_sub_condMeanAt_sq_eq μ i hgm hg, hins]
  ring

/-- **The Jensen step**: block averaging can only shrink the `i`-th Efron–Stein summand. -/
theorem integral_avgOn_sub_condMeanAt_sq_le (S : Finset ι) {i : ι} (hi : i ∉ S)
    (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, (avgOn μ S f x - condMeanAt μ i (avgOn μ S f) x) ^ 2 ∂(Measure.pi μ)
      ≤ ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) := by
  have hfi : Integrable f (Measure.pi μ) := hf.integrable one_le_two
  have hcmm := (stronglyMeasurable_condMeanAt μ i hfm).measurable
  have hcmL := memLp_condMeanAt μ i hfm hf
  have hhm : Measurable (fun w => f w - condMeanAt μ i f w) := hfm.sub hcmm
  have hhL : MemLp (fun w => f w - condMeanAt μ i f w) 2 (Measure.pi μ) := hf.sub hcmL
  have hgL := memLp_avgOn μ S hfm hf
  have hgm := (stronglyMeasurable_avgOn μ S hfm).measurable
  have hLHS : Integrable
      (fun x => (avgOn μ S f x - condMeanAt μ i (avgOn μ S f) x) ^ 2) (Measure.pi μ) :=
    (hgL.sub (memLp_condMeanAt μ i hgm hgL)).integrable_sq
  have key : ∀ᵐ x ∂(Measure.pi μ),
      (avgOn μ S f x - condMeanAt μ i (avgOn μ S f) x) ^ 2
        ≤ avgOn μ S (fun w => (f w - condMeanAt μ i f w) ^ 2) x := by
    filter_upwards [condMeanAt_avgOn_comm μ S hi hfi,
      avgOn_sub μ S hfi (hcmL.integrable one_le_two),
      sq_avgOn_le μ S hhm hhL] with x hc hs hj
    rw [hc, ← hs]
    exact hj
  calc ∫ x, (avgOn μ S f x - condMeanAt μ i (avgOn μ S f) x) ^ 2 ∂(Measure.pi μ)
      ≤ ∫ x, avgOn μ S (fun w => (f w - condMeanAt μ i f w) ^ 2) x ∂(Measure.pi μ) :=
        integral_mono_ae hLHS (integrable_avgOn μ S hhL.integrable_sq) key
    _ = ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) :=
        integral_avgOn μ S hhL.integrable_sq

/-- **Tensorization of the variance**, by induction on the block of coordinates. -/
theorem integral_varOn_le (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ))
    (S : Finset ι) :
    ∫ x, varOn μ S f x ∂(Measure.pi μ)
      ≤ ∑ i ∈ S, ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [integral_varOn_insert μ S hi hfm hf, Finset.sum_insert hi]
      have hle := integral_avgOn_sub_condMeanAt_sq_le μ S hi hfm hf
      linarith

@[simp] theorem integral_varOn_univ :
    ∫ x, varOn μ Finset.univ f x ∂(Measure.pi μ) = Var[f; Measure.pi μ] := by
  simp [varOn]

/-- **The Efron–Stein inequality** (Boucheron–Lugosi–Massart 2013, Theorem 3.1). For
independent — not necessarily identically distributed — coordinates and a
square-integrable `f`,
$$ \operatorname{Var}(f) \;\le\; \sum_{i} \mathbf{E}\bigl[(f - \mathbf{E}^{(i)}f)^2\bigr]
   \;=\; v. $$ -/
theorem variance_le_efronSteinBound (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤ efronSteinBound μ f := by
  have h := integral_varOn_le μ hfm hf Finset.univ
  rwa [integral_varOn_univ μ] at h

end StatLean.ConcentrationInequalities
