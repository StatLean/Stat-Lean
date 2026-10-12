import StatLean.ConcentrationInequalities.ForMathlib.PiUpdate
import StatLean.ConcentrationInequalities.ForMathlib.VarianceResample

/-!
# The Efron–Stein bound: leave-one-out conditional means and the resampled form

Let $X_1, \dots, X_n$ be independent (not necessarily identically distributed) random
variables, realized canonically as the coordinates of a product probability space
$\bigotimes_j \mu_j$, and let $Z = f(X)$ be square-integrable. Write
$$ \mathbf{E}^{(i)} Z \;=\; \int f(X_1, \dots, x_i, \dots, X_n) \, d\mu_i(x_i) $$
for the conditional mean of $Z$ given every coordinate but the $i$-th. This file
introduces $\mathbf{E}^{(i)}$ (`condMeanAt`) and the quantity
$$ v \;=\; \sum_{i=1}^n \mathbf{E}\bigl[(Z - \mathbf{E}^{(i)} Z)^2\bigr] $$
(`efronSteinBound`) that bounds $\operatorname{Var}(Z)$ in the Efron–Stein inequality, and
proves the **resampling identity**
$$ v \;=\; \tfrac12 \sum_{i=1}^n \mathbf{E}\bigl[(Z - Z_i')^2\bigr], \qquad
   Z_i' = f(X_1, \dots, X_i', \dots, X_n), $$
which is the form in which the bound is actually applied.

The inequality $\operatorname{Var}(Z) \le v$ itself is proved in
`EfronStein/Tensorization.lean`, by tensorization of the variance over blocks of
coordinates.

**Reference.** Stéphane Boucheron, Gábor Lugosi and Pascal Massart, *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, 2013
(ISBN 978-0-19-953525-5), §3.1, Theorem 3.1 and its proof. The
discussion immediately before the theorem defines $X^{(i)}$, the vector with the $i$-th
coordinate omitted, and $\mathbf{E}^{(i)}$, expectation over that coordinate. The identity
proved here is the chain
$v = \sum_i \mathbf{E}[\operatorname{Var}^{(i)}(Z)] = \tfrac12 \sum_i
\mathbf{E}[(Z - Z_i')^2]$ inside the proof of Theorem 3.1.

**Relation to the 1981 result.** B. Efron and C. Stein, "The jackknife estimate of
variance", *Ann. Statist.* **9** (1981), 586–596, is the paper discussed in
Boucheron–Lugosi–Massart §3.9: "While the original result of Efron and Stein had some
extra conditions and came with a sub-optimal constant, Steele (1986) and Rhee and
Talagrand (1986) obtained improved versions and the form presented in Theorem 3.1."
For a symmetric statistic $S$ of i.i.d. observations,
Theorem 1 of the 1981 paper gives an exact formula for the bias of the natural jackknife
estimate of $\operatorname{Var} S(X_1,\ldots,X_{n-1})$. Theorem 2 drops symmetry and
identical distribution in the paper's leave-one-out setting: for independent observations
it proves
$\mathbf{E}\sum_i(S_{(i)}-S_{(\cdot)})^2 \ge n^{-1}\sum_i\operatorname{Var}(S_{(i)})
\ge \frac{n}{n-1}\operatorname{Var}(S_{(\cdot)})$, where $S_{(i)}$ is the statistic
computed with observation $i$ deleted and $S_{(\cdot)}$ is the average of the
$S_{(i)}$. The theorem formalized here is the improved form presented as Theorem 3.1 by
Boucheron–Lugosi–Massart.

**Proof formalization notes.** Everything is done on the canonical product space, so
$\mathbf{E}^{(i)}$ is a plain integral in one coordinate rather than a conditional
expectation, and no filtration is needed. Two facts carry the argument:
`integral_sub_sq_right` (ForMathlib/VarianceResample) evaluates the inner integral
$\int (g(a) - g(b))^2 \, d\nu(b) = (g(a) - \nu[g])^2 + \operatorname{Var}(g)$, and
`integral_integral_update` (ForMathlib/PiUpdate) says that averaging over a fresh $i$-th
coordinate leaves an expectation unchanged — this is where independence enters the
resampling identity. Combining them turns $\mathbf{E}[(Z - Z_i')^2]$ into
$\mathbf{E}[(Z - \mathbf{E}^{(i)}Z)^2]$ twice
over, giving the factor $\tfrac12$. Square-integrability of the slices and of
`condMeanAt` is obtained by transporting `MemLp.integrable_sq` across the same
measure-preserving map, with `sq_integral_le_integral_sq` (Jensen) dominating
$(\mathbf{E}^{(i)}Z)^2$ by $\mathbf{E}^{(i)}[Z^2]$.

**Bibliographic comments.** Boucheron–Lugosi–Massart §3.9 says: "The proof shown in
Section 3.1 appears in Rhee and Talagrand (1986)." The formalization in
`EfronStein/Tensorization.lean` realizes the same variance decomposition and Jensen step
through a block-tensorization recursion on the canonical product space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝓧 : ι → Type*}
  [∀ i, MeasurableSpace (𝓧 i)] (μ : ∀ i, Measure (𝓧 i))
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **The leave-one-out conditional mean** `E^{(i)} Z`: the average of `f` over a fresh
`i`-th coordinate, holding every other coordinate fixed. Under the measurability and
integrability hypotheses used below, it is a version of the conditional expectation of
`f` given all coordinates other than `i`; this identification with Mathlib's `condExp`
is not formalized here. -/
noncomputable def condMeanAt (i : ι) (f : (Π j, 𝓧 j) → ℝ) (x : Π j, 𝓧 j) : ℝ :=
  ∫ y, f (Function.update x i y) ∂(μ i)

/-- **The Efron–Stein bound** `v = ∑ᵢ E[(Z − E^{(i)}Z)²]`
(Boucheron–Lugosi–Massart 2013, Theorem 3.1). -/
noncomputable def efronSteinBound (f : (Π j, 𝓧 j) → ℝ) : ℝ :=
  ∑ i, ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ)

variable {f : (Π j, 𝓧 j) → ℝ}

omit [Fintype ι] [∀ i, IsProbabilityMeasure (μ i)] in
/-- **`E^{(i)}` forgets the `i`-th coordinate**: it is invariant under updating that
coordinate, which is what makes it a function of `X^{(i)}` alone. -/
@[simp] theorem condMeanAt_update (i : ι) (g : (Π j, 𝓧 j) → ℝ) (x : Π j, 𝓧 j) (y : 𝓧 i) :
    condMeanAt μ i g (Function.update x i y) = condMeanAt μ i g x := by
  simp only [condMeanAt, Function.update_idem]

omit [Fintype ι] in
/-- `E^{(i)} Z` is strongly measurable in the sample. -/
theorem stronglyMeasurable_condMeanAt (i : ι) (hfm : Measurable f) :
    StronglyMeasurable (condMeanAt μ i f) :=
  ((hfm.comp (measurable_update' (a := i))).stronglyMeasurable).integral_prod_right'

/-- **Almost every slice is square-integrable.** Transported across the measure-preserving
resampling map of `ForMathlib/PiUpdate`. -/
theorem ae_memLp_slice (i : ι) (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), MemLp (fun y => f (Function.update x i y)) 2 (μ i) := by
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × 𝓧 i => f (Function.update p.1 i p.2) ^ 2)
      ((Measure.pi μ).prod (μ i)) :=
    (measurePreserving_updateAt μ i).integrable_comp_of_integrable hf.integrable_sq
  filter_upwards [hcomp.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq
    (hfm.comp (measurable_update (a := i) x)).aestronglyMeasurable).2 hx

/-- **`E^{(i)} Z` is square-integrable.** Jensen dominates `(E^{(i)}Z)²` by `E^{(i)}[Z²]`,
whose expectation is `E[Z²]`. -/
theorem memLp_condMeanAt (i : ι) (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    MemLp (condMeanAt μ i f) 2 (Measure.pi μ) := by
  have hsm := stronglyMeasurable_condMeanAt μ i hfm
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × 𝓧 i => f (Function.update p.1 i p.2) ^ 2)
      ((Measure.pi μ).prod (μ i)) :=
    (measurePreserving_updateAt μ i).integrable_comp_of_integrable hf.integrable_sq
  have hdom : Integrable (fun x => ∫ y, f (Function.update x i y) ^ 2 ∂(μ i))
      (Measure.pi μ) := hcomp.integral_prod_left
  refine (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 ?_
  refine hdom.mono' ((hsm.measurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_memLp_slice μ i hfm hf] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_integral_le_integral_sq hx

/-- The `i`-th summand of the Efron–Stein bound is integrable. -/
theorem integrable_sub_condMeanAt_sq (i : ι) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Integrable (fun z => (f z - condMeanAt μ i f z) ^ 2) (Measure.pi μ) :=
  (hf.sub (memLp_condMeanAt μ i hfm hf)).integrable_sq

/-- **The resampling identity, one coordinate at a time.** Averaging the squared
difference between `Z` and its resampled copy `Z_i'` gives twice the `i`-th summand of the
Efron–Stein bound (Boucheron–Lugosi–Massart 2013, inside the proof of Theorem 3.1). -/
theorem integral_integral_sub_sq_update (i : ι) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ x, ∫ y, (f x - f (Function.update x i y)) ^ 2 ∂(μ i) ∂(Measure.pi μ)
      = 2 * ∫ x, (f x - condMeanAt μ i f x) ^ 2 ∂(Measure.pi μ) := by
  set h : (Π j, 𝓧 j) → ℝ := fun z => (f z - condMeanAt μ i f z) ^ 2 with hh
  have hhint : Integrable h (Measure.pi μ) := integrable_sub_condMeanAt_sq μ i hfm hf
  have hhint' : Integrable (fun x => ∫ y, h (Function.update x i y) ∂(μ i))
      (Measure.pi μ) :=
    ((measurePreserving_updateAt μ i).integrable_comp_of_integrable
      hhint).integral_prod_left
  have key : ∀ᵐ x ∂(Measure.pi μ), ∫ y, (f x - f (Function.update x i y)) ^ 2 ∂(μ i)
      = h x + ∫ y, h (Function.update x i y) ∂(μ i) := by
    filter_upwards [ae_memLp_slice μ i hfm hf] with x hx
    have hself : f (Function.update x i (x i)) = f x := by
      rw [Function.update_eq_self]
    have hslice := integral_sub_sq_right hx (x i)
    rw [hself] at hslice
    have hvar : Var[fun y => f (Function.update x i y); μ i]
        = ∫ y, h (Function.update x i y) ∂(μ i) := by
      rw [variance_eq_integral hx.aestronglyMeasurable.aemeasurable]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only [hh, condMeanAt_update]
      rfl
    rw [hslice, hvar]
    simp only [hh]
    rfl
  rw [integral_congr_ae key, integral_add hhint hhint',
    integral_integral_update μ i hhint]
  ring

/-- **The Efron–Stein bound in resampled form**
$$ v \;=\; \tfrac12 \sum_{i} \mathbf{E}\bigl[(Z - Z_i')^2\bigr], $$
where `Z_i'` replaces the `i`-th coordinate by an independent copy
(Boucheron–Lugosi–Massart 2013, Theorem 3.1). -/
theorem efronSteinBound_eq_half_sum (hfm : Measurable f) (hf : MemLp f 2 (Measure.pi μ)) :
    efronSteinBound μ f
      = (1 / 2) * ∑ i, ∫ x, ∫ y, (f x - f (Function.update x i y)) ^ 2 ∂(μ i)
          ∂(Measure.pi μ) := by
  simp only [efronSteinBound, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_integral_sub_sq_update μ i hfm hf]
  ring

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The Efron–Stein bound is nonnegative. -/
theorem efronSteinBound_nonneg : 0 ≤ efronSteinBound μ f :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

end StatLean.ConcentrationInequalities
