import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling one coordinate of a product measure

On a finite product $\bigotimes_j \mu_j$ of probability measures, replacing the $i$-th
coordinate of a sample by an independent draw from $\mu_i$ leaves the law unchanged:
the map $(x, y) \mapsto \mathrm{update}\,x\,i\,y$ pushes
$\left(\bigotimes_j \mu_j\right) \otimes \mu_i$ forward to $\bigotimes_j \mu_j$.
Mathlib supplies the joint measurability of this map as `measurable_update'`. This file
adds the product-law measure-preserving and integral results. It has Mathlib-only imports
and is a candidate for upstreaming those probability-specific results.

This is one of the product-law invariance facts through which independence enters the
Efron–Stein development; `PiMix` supplies the corresponding block fact. It licenses
reading $Z_i' = f(X_1, \dots, X_i', \dots, X_n)$ as an independent copy of $Z$
conditionally on $X^{(i)}$.

**Reference.** Stéphane Boucheron, Gábor Lugosi and Pascal Massart, *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, 2013
(ISBN 978-0-19-953525-5), §3.1, in the discussion preceding Theorem 3.1, for the
coordinatewise integral formulas and surrounding Fubini discussion. Equation (3.1) there
is the conditional-expectation identity
$\mathbf{E}_i[\mathbf{E}^{(i)}Z] = \mathbf{E}_{i-1}Z$.

**Proof formalization notes.** `Measure.pi_eq` reduces the pushforward identity to
measurable rectangles. The preimage of `Set.univ.pi s` under the update map is
`(Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i`, whose product measure is
`(∏ j, μ j (Function.update s i Set.univ j)) * μ i (s i)`; rewriting the integrand as
`Function.update (fun j => μ j (s j)) i (μ i Set.univ)` lets `Finset.prod_update_of_mem`
peel off the `i`-th factor, which is `1` because `μ i` is a probability measure, and
`Finset.mul_prod_erase` puts `μ i (s i)` back in its place. The integral form is
`integral_prod` followed by `integral_map` against `MeasurePreserving.map_eq`; note the
update map is *not* a measurable embedding (it forgets the old `i`-th coordinate), so
`MeasurePreserving.integral_comp` does not apply and `integral_map` is used directly.

**Bibliographic comments.** The statement is the elementary "resampling leaves a product
law invariant" fact underlying every exchangeable-pair and Stein-method construction; it
has no individual attribution.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {ι : Type*} [DecidableEq ι] {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]

omit [∀ i, MeasurableSpace (𝓧 i)] in
/-- The preimage of a measurable rectangle under the update map is again a rectangle:
the `i`-th side is carried by the fresh draw, every other side by the sample. -/
private theorem preimage_updateAt (i : ι) (s : ∀ j, Set (𝓧 j)) :
    (fun p : (Π j, 𝓧 j) × 𝓧 i => Function.update p.1 i p.2) ⁻¹' (univ.pi s)
      = (univ.pi (Function.update s i univ)) ×ˢ s i := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simp
      · have hxj := h j
        rw [Function.update_of_ne hj] at hxj
        rwa [Function.update_of_ne hj]
    · have hy := h i
      rwa [Function.update_self] at hy
  · rintro ⟨hx, hy⟩ j
    by_cases hj : j = i
    · subst hj; rwa [Function.update_self]
    · rw [Function.update_of_ne hj]
      have hxj := hx j
      rwa [Function.update_of_ne hj] at hxj

variable [Fintype ι] (μ : ∀ i, Measure (𝓧 i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **Resampling one coordinate preserves the product law.** For probability measures
`μ j`, the map `(x, y) ↦ Function.update x i y` pushes `(⨂ⱼ μ j) ⊗ μ i` forward to
`⨂ⱼ μ j` (cf. the product-space and Fubini discussion in
Boucheron–Lugosi–Massart 2013, §3.1). -/
theorem measurePreserving_updateAt (i : ι) :
    MeasurePreserving (fun p : (Π j, 𝓧 j) × 𝓧 i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update' (a := i), ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_update' (a := i)) (MeasurableSet.univ_pi hs),
    preimage_updateAt i s, Measure.prod_prod, Measure.pi_pi]
  have hrw : (fun j => μ j (Function.update s i univ j))
      = Function.update (fun j => μ j (s j)) i (μ i univ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hrw, Finset.prod_update_of_mem (Finset.mem_univ i), measure_univ, one_mul,
    Finset.sdiff_singleton_eq_erase, mul_comm,
    Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i)]

/-- **Resampling form of the integral.** Averaging over a fresh `i`-th coordinate does not
change the expectation: `∫∫ f(update x i y) dμᵢ(y) d(⨂μ)(x) = ∫ f d(⨂μ)`. -/
theorem integral_integral_update (i : ι) {f : (Π j, 𝓧 j) → ℝ}
    (hf : Integrable f (Measure.pi μ)) :
    ∫ x, ∫ y, f (Function.update x i y) ∂(μ i) ∂(Measure.pi μ)
      = ∫ x, f x ∂(Measure.pi μ) := by
  have hmp := measurePreserving_updateAt μ i
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × 𝓧 i => f (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) := hmp.integrable_comp_of_integrable hf
  have hmeas : AEStronglyMeasurable f (Measure.map
      (fun p : (Π j, 𝓧 j) × 𝓧 i => Function.update p.1 i p.2) ((Measure.pi μ).prod (μ i))) := by
    rw [hmp.map_eq]; exact hf.aestronglyMeasurable
  calc ∫ x, ∫ y, f (Function.update x i y) ∂(μ i) ∂(Measure.pi μ)
      = ∫ p, f (Function.update p.1 i p.2) ∂((Measure.pi μ).prod (μ i)) :=
        (integral_prod _ hcomp).symm
    _ = ∫ x, f x ∂(Measure.pi μ) := by
        have hmap := integral_map (μ := (Measure.pi μ).prod (μ i))
          (φ := fun p : (Π j, 𝓧 j) × 𝓧 i => Function.update p.1 i p.2)
          (measurable_update' (a := i)).aemeasurable hmeas
        rw [hmp.map_eq] at hmap
        exact hmap.symm

end StatLean.ConcentrationInequalities
