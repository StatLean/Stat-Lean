import StatLean.ConcentrationInequalities.ForMathlib.PiUpdate
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Resampling a block of coordinates of a product measure

`PiUpdate` shows that redrawing a *single* coordinate of a finite product of probability
measures leaves the law unchanged. This file does the same for an arbitrary block
`S : Finset ι` of coordinates. The domain-specific `mixAt` name is a transparent alias
for `Finset.piecewise`, and the map
$$ (x, z) \;\longmapsto\; \bigl(j \mapsto \text{if } j \in S \text{ then } z_j
   \text{ else } x_j\bigr) $$
pushes $\left(\bigotimes_j \mu_j\right) \otimes \left(\bigotimes_j \mu_j\right)$ forward
to $\bigotimes_j \mu_j$. The block measure-preserving and integral results are absent
from Mathlib at our pin; the file has Mathlib-only imports and is a candidate upstream.

The second argument ranges over the *whole* product rather than over `∀ j : S, 𝓧 j`; the
coordinates outside `S` are simply discarded. This costs nothing (the extra marginals
integrate to one) and keeps every object in a single type, which avoids the subtype
products and `Function.updateFinset` coercions that `Mathlib/MeasureTheory/Integral/
Marginal.lean` needs for its `ℝ≥0∞`-valued `lmarginal`.

The payoff is `integral_integral_mixAt`: averaging a block of coordinates does not change
an expectation. With `avgOn` (see `EfronStein/Tensorization.lean`) this is what turns the
block-by-block variance recursion into a statement about `⨂ⱼ μ j` itself.

**Reference.** Stéphane Boucheron, Gábor Lugosi and Pascal Massart, *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, 2013
(ISBN 978-0-19-953525-5), §3.1. The block form is the analogue of the product-space
Fubini argument used there for coordinatewise resampling.

**Proof formalization notes.** Identical in shape to `measurePreserving_updateAt`:
`Measure.pi_eq` reduces to measurable rectangles, and the preimage of `Set.univ.pi s`
splits as a product of two rectangles, one carrying the sides outside `S` and one carrying
the sides inside `S`. Each factor's measure collapses by `Finset.prod_mul_prod_compl`
because the discarded marginals are probability measures. The integral form is
`integral_prod` followed by `integral_map`.

**Bibliographic comments.** As for `PiUpdate`: the invariance of a product law under
resampling a block of coordinates is elementary and carries no individual attribution.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {ι : Type*} [DecidableEq ι] {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]

/-- **The mix map.** `mixAt S x z` takes its `S`-coordinates from `z` and all others
from `x`. This is the domain-specific alias for `Finset.piecewise S z x`. -/
abbrev mixAt (S : Finset ι) (x z : Π j, 𝓧 j) : Π j, 𝓧 j :=
  S.piecewise z x

/-- Mixing is jointly measurable. -/
theorem measurable_mixAt (S : Finset ι) :
    Measurable (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => mixAt S p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j ∈ S
  · simpa only [mixAt, Finset.piecewise, h, if_true] using
      (measurable_pi_apply j).comp measurable_snd
  · simpa only [mixAt, Finset.piecewise, h, if_false] using
      (measurable_pi_apply j).comp measurable_fst

omit [∀ i, MeasurableSpace (𝓧 i)] in
/-- The preimage of a measurable rectangle under the mix map splits into the rectangle of
sides outside `S` (carried by `x`) times the rectangle of sides inside `S` (carried by
`z`), each padded with `univ` on the other block. -/
private theorem preimage_mixAt (S : Finset ι) (s : ∀ j, Set (𝓧 j)) :
    (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => mixAt S p.1 p.2) ⁻¹' (univ.pi s)
      = (univ.pi fun j => if j ∈ S then (univ : Set (𝓧 j)) else s j)
          ×ˢ (univ.pi fun j => if j ∈ S then s j else (univ : Set (𝓧 j))) := by
  ext ⟨x, z⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
    mixAt, Finset.piecewise]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j ∈ S
      · simp [hj]
      · have hx := h j; simp only [hj, if_false] at hx; simpa [hj]
    · by_cases hj : j ∈ S
      · have hz := h j; simp only [hj, if_true] at hz; simpa [hj]
      · simp [hj]
  · rintro ⟨hx, hz⟩ j
    by_cases hj : j ∈ S
    · have := hz j; simp only [hj, if_true] at this ⊢; exact this
    · have := hx j; simp only [hj, if_false] at this ⊢; exact this

variable [Fintype ι] (μ : ∀ i, Measure (𝓧 i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **Resampling a block of coordinates preserves the product law.** -/
theorem measurePreserving_mixAt (S : Finset ι) :
    MeasurePreserving (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => mixAt S p.1 p.2)
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  refine ⟨measurable_mixAt S, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_mixAt S) (MeasurableSet.univ_pi hs),
    preimage_mixAt S s, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  have key : ∀ F : ι → ℝ≥0∞,
      (∏ j, if j ∈ S then (1 : ℝ≥0∞) else F j) = ∏ j ∈ Sᶜ, F j := by
    intro F
    rw [← Finset.prod_mul_prod_compl S (fun j => if j ∈ S then (1 : ℝ≥0∞) else F j),
      Finset.prod_eq_one (fun j hj => by simp [hj]), one_mul]
    exact Finset.prod_congr rfl fun j hj => by simp [Finset.mem_compl.mp hj]
  have key' : ∀ F : ι → ℝ≥0∞,
      (∏ j, if j ∈ S then F j else (1 : ℝ≥0∞)) = ∏ j ∈ S, F j := by
    intro F
    rw [← Finset.prod_mul_prod_compl S (fun j => if j ∈ S then F j else (1 : ℝ≥0∞)),
      Finset.prod_eq_one (s := Sᶜ) (fun j hj => by simp [Finset.mem_compl.mp hj]), mul_one]
    exact Finset.prod_congr rfl fun j hj => by simp [hj]
  have h1 : ∀ j, μ j (if j ∈ S then (univ : Set (𝓧 j)) else s j)
      = if j ∈ S then 1 else μ j (s j) := by
    intro j; by_cases hj : j ∈ S <;> simp [hj]
  have h2 : ∀ j, μ j (if j ∈ S then s j else (univ : Set (𝓧 j)))
      = if j ∈ S then μ j (s j) else 1 := by
    intro j; by_cases hj : j ∈ S <;> simp [hj]
  simp_rw [h1, h2]
  rw [key (fun j => μ j (s j)), key' (fun j => μ j (s j))]
  exact Finset.prod_compl_mul_prod S (fun j => μ j (s j))

/-- **Averaging a block of coordinates does not change an expectation.** -/
theorem integral_integral_mixAt (S : Finset ι) {g : (Π j, 𝓧 j) → ℝ}
    (hg : Integrable g (Measure.pi μ)) :
    ∫ x, ∫ z, g (mixAt S x z) ∂(Measure.pi μ) ∂(Measure.pi μ)
      = ∫ x, g x ∂(Measure.pi μ) := by
  have hmp := measurePreserving_mixAt μ S
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => g (mixAt S p.1 p.2))
      ((Measure.pi μ).prod (Measure.pi μ)) := hmp.integrable_comp_of_integrable hg
  have hmeas : AEStronglyMeasurable g (Measure.map
      (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => mixAt S p.1 p.2)
      ((Measure.pi μ).prod (Measure.pi μ))) := by
    rw [hmp.map_eq]; exact hg.aestronglyMeasurable
  calc ∫ x, ∫ z, g (mixAt S x z) ∂(Measure.pi μ) ∂(Measure.pi μ)
      = ∫ p, g (mixAt S p.1 p.2) ∂((Measure.pi μ).prod (Measure.pi μ)) :=
        (integral_prod _ hcomp).symm
    _ = ∫ x, g x ∂(Measure.pi μ) := by
        have hmap := integral_map (μ := (Measure.pi μ).prod (Measure.pi μ))
          (φ := fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => mixAt S p.1 p.2)
          (measurable_mixAt S).aemeasurable hmeas
        rw [hmp.map_eq] at hmap
        exact hmap.symm

/-- Almost every mixed slice of a square-integrable function is square-integrable. -/
theorem ae_memLp_mixAt (S : Finset ι) {g : (Π j, 𝓧 j) → ℝ} (hgm : Measurable g)
    (hg : MemLp g 2 (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), MemLp (fun z => g (mixAt S x z)) 2 (Measure.pi μ) := by
  have hcomp : Integrable (fun p : (Π j, 𝓧 j) × (Π j, 𝓧 j) => g (mixAt S p.1 p.2) ^ 2)
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    (measurePreserving_mixAt μ S).integrable_comp_of_integrable hg.integrable_sq
  filter_upwards [hcomp.prod_right_ae] with x hx
  have hsl : Measurable (fun z => g (mixAt S x z)) :=
    hgm.comp ((measurable_mixAt S).comp (measurable_const.prodMk measurable_id))
  exact (memLp_two_iff_integrable_sq hsl.aestronglyMeasurable).2 hx

end StatLean.ConcentrationInequalities
