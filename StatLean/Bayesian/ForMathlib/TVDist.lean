import StatLean.Minimaxity.ForMathlib.TotalVariation
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Total-variation distance: transport, conditioning, and kernel measurability

Extensions of `StatLean.Minimaxity.tvDist` (the sup-over-events total-variation distance)
needed by the Bernstein–von Mises development (vdV Chapter 10):

* `tvDist_triangle` — the triangle inequality;
* `tvDist_map_le` / `tvDist_map_measurableEmbedding` — pushforward contracts TV, with
  equality under a measurable embedding (used to unrescale the local parameter
  `h = √n(θ − θ₀)`);
* `tvDist_cond_le` — conditioning on an event `C` moves a probability measure by at most
  `μ Cᶜ / μ C` in TV (vdV's Step-A bound `‖P − P^C‖ ≤ 2 P(Cᶜ)`, in sup-form normalization);
* `tvDist_withDensity_eq` — the positive-part density formula on a common dominating measure;
* `one_sub_lintegral_le_lintegral_one_sub` — the scalar Jensen step `(1 − ∫Y)⁺ ≤ ∫(1 − Y)⁺`
  in its `ℝ≥0∞` truncated-subtraction form;
* `measurable_tvDist_kernel` — measurability of `x ↦ tvDist (κ x) (η x)` for finite kernels
  on a countably generated target (via `Kernel.rnDeriv` joint measurability), which makes the
  Bernstein–von Mises event `{x | δ ≤ tvDist (posterior x) (gauss x)}` measurable.

**Proof formalization notes.** `tvDist` is the *sup-over-events* distance, i.e. **half** of
vdV's `L¹` total-variation norm `‖P − Q‖ = ∫|p − q|`; all Chapter-10 statements are
convergence-to-zero so the factor is immaterial, but the constants in intermediate bounds
follow the sup-form convention. The formula route is `tvDist_eq_half_lintegral` plus
`|a − b| = (a − b) + (b − a)` in truncated `ℝ≥0∞` arithmetic.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
open StatLean.Minimaxity

namespace StatLean.Bayesian

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Triangle inequality** for the total-variation distance. -/
theorem tvDist_triangle (μ ν ξ : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  calc μ s - ξ s ≤ (μ s - ν s) + (ν s - ξ s) := tsub_le_tsub_add_tsub
    _ ≤ tvDist μ ν + tvDist ν ξ :=
        add_le_add (le_iSup₂ (f := fun t (_ : MeasurableSet t) => μ t - ν t) s hs)
          (le_iSup₂ (f := fun t (_ : MeasurableSet t) => ν t - ξ t) s hs)

/-- **Pushforward contracts total variation.** -/
theorem tvDist_map_le (μ ν : Measure α) {f : α → β}
    -- LEAN-ONLY: measurability of the transport map (regularity)
    (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  exact le_iSup₂ (f := fun t (_ : MeasurableSet t) => μ t - ν t) (f ⁻¹' s) (hf hs)

/-- **Total variation is invariant under measurable embeddings** (in particular under
measurable equivalences, e.g. the affine rescaling `θ ↦ √n(θ − θ₀)`). -/
theorem tvDist_map_measurableEmbedding (μ ν : Measure α) {f : α → β}
    -- LEAN-ONLY: the transport map is a measurable embedding (regularity)
    (hf : MeasurableEmbedding f) :
    tvDist (μ.map f) (ν.map f) = tvDist μ ν := by
  refine le_antisymm (tvDist_map_le μ ν hf.measurable) ?_
  refine iSup_le fun s => iSup_le fun hs => ?_
  have himg : MeasurableSet (f '' s) := hf.measurableSet_image' hs
  have hpre : f ⁻¹' (f '' s) = s := hf.injective.preimage_image s
  have hμ : (μ.map f) (f '' s) = μ s := by
    rw [Measure.map_apply hf.measurable himg, hpre]
  have hν : (ν.map f) (f '' s) = ν s := by
    rw [Measure.map_apply hf.measurable himg, hpre]
  rw [← hμ, ← hν]
  exact le_iSup₂ (f := fun t (_ : MeasurableSet t) => (μ.map f) t - (ν.map f) t) (f '' s) himg

/-- **Conditioning moves a probability measure by at most `μ Cᶜ / μ C` in TV.** This is the
sup-form version of vdV's Step-A inequality `‖P − P^C‖ ≤ 2 P(Cᶜ)` (p. 142): for any event
`A`, `μ A − μ[|C] A ≤ μ (Cᶜ)` and `μ[|C] A − μ A ≤ μ Cᶜ / μ C`. -/
theorem tvDist_cond_le (μ : Measure α) [IsProbabilityMeasure μ] {C : Set α}
    -- LEAN-ONLY: the conditioning event is measurable (regularity)
    (hC : MeasurableSet C) :
    tvDist μ (μ[|C]) ≤ μ Cᶜ / μ C := by
  rcases eq_or_ne (μ C) 0 with hC0 | hC0
  · have : μ Cᶜ = 1 := by
      rw [prob_compl_eq_one_sub hC, hC0, tsub_zero]
    rw [this, hC0, ENNReal.div_zero one_ne_zero]
    exact le_top
  · have hCle : μ C ≤ 1 := prob_le_one
    have hcc : μ Cᶜ ≤ μ Cᶜ / μ C := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl (measure_ne_top _ _))]
      exact mul_le_of_le_one_right' hCle
    refine iSup_le fun s => iSup_le fun hs => ?_
    refine le_trans ?_ hcc
    have hle : μ (C ∩ s) ≤ (μ C)⁻¹ * μ (C ∩ s) := by
      refine le_mul_of_one_le_left' ?_
      exact ENNReal.one_le_inv.mpr hCle
    have hsplit : μ s ≤ μ (C ∩ s) + μ Cᶜ := by
      calc μ s ≤ μ ((C ∩ s) ∪ Cᶜ) := measure_mono (fun x hx => by
            by_cases hxC : x ∈ C
            · exact Or.inl ⟨hxC, hx⟩
            · exact Or.inr hxC)
        _ ≤ μ (C ∩ s) + μ Cᶜ := measure_union_le _ _
    rw [cond_apply hC μ s]
    calc μ s - (μ C)⁻¹ * μ (C ∩ s) ≤ (μ (C ∩ s) + μ Cᶜ) - μ (C ∩ s) :=
          tsub_le_tsub hsplit hle
      _ = μ Cᶜ := ENNReal.add_sub_cancel_left (measure_ne_top _ _)

-- General (finite-mass) form of the positive-part density formula: the defining supremum is
-- attained on `A = {q ≤ p}`, where `wd p A − wd q A = ∫_A (p − q)` and `(p − q)` vanishes off `A`.
-- Only finiteness of the *subtracted* density's total mass is needed.
private lemma tvDist_withDensity_eq' (base : Measure α) {p q : α → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hqfin : ∫⁻ x, q x ∂base ≠ ∞) :
    tvDist (base.withDensity p) (base.withDensity q) = ∫⁻ x, p x - q x ∂base := by
  set A : Set α := {x | q x ≤ p x} with hA
  have hAm : MeasurableSet A := measurableSet_le hq hp
  refine le_antisymm ?_ ?_
  · refine iSup_le fun s => iSup_le fun hs => ?_
    rw [withDensity_apply _ hs, withDensity_apply _ hs]
    calc ∫⁻ x in s, p x ∂base - ∫⁻ x in s, q x ∂base
        ≤ ∫⁻ x in s, (p x - q x) ∂base := lintegral_sub_le _ _ hq
      _ ≤ ∫⁻ x, (p x - q x) ∂base := lintegral_mono' Measure.restrict_le_self le_rfl
  · have hqA : ∫⁻ x in A, q x ∂base ≠ ∞ :=
      ne_top_of_le_ne_top hqfin (lintegral_mono' Measure.restrict_le_self le_rfl)
    have hcompl : ∫⁻ x in Aᶜ, (p x - q x) ∂base = 0 := by
      refine setLIntegral_eq_zero hAm.compl (fun x hx => ?_)
      simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact tsub_eq_zero_of_le hx.le
    have hle : q ≤ᵐ[base.restrict A] p := ae_restrict_of_forall_mem hAm (fun x hx => hx)
    have key : ∫⁻ x, (p x - q x) ∂base
        = (base.withDensity p) A - (base.withDensity q) A := by
      rw [← lintegral_add_compl _ hAm, hcompl, add_zero, lintegral_sub hq hqA hle,
        withDensity_apply _ hAm, withDensity_apply _ hAm]
    rw [key]
    exact le_iSup₂ (f := fun s (_ : MeasurableSet s) =>
      (base.withDensity p) s - (base.withDensity q) s) A hAm

/-- **Positive-part density formula on a common dominating measure**: for probability
measures given by densities `p, q` against a common base,
`tvDist = ∫⁻ (p − q) d(base)` (truncated subtraction = positive part). -/
theorem tvDist_withDensity_eq (base : Measure α) {p q : α → ℝ≥0∞}
    -- LEAN-ONLY: measurable densities (regularity)
    (hp : Measurable p) (hq : Measurable q)
    [IsProbabilityMeasure (base.withDensity p)] [IsProbabilityMeasure (base.withDensity q)] :
    tvDist (base.withDensity p) (base.withDensity q) = ∫⁻ x, p x - q x ∂base :=
  tvDist_withDensity_eq' base hp hq (by
    have h : ∫⁻ x, q x ∂base = (base.withDensity q) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h]; exact measure_ne_top _ _)

/-- **Scalar Jensen step in truncated `ℝ≥0∞` arithmetic**: `1 − ∫ Y ≤ ∫ (1 − Y)` for a
probability measure. (vdV p. 143: `(1 − E Y)⁺ ≤ E (1 − Y)⁺`; in `ℝ≥0∞` the truncated
subtraction is the positive part.) -/
theorem one_sub_lintegral_le_lintegral_one_sub (ν : Measure α) [IsProbabilityMeasure ν]
    (Y : α → ℝ≥0∞) :
    1 - ∫⁻ x, Y x ∂ν ≤ ∫⁻ x, 1 - Y x ∂ν := by
  sorry

/-- **Bounded integrands move by at most `B · tvDist`**: for probability measures and a
measurable `w ≤ B`, `∫ w dμ ≤ ∫ w dν + B · tvDist μ ν` (layer-cake over the sup-form
distance). -/
theorem lintegral_le_lintegral_add_tvDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {w : α → ℝ≥0∞}
    -- LEAN-ONLY: measurable integrand (regularity)
    (hw : Measurable w) {B : ℝ≥0∞}
    -- LEAN-ONLY: uniform bound on the integrand
    (hwB : ∀ x, w x ≤ B) :
    ∫⁻ x, w x ∂μ ≤ ∫⁻ x, w x ∂ν + B * tvDist μ ν := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Measure α, ξ = μ + ν := ⟨_, rfl⟩
  rw [← hξ] at hμξ hνξ
  haveI : IsFiniteMeasure ξ := by rw [hξ]; infer_instance
  set p := μ.rnDeriv ξ with hpdef
  set q := ν.rnDeriv ξ with hqdef
  have hpm : Measurable p := Measure.measurable_rnDeriv _ _
  have hqm : Measurable q := Measure.measurable_rnDeriv _ _
  have eμ : ξ.withDensity p = μ := Measure.withDensity_rnDeriv_eq _ _ hμξ
  have eν : ξ.withDensity q = ν := Measure.withDensity_rnDeriv_eq _ _ hνξ
  have hqfin : ∫⁻ x, q x ∂ξ ≠ ∞ := by
    rw [hqdef, Measure.lintegral_rnDeriv hνξ]; exact measure_ne_top _ _
  have htv : tvDist μ ν = ∫⁻ x, (p x - q x) ∂ξ := by
    have h := tvDist_withDensity_eq' ξ hpm hqm hqfin
    rwa [eμ, eν] at h
  have hμint : ∫⁻ x, w x ∂μ = ∫⁻ x, p x * w x ∂ξ := by
    have h : ∫⁻ x, w x ∂(ξ.withDensity p) = ∫⁻ x, p x * w x ∂ξ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hpm hw]; rfl
    rwa [eμ] at h
  have hνint : ∫⁻ x, w x ∂ν = ∫⁻ x, q x * w x ∂ξ := by
    have h : ∫⁻ x, w x ∂(ξ.withDensity q) = ∫⁻ x, q x * w x ∂ξ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hqm hw]; rfl
    rwa [eν] at h
  rw [hμint, hνint, htv]
  have hpt : ∀ x, p x * w x ≤ q x * w x + (p x - q x) * w x := by
    intro x
    rw [← add_mul]
    exact mul_le_mul_right' le_add_tsub _
  calc ∫⁻ x, p x * w x ∂ξ
      ≤ ∫⁻ x, (q x * w x + (p x - q x) * w x) ∂ξ := lintegral_mono hpt
    _ = ∫⁻ x, q x * w x ∂ξ + ∫⁻ x, (p x - q x) * w x ∂ξ :=
        lintegral_add_left (hqm.mul hw) _
    _ ≤ ∫⁻ x, q x * w x ∂ξ + ∫⁻ x, (p x - q x) * B ∂ξ := by
        refine add_le_add le_rfl (lintegral_mono fun x => ?_)
        exact mul_le_mul_left' (hwB x) (p x - q x)
    _ = ∫⁻ x, q x * w x ∂ξ + B * ∫⁻ x, (p x - q x) ∂ξ := by
        simp_rw [mul_comm _ B]
        rw [lintegral_const_mul _ (hpm.sub hqm)]

/-- **The pair-ratio Jensen bound** (vdV p. 143, Step B of the Bernstein–von Mises proof):
for probability measures `P, Q` obtained by normalizing densities `s, t` against a common
base, the TV distance is bounded by the double integral of the truncated pair ratio,
`tvDist P Q ≤ ∫∫ (1 − s(g)t(h)/(s(h)t(g))) dQ(g) dP(h)`.
The proof is `q/p (h) = ∫ s(g)t(h)/(s(h)t(g)) dQ(g)` plus the scalar Jensen step
`one_sub_lintegral_le_lintegral_one_sub` and `tvDist = ∫ (p − q)⁺`. -/
theorem tvDist_normalize_le_double_lintegral (base : Measure α) {s t : α → ℝ≥0∞}
    -- LEAN-ONLY: measurable densities (regularity)
    (hs : Measurable s) (ht : Measurable t)
    -- LEAN-ONLY: nondegenerate normalizers (positive, finite total masses)
    (hs0 : 0 < ∫⁻ x, s x ∂base) (hsT : ∫⁻ x, s x ∂base ≠ ∞)
    (ht0 : 0 < ∫⁻ x, t x ∂base) (htT : ∫⁻ x, t x ∂base ≠ ∞)
    -- LEAN-ONLY: a.e.-positive, a.e.-finite densities (the ratio is a.e. well defined)
    (hs_pos : ∀ᵐ x ∂base, 0 < s x) (hs_fin : ∀ᵐ x ∂base, s x ≠ ∞)
    (ht_pos : ∀ᵐ x ∂base, 0 < t x) (ht_fin : ∀ᵐ x ∂base, t x ≠ ∞) :
    tvDist (base.withDensity fun x => s x / ∫⁻ y, s y ∂base)
        (base.withDensity fun x => t x / ∫⁻ y, t y ∂base)
      ≤ ∫⁻ h, (∫⁻ g, (1 - (s g * t h) / (s h * t g))
            ∂(base.withDensity fun x => t x / ∫⁻ y, t y ∂base))
          ∂(base.withDensity fun x => s x / ∫⁻ y, s y ∂base) := by
  sorry

/-- **Measurability of the pointwise TV distance between two finite kernels** on a countably
generated target σ-algebra, via joint measurability of `Kernel.rnDeriv`. This is what makes
the Bernstein–von Mises deviation event `{x | δ ≤ tvDist (posterior x) (gaussian x)}`
measurable. -/
theorem measurable_tvDist_kernel [MeasurableSpace.CountablyGenerated β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable fun a => tvDist (κ a) (η a) := by
  classical
  set F : α → β → ℝ≥0∞ := fun a x => ENNReal.ofReal (Kernel.rnDerivAux κ (κ + η) a x) with hF
  set G : α → β → ℝ≥0∞ := fun a x => ENNReal.ofReal (Kernel.rnDerivAux η (κ + η) a x) with hG
  have hFκ : ∀ a, ((κ + η) a).withDensity (F a) = κ a := by
    intro a
    ext s hs
    rw [withDensity_apply _ hs]
    exact Kernel.setLIntegral_rnDerivAux κ η a hs
  have hGη : ∀ a, ((κ + η) a).withDensity (G a) = η a := by
    intro a
    ext s hs
    rw [withDensity_apply _ hs]
    have h := Kernel.setLIntegral_rnDerivAux η κ a hs
    rw [add_comm η κ] at h
    exact h
  have hFm : ∀ a, Measurable (F a) := fun a =>
    (Kernel.measurable_rnDerivAux_right κ (κ + η) a).ennreal_ofReal
  have hGm : ∀ a, Measurable (G a) := fun a =>
    (Kernel.measurable_rnDerivAux_right η (κ + η) a).ennreal_ofReal
  have heq : ∀ a, tvDist (κ a) (η a) = ∫⁻ x, (F a x - G a x) ∂((κ + η) a) := by
    intro a
    have hqfin : ∫⁻ x, G a x ∂((κ + η) a) ≠ ∞ := by
      have h : ∫⁻ x, G a x ∂((κ + η) a) = (((κ + η) a).withDensity (G a)) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [h, hGη a]; exact measure_ne_top _ _
    conv_lhs => rw [← hFκ a, ← hGη a]
    exact tvDist_withDensity_eq' _ (hFm a) (hGm a) hqfin
  simp_rw [heq]
  refine Measurable.lintegral_kernel_prod_right (κ := κ + η) ?_
  exact ((Kernel.measurable_rnDerivAux κ (κ + η)).ennreal_ofReal).sub
    ((Kernel.measurable_rnDerivAux η (κ + η)).ennreal_ofReal)

end StatLean.Bayesian
