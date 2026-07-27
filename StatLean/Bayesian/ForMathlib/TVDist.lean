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
  sorry

/-- **Pushforward contracts total variation.** -/
theorem tvDist_map_le (μ ν : Measure α) {f : α → β}
    -- LEAN-ONLY: measurability of the transport map (regularity)
    (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  sorry

/-- **Total variation is invariant under measurable embeddings** (in particular under
measurable equivalences, e.g. the affine rescaling `θ ↦ √n(θ − θ₀)`). -/
theorem tvDist_map_measurableEmbedding (μ ν : Measure α) {f : α → β}
    -- LEAN-ONLY: the transport map is a measurable embedding (regularity)
    (hf : MeasurableEmbedding f) :
    tvDist (μ.map f) (ν.map f) = tvDist μ ν := by
  sorry

/-- **Conditioning moves a probability measure by at most `μ Cᶜ / μ C` in TV.** This is the
sup-form version of vdV's Step-A inequality `‖P − P^C‖ ≤ 2 P(Cᶜ)` (p. 142): for any event
`A`, `μ A − μ[|C] A ≤ μ (Cᶜ)` and `μ[|C] A − μ A ≤ μ Cᶜ / μ C`. -/
theorem tvDist_cond_le (μ : Measure α) [IsProbabilityMeasure μ] {C : Set α}
    -- LEAN-ONLY: the conditioning event is measurable (regularity)
    (hC : MeasurableSet C) :
    tvDist μ (μ[|C]) ≤ μ Cᶜ / μ C := by
  sorry

/-- **Positive-part density formula on a common dominating measure**: for probability
measures given by densities `p, q` against a common base,
`tvDist = ∫⁻ (p − q) d(base)` (truncated subtraction = positive part). -/
theorem tvDist_withDensity_eq (base : Measure α) {p q : α → ℝ≥0∞}
    -- LEAN-ONLY: measurable densities (regularity)
    (hp : Measurable p) (hq : Measurable q)
    [IsProbabilityMeasure (base.withDensity p)] [IsProbabilityMeasure (base.withDensity q)] :
    tvDist (base.withDensity p) (base.withDensity q) = ∫⁻ x, p x - q x ∂base := by
  sorry

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
  sorry

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
  sorry

end StatLean.Bayesian
