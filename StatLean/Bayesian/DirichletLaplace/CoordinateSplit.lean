import StatLean.Bayesian.DirichletLaplace.Defs
import StatLean.Bayesian.ForMathlib.PiLintegralFintype
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Coordinate splitting and tensorization of the DL posterior ratio (C11)

**This is the riskiest file of the milestone** — it carries the whole `WithLp.toLp` / subtype-pi /
product-measure transport stack, plus the `ℝ≥0∞`-cancellation that turns the full-model posterior
ratio into the sub-model posterior ratio (BPPD eq. (26), tensorization).

For a support set `S ⊆ ι` (with the true support `S₀` the intended instance), split every
coordinate object of the normal-means model along `S` and its complement `Sᶜ`:

* `projS S` / `extendS S` — the coordinate restriction `ℝ^ι → ℝ^{S}` and the zero-padding section
  `ℝ^{S} → ℝ^ι`;
* `norm_sq_split` — `‖θ‖² = ‖projS S θ‖² + ‖projS Sᶜ θ‖²` (Pythagoras over the coordinate partition);
* `dlPrior_map_projS` / `dlPrior_prod_apply` — the DL product prior marginalizes to the sub-prior and
  factorizes on product sets;
* `dlLR_split` — the Gaussian likelihood ratio factorizes, `dlLR θ₀ θ y = dlLR_S · dlLR_{Sᶜ}`;
* `dlNumer_cylinder` — on a cylinder over `S` the `S`-factor of the numerator peels off (the `Sᶜ`
  coordinates integrate to the sub-model denominator);
* `dlRatio_cylinder` — **tensorization (BPPD eq. (26))**: on a cylinder over `Sᶜ`, the full posterior
  ratio equals the `Sᶜ`-sub-model posterior ratio, the `S`-factor cancelling between numerator and
  denominator (which requires the `S`-factor to be finite and nonzero, `dlDenom_pos_lt_top`);
* `gaussShift_map_projS` — the data measure `N(θ, I)` marginalizes to `N(projS S θ, I)` on the
  sub-space.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). §6, eq. (26) (reduction of the posterior on `S₀ᶜ`-cylinders to the `S₀ᶜ`
sub-model, using the product structure of the prior and the likelihood).

**Proof formalization notes.** The subtype `{j // j ∈ S}` inherits `Fintype` from `[Fintype ι]` and
`[DecidablePred (· ∈ S)]`, so the sub-space `EuclideanSpace ℝ {j // j ∈ S}` and the sub-prior
`dlPrior a {j // j ∈ S}` are well-typed. The transport uses `WithLp.toLp` / `WithLp.ofLp` to move
between `EuclideanSpace ℝ ι` and the plain pi type, `measurePreserving_piEquivPiSubtypeProd` for the
`ℝ^ι ≃ ℝ^{S} × ℝ^{Sᶜ}` measure isomorphism, and `pi_map_restrict_subtype` / `lintegral_pi_split`
(from `ForMathlib.PiLintegralFintype`) for the marginal and the split-Tonelli. `dlLR_split` combines
`norm_sq_split` with the analogous inner-product split and `ENNReal.ofReal (exp a) * ENNReal.ofReal
(exp b) = ENNReal.ofReal (exp (a + b))`. In `dlRatio_cylinder` the `S`-factor
`dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)` is in `(0, ∞)` (integrand bounded by
`exp(½‖·‖²)`, prior a probability measure), so it cancels in the `ℝ≥0∞` quotient. **Fallback** (per
plan): if the `ℝ≥0∞` cancellation is intractable, prove only the `≤` direction `Theorem34` consumes,
or leave `dlRatio_cylinder` as the single named debt (its statement layer insulates the consumers).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Coordinate restriction to `S`** `ℝ^ι → ℝ^{S}` (BPPD §6, tensorization setup).

`projS S θ` keeps the coordinates of `θ` indexed by `S`, as an element of
`EuclideanSpace ℝ {j // j ∈ S}`. Edge behaviour: `S = ∅` gives a map into the zero space. -/
noncomputable def projS (S : Set ι) [DecidablePred (· ∈ S)] :
    EuclideanSpace ℝ ι → EuclideanSpace ℝ {j // j ∈ S} :=
  fun θ => WithLp.toLp 2 (fun i : {j // j ∈ S} => θ (i : ι))

/-- **Zero-padding extension** `ℝ^{S} → ℝ^ι` (BPPD §6, tensorization setup).

`extendS S u` places the coordinates of `u` at the indices in `S` and fills the complement with `0`;
it is a linear section of `projS S`. Edge behaviour: coordinates outside `S` are set to `0`. -/
noncomputable def extendS (S : Set ι) [DecidablePred (· ∈ S)] :
    EuclideanSpace ℝ {j // j ∈ S} → EuclideanSpace ℝ ι :=
  fun u => WithLp.toLp 2 (fun i : ι => if h : i ∈ S then u ⟨i, h⟩ else 0)

/-- **Pythagoras over the coordinate partition**: `‖θ‖² = ‖projS S θ‖² + ‖projS Sᶜ θ‖²`. -/
lemma norm_sq_split (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ : EuclideanSpace ℝ ι) :
    ‖θ‖ ^ 2 = ‖projS S θ‖ ^ 2 + ‖projS Sᶜ θ‖ ^ 2 := by
  sorry

/-- **The DL product prior marginalizes to the sub-prior**:
`(dlPrior a ι).map (projS S) = dlPrior a {j // j ∈ S}`. The product structure of the prior means
the `S`-coordinates are jointly `dlPrior a {j // j ∈ S}`, independent of the rest. -/
lemma dlPrior_map_projS (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] :
    (dlPrior a ι).map (projS S) = dlPrior a {j // j ∈ S} := by
  sorry

/-- **Product-set factorization of the DL prior**: on a "box" `projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B`
(constrain the `S`-coordinates to `A` and the `Sᶜ`-coordinates to `B`),
`dlPrior a ι (·) = dlPrior a {j // j ∈ S} A · dlPrior a {j // j ∈ Sᶜ} B`. -/
lemma dlPrior_prod_apply (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    {A : Set (EuclideanSpace ℝ {j // j ∈ S})} {B : Set (EuclideanSpace ℝ {j // j ∈ Sᶜ})}
    -- LEAN-ONLY: `A` measurable (product-measure factorization regularity)
    (hA : MeasurableSet A)
    -- LEAN-ONLY: `B` measurable (product-measure factorization regularity)
    (hB : MeasurableSet B) :
    dlPrior a ι (projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B)
      = dlPrior a {j // j ∈ S} A * dlPrior a {j // j ∈ Sᶜ} B := by
  sorry

/-- **The Gaussian likelihood ratio factorizes** over the coordinate partition:
`dlLR θ₀ θ y = dlLR (projS S θ₀) (projS S θ) (projS S y) · dlLR (projS Sᶜ θ₀) (projS Sᶜ θ)
(projS Sᶜ y)`. Both the inner product `⟪θ − θ₀, y − θ₀⟫` and the penalty `‖θ − θ₀‖²/2` split as a
sum over `S` and `Sᶜ`, and `exp` turns the sum into a product. -/
lemma dlLR_split (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ θ y : EuclideanSpace ℝ ι) :
    dlLR θ₀ θ y
      = dlLR (projS S θ₀) (projS S θ) (projS S y)
        * dlLR (projS Sᶜ θ₀) (projS Sᶜ θ) (projS Sᶜ y) := by
  sorry

/-- **The denominator is finite and nonzero, pointwise** (the `S`-factor of the tensorization).

For any finite index type `κ`, `dlDenom θ₀ (dlPrior a κ) y ∈ (0, ∞)`: the integrand
`dlLR θ₀ θ y = exp(½‖y − θ₀‖²)·exp(−½‖θ − y‖²)` is strictly positive and bounded above by
`exp(½‖y − θ₀‖²)`, and `dlPrior a κ` is a probability measure. This lets the `S`-factor cancel in the
`ℝ≥0∞` quotient of `dlRatio_cylinder`. -/
lemma dlDenom_pos_lt_top (a : ℝ) {κ : Type*} [Fintype κ] (θ₀ y : EuclideanSpace ℝ κ) :
    0 < dlDenom θ₀ (dlPrior a κ) y ∧ dlDenom θ₀ (dlPrior a κ) y < ⊤ := by
  sorry

/-- **The `S`-factor of the numerator peels off on a cylinder over `S`.**

For a cylinder `projS S ⁻¹' A` (constrain only the `S`-coordinates to `A`), the un-normalized
numerator factorizes as an `S`-sub-model numerator over `A` times the full `Sᶜ`-sub-model
denominator:

  `dlNumer θ₀ (dlPrior a ι) (projS S ⁻¹' A) y
      = dlNumer (projS S θ₀) (dlPrior a {j // j ∈ S}) A (projS S y)
        · dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y)`. -/
lemma dlNumer_cylinder (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ y : EuclideanSpace ℝ ι) {A : Set (EuclideanSpace ℝ {j // j ∈ S})}
    -- LEAN-ONLY: `A` measurable (Tonelli split regularity)
    (hA : MeasurableSet A) :
    dlNumer θ₀ (dlPrior a ι) (projS S ⁻¹' A) y
      = dlNumer (projS S θ₀) (dlPrior a {j // j ∈ S}) A (projS S y)
        * dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y) := by
  sorry

/-- **Tensorization / posterior-ratio reduction to the `Sᶜ`-sub-model** (BPPD eq. (26)).

When the truth is supported on `S` (`projS Sᶜ θ₀ = 0`), the full-model posterior ratio of a cylinder
`projS Sᶜ ⁻¹' B` over the complement coordinates equals the `Sᶜ`-sub-model posterior ratio of `B`:

  `dlNumer θ₀ Π (projS Sᶜ ⁻¹' B) y / dlDenom θ₀ Π y
      = dlNumer (projS Sᶜ θ₀) Π_{Sᶜ} B (projS Sᶜ y) / dlDenom (projS Sᶜ θ₀) Π_{Sᶜ} (projS Sᶜ y)`,

where `Π = dlPrior a ι` and `Π_{Sᶜ} = dlPrior a {j // j ∈ Sᶜ}`. The `S`-factor
`dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)` appears in both numerator and denominator
(via `dlNumer_cylinder` and `dlPrior_prod_apply`) and cancels because it is in `(0, ∞)`
(`dlDenom_pos_lt_top`). **Riskiest lemma of the milestone.** -/
lemma dlRatio_cylinder (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ y : EuclideanSpace ℝ ι)
    -- USER-INPUT: truth supported on `S` (θ₀ vanishes off `S`, i.e. `S ⊇ supp θ₀`); BPPD eq. (26) (S = S₀)
    (hθ₀ : projS Sᶜ θ₀ = 0)
    -- LEAN-ONLY: `B` measurable (cylinder regularity)
    {B : Set (EuclideanSpace ℝ {j // j ∈ Sᶜ})} (hB : MeasurableSet B) :
    dlNumer θ₀ (dlPrior a ι) (projS Sᶜ ⁻¹' B) y / dlDenom θ₀ (dlPrior a ι) y
      = dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) B (projS Sᶜ y)
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y) := by
  sorry

/-- **The data measure marginalizes to the sub-model data measure**:
`(gaussShiftKernel ι θ).map (projS S) = gaussShiftKernel {j // j ∈ S} (projS S θ)`. Marginalizing
`N(θ, I)` onto the `S`-coordinates gives `N(projS S θ, I)` on the sub-space. -/
lemma gaussShift_map_projS (S : Set ι) [DecidablePred (· ∈ S)] (θ : EuclideanSpace ℝ ι) :
    (gaussShiftKernel ι θ).map (projS S) = gaussShiftKernel {j // j ∈ S} (projS S θ) := by
  sorry

end StatLean.Bayesian
