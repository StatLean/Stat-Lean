import StatLean.HypothesisTesting.Unbiased.ConditionalExpFamily
import StatLean.HypothesisTesting.Unbiased.PowerContinuity

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
  -- BLOCKED. Route unchanged — (1) reduce to the boundary surface `θ = θ₀` via
  -- `PowerContinuity.isUMPU_of_isUMP_on_boundary`; (2) similar ⟺ Neyman structure by
  -- `SimilarityCompleteness` + completeness of the `T`-laws on the slice; (3) apply conditional
  -- Neyman–Pearson to the one-parameter conditional exp family — but the two binding obstructions
  -- are now: (a) `ConditionalExpFamily.condDistrib_expFamily_of_isCanonicalUT`, itself blocked on
  -- `[OpensMeasurableSpace Ξ] [SecondCountableTopology Ξ]` (the nuisance factor `t ↦ exp⟪ϑ,t⟫`
  -- measurability — `CondDistribTilt` is now CLOSED, so it is no longer the block); and
  -- (b) `PowerContinuity.continuous_power_expFamily`, still an open analytic debt (differentiation
  -- under the integral for the exp-family power). Both are required by the assembly. Reported.
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
  -- BLOCKED as `isUMPU_conditional_oneSided`, with two boundary surfaces `θ = θ₁, θ = θ₂` and the
  -- conditional generalized Neyman–Pearson (two size constraints) for the reject-inside test. Same
  -- two blocks: the conditional exp-family form (needs `[OpensMeasurableSpace Ξ]
  -- [SecondCountableTopology Ξ]`; `CondDistribTilt` is now closed) and the open
  -- `continuous_power_expFamily`. Reported.
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
  -- BLOCKED: interval-null dual of `isUMPU_conditional_inside` (reject-outside test, two size
  -- constraints on `θ = θ₁, θ = θ₂`). Same two blocks — conditional exp-family form (needs
  -- `[OpensMeasurableSpace Ξ] [SecondCountableTopology Ξ]`; `CondDistribTilt` now closed) and the
  -- open `continuous_power_expFamily`. Reported.
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
  -- BLOCKED: point-null conditional UMPU. As `isUMPU_conditional_outside` but the single surface
  -- `θ = θ₀` carries BOTH the conditional size and conditional derivative (`hsize`, `hderiv`)
  -- constraints — unbiasedness at the interior minimum. Same two blocks: conditional exp-family
  -- form (needs `[OpensMeasurableSpace Ξ] [SecondCountableTopology Ξ]`; `CondDistribTilt` now
  -- closed) and the open `continuous_power_expFamily`. Reported.
  sorry

/-! ## Measurable selection of the conditional constants -/

/-- **Existence of measurable conditional constants (one-sided case).**

There is a measurable choice of critical value `C₀(t)` and randomization probability `γ₀(t)`
achieving conditional size `α` on the surface `T = t`, for almost every `t`.

Construction: with `F_t(u) = P_{θ₀}{U ≤ u ∣ t}` the conditional distribution function
(Mathlib's `condCDF` of the conditional law), the size equation reads
`F_t(C) − γ·[F_t(C) − F_t(C−)] = 1 − α`, solved by the conditional quantile
`C₀(t) = inf {u | F_t(u) ≥ 1 − α}` together with the matching interpolation weight.
Joint measurability of `(u, t) ↦ F_t(u)` — which follows from monotonicity and right
continuity in `u` via the countable rational approximation
`{(u,t) | F_t(u) ≥ c} = ⋂ₙ ⋃ᵣ {(u,t) | 0 ≤ r − u < 1/n, F_t(r) ≥ c}` — makes both `C₀` and
`γ₀` measurable in `t`. -/
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
  -- BLOCKED on a packaged measurable conditional quantile — NOTE this target needs NEITHER
  -- `Ξ`-measurability NOR the exp-family form (`CondDistribTilt`): the size equation
  -- `κt(Ioi C₀) + γ₀·κt{C₀} = α` for `κ = condDistrib U T (P p₀)` (a Markov kernel) is attainable
  -- for ANY conditional law by the quantile construction (`ForMathlib/QuantileFunction`'s
  -- `exists_critical_constants` gives it per-`t`; `quantile_le_iff` is the Galois input). The gap
  -- is MEASURABILITY in `t`: set `C₀ t = quantile (condCDF ρ t) (1-α)` for `ρ = (P p₀).map (T,U)`
  -- (so `κ = ρ.condKernel`); `measurable_condCDF` + `quantile_le_iff` give `Measurable C₀`, but the
  -- atom weight `γ₀ t` needs a measurable `Function.leftLim (condCDF ρ t)`, and relating the
  -- real-point masses `κt(Ioi C₀ t)`, `κt{C₀ t}` back to `condCDF ρ t` uses only the a.e.-at-
  -- rationals bridge `condCDF_ae_eq` — Mathlib packages no measurable conditional quantile of a
  -- kernel. Self-contained (~250 lines) but out of a single non-interactive pass's safe budget.
  -- Reported (not lifted: this is a real missing Mathlib brick, not a false statement).
  sorry

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

/-- **Reduction to canonical form.**

A canonical `(U, T)` family is again canonical after the change of parameter of interest
`θ* = a₀θ + ⟪a, ϑ⟫` (`a₀ ≠ 0`), with statistic `U* = U/a₀`, `T* = T − (U/a₀)·a` and base
measure the image of `ν` under the same transformation. Consequently the four optimality
theorems above apply verbatim to hypotheses about `θ*`. -/
theorem isCanonicalUT_reparam
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {a₀ : ℝ} {a : Ξ}
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: the coefficient of the parameter of interest is nonzero
    (ha₀ : a₀ ≠ 0) :
    IsCanonicalUT (fun q => P (reparamUTInv a₀ a q)) (reparamUT a₀ a '' Ω)
      (fun x => U x / a₀) (fun x => T x - (U x / a₀) • a)
      (ν.map (statTransformUT a₀ a)) (fun q => C (reparamUTInv a₀ a q)) := by
  -- BLOCKED. Pure change-of-variables, but `statTransformUT a₀ a` (`z ↦ (z.1/a₀, z.2 -
  -- (z.1/a₀)•a)`) is measurable only with `[MeasurableSMul ℝ Ξ]` and `[MeasurableSub₂ Ξ]` (or a
  -- Borel structure on `Ξ`): `fun r : ℝ => r • a` and vector subtraction are continuous but the
  -- frozen `[MeasurableSpace Ξ]` is Borel-incompatible, so `map_map` for the statistic transform
  -- is unavailable (confirmed: `fun_prop` fails on `fun z : ℝ×Ξ => z.2 - (z.1/a₀)•a`). Given those
  -- instances the route: `(P (reparamUTInv q)).map statMap = ((P p).map (U,T)).map statTransform`
  -- (`map_map`), `= (ν.withDensity density_p).map statTransform` by `hUT`, `= (ν.map
  -- statTransform).withDensity density_q` via `MeasurableEquiv.map_withDensity`, with
  -- `density_p ∘ statTransform.symm = density_q` from `inner_exponent_reparam` (closed above).
  -- Reported.
  sorry

end StatLean.HypothesisTesting
