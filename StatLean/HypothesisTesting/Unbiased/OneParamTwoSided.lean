import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.Unbiased.PowerContinuity
import StatLean.PointEstimation.ExponentialFamily.Defs

/-!
# UMP unbiased two-sided tests in a one-parameter exponential family

Let `P_θ` be a one-parameter exponential family with natural statistic `T`, i.e.
`dP_θ = C(θ) e^{θ T(x)} dν(x)`, and let `θ` range over a parameter set `Ξ` inside the
interior of the natural parameter set. For the two problems

* `H : θ₁ ≤ θ ≤ θ₂` against `K : θ < θ₁ or θ > θ₂`,
* `H : θ = θ₀` against `K : θ ≠ θ₀`,

no UMP test exists, but a UMP **unbiased** test does, and in both cases it rejects outside
an interval in `T`:
$$ \varphi(x) \;=\;
   \begin{cases} 1, & T(x) < C_1 \text{ or } T(x) > C_2,\\
                 \gamma_i, & T(x) = C_i,\ i = 1,2,\\
                 0, & C_1 < T(x) < C_2. \end{cases} $$
What differs is the pair of side conditions pinning `C₁, C₂, γ₁, γ₂`:

* interval null: **two size equations** `E_{θ₁}φ = E_{θ₂}φ = α`;
* point null: the **size equation** `E_{θ₀}φ = α` *together with the derivative condition*
  `E_{θ₀}[T φ] = α·E_{θ₀}[T]`.

The derivative condition is not decoration: unbiasedness forces the power function to have a
minimum at `θ₀`, and differentiating the power of an exponential family under the integral
sign turns `β'(θ₀) = 0` into exactly `E_{θ₀}[T φ] − E_{θ₀}[T]·E_{θ₀}[φ] = 0`, which combines
with the size equation to give the displayed form. Both equations are transcribed literally
below; neither may be dropped.

**Reference.** Classical one-parameter exponential-family testing theory; original sources in
the bibliographic comments below.

**Proof formalization notes.**
* *Dependency.* The critical function above is the complement `1 − φ` of the
  reject-inside-an-interval test used for the UMP problem `H : θ ≤ θ₁ or θ ≥ θ₂`, whose
  concrete definition `twoSidedTest` is drafted in
  `StatLean/HypothesisTesting/MLR/TwoSided.lean` (generalized Neyman–Pearson assembly).
  To avoid duplicating that definition here — and to keep this file independent of the
  exact shape of its arguments while both are in draft — the test enters as an abstract
  critical function `φ` constrained by four pointwise shape equations. When the assembly
  lands, these theorems should be instantiated at `1 − twoSidedTest …` (the `1 − φ`
  device by which the source derives the constants).
* The model enters as an arbitrary family `P` together with the identification
  `P θ = E.P θ` on `Ξ` (a `IsCanonicalRepr`-style hypothesis restricted to the parameter
  set actually used), so callers may keep their own parametrization; only members with
  `θ ∈ Ξ` are ever evaluated by the conclusion.
* `Ξ ⊆ interior E.natSet` is what makes the power functions continuous and differentiable
  (`continuous_power_expFamily`), which is what licenses the boundary device of
  `isUMPU_of_isUMP_on_boundary`; it also makes `T` integrable under every `P θ`, `θ ∈ Ξ`,
  so no separate integrability hypothesis is imposed on the two displayed equations.
* `C₁ ≤ C₂` is the degenerate-tolerant form of the source's `C₁ < C₂`; if `C₁ = C₂` the two
  boundary equations are compatible only when `γ₁ = γ₂`, which is the caller's obligation.

**Bibliographic comments.** UMP unbiased two-sided tests for exponential families are due to
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37), whose earlier fundamental
lemma ("On the problem of the most efficient tests of statistical hypotheses," *Phil. Trans.
R. Soc. A* **231** (1933), 289–337) supplies, in its multi-constraint form, the optimality
of tests subject to the two displayed side conditions.
-/

open MeasureTheory
open StatLean.PointEstimation

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **UMP unbiased test of a point null in a one-parameter exponential family.**

For `H : θ = θ₀` against `K : θ ≠ θ₀`, the test rejecting outside `[C₁, C₂]` on the natural
statistic scale is UMP unbiased at level `α`, provided the constants satisfy **both**

* the size condition `E_{θ₀}[φ] = α`, and
* the derivative condition `E_{θ₀}[T·φ] = α·E_{θ₀}[T]`

(the latter being the analytic form of "the power function has a minimum at `θ₀`"). -/
theorem isUMPU_twoSided_expFamily
    {P : ℝ → Measure 𝓧} {E : ExpFamily 𝓧 ℝ} {T : 𝓧 → ℝ} {Ξ : Set ℝ}
    {θ₀ α C₁ C₂ γ₁ γ₂ : ℝ} {φ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- LEAN-ONLY: name for the natural statistic of the family
    (hT : T = E.stat)
    -- USER-INPUT: on the parameter set of interest the model is the canonical
    -- one-parameter exponential family `dP_θ = C(θ)e^{θT}dν`
    (hP : ∀ θ ∈ Ξ, P θ = E.P θ)
    -- USER-INPUT: the parameter set lies in the interior of the natural parameter set;
    -- the standing regularity of the exponential-family development
    (hΞ : Ξ ⊆ interior E.natSet)
    -- USER-INPUT: the null value belongs to the parameter set
    (hθ₀ : θ₀ ∈ Ξ)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the two critical values are ordered
    (hC : C₁ ≤ C₂)
    -- USER-INPUT: the test is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: shape of the test — rejection outside the interval
    (hφ_one : ∀ x, T x < C₁ ∨ C₂ < T x → φ x = 1)
    -- USER-INPUT: shape of the test — acceptance strictly inside the interval
    (hφ_zero : ∀ x, C₁ < T x → T x < C₂ → φ x = 0)
    -- USER-INPUT: shape of the test — randomization at the lower critical value
    (hφ_γ₁ : ∀ x, T x = C₁ → φ x = γ₁)
    -- USER-INPUT: shape of the test — randomization at the upper critical value
    (hφ_γ₂ : ∀ x, T x = C₂ → φ x = γ₂)
    -- USER-INPUT: size condition at the null value
    (hsize : power P φ θ₀ = α)
    -- USER-INPUT: derivative (unbiasedness) condition: `E_{θ₀}[Tφ] = α E_{θ₀}[T]`
    (hderiv : ∫ x, T x * φ x ∂(P θ₀) = α * ∫ x, T x ∂(P θ₀)) :
    IsUMPU P {θ₀} {θ ∈ Ξ | θ ≠ θ₀} α φ := by
  -- TODO: point-null two-sided UMPU. The boundary device `isUMPU_of_isUMP_on_boundary` reduces
  -- this to optimality among tests similar at `θ₀` and satisfying the derivative constraint
  -- `∫ T·ψ dP_{θ₀} = α ∫ T dP_{θ₀}`; the reject-outside test with `hsize`+`hderiv` is optimal by
  -- the two-constraint generalized Neyman–Pearson lemma. Requires: (a) `continuous_power_expFamily`
  -- (the analytic debt lifted in `PowerContinuity`) to run the boundary device, and (b) a
  -- generalized (two-constraint) NP optimality lemma not yet present in `NeymanPearson`. This is
  -- the one-parameter (`Ξ`-trivial-nuisance) specialization of `MultiparamUMPU.isUMPU_conditional_
  -- point`. Reported.
  sorry

/-- **UMP unbiased test of an interval null in a one-parameter exponential family.**

For `H : θ₁ ≤ θ ≤ θ₂` against `K : θ < θ₁ or θ > θ₂`, the same reject-outside-an-interval
test is UMP unbiased at level `α`, now with the constants pinned by the **two size
equations** `E_{θ₁}[φ] = E_{θ₂}[φ] = α` (the boundary of the testing problem consists of the
two points `θ₁, θ₂`, and unbiasedness with a continuous power function forces similarity
there). -/
theorem isUMPU_outside_interval_expFamily
    {P : ℝ → Measure 𝓧} {E : ExpFamily 𝓧 ℝ} {T : 𝓧 → ℝ} {Ξ : Set ℝ}
    {θ₁ θ₂ α C₁ C₂ γ₁ γ₂ : ℝ} {φ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; the model's standing setting
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- LEAN-ONLY: name for the natural statistic of the family
    (hT : T = E.stat)
    -- USER-INPUT: on the parameter set of interest the model is the canonical
    -- one-parameter exponential family `dP_θ = C(θ)e^{θT}dν`
    (hP : ∀ θ ∈ Ξ, P θ = E.P θ)
    -- USER-INPUT: the parameter set lies in the interior of the natural parameter set
    (hΞ : Ξ ⊆ interior E.natSet)
    -- USER-INPUT: the two null endpoints belong to the parameter set and are ordered
    (hθ₁ : θ₁ ∈ Ξ) (hθ₂ : θ₂ ∈ Ξ) (hθ : θ₁ < θ₂)
    -- LEAN-ONLY: the level is strictly interior to `[0,1]`; degenerate levels are excluded
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the two critical values are ordered
    (hC : C₁ ≤ C₂)
    -- USER-INPUT: the test is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: shape of the test — rejection outside the interval
    (hφ_one : ∀ x, T x < C₁ ∨ C₂ < T x → φ x = 1)
    -- USER-INPUT: shape of the test — acceptance strictly inside the interval
    (hφ_zero : ∀ x, C₁ < T x → T x < C₂ → φ x = 0)
    -- USER-INPUT: shape of the test — randomization at the lower critical value
    (hφ_γ₁ : ∀ x, T x = C₁ → φ x = γ₁)
    -- USER-INPUT: shape of the test — randomization at the upper critical value
    (hφ_γ₂ : ∀ x, T x = C₂ → φ x = γ₂)
    -- USER-INPUT: size condition at the lower endpoint
    (hsize₁ : power P φ θ₁ = α)
    -- USER-INPUT: size condition at the upper endpoint
    (hsize₂ : power P φ θ₂ = α) :
    IsUMPU P {θ ∈ Ξ | θ₁ ≤ θ ∧ θ ≤ θ₂} {θ ∈ Ξ | θ < θ₁ ∨ θ₂ < θ} α φ := by
  -- TODO: interval-null two-sided UMPU. Boundary `ωB = {θ₁, θ₂}`; the two size equations
  -- `hsize₁`, `hsize₂` pin the reject-outside test, optimal by the two-constraint generalized NP
  -- lemma among tests similar on `{θ₁, θ₂}`. Same requirements as `isUMPU_twoSided_expFamily`
  -- (`continuous_power_expFamily` + generalized NP); the one-parameter case of
  -- `MultiparamUMPU.isUMPU_conditional_outside`. Reported.
  sorry

end StatLean.HypothesisTesting
