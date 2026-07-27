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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.2 (One-Parameter Exponential Families), the UMP unbiased two-sided
tests of a one-parameter exponential family. (`TSH4 §4.2`.)

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

**⚠ BOTH THEOREMS BELOW ARE FALSE AS STATED — a missing hypothesis on `Ξ`.**
Nothing constrains `Ξ` beyond `Ξ ⊆ interior E.natSet`, so `Ξ` may be *sparse*: the null
value(s) need not be limit points of the alternative set `Θ₁`. When they are not,
unbiasedness imposes **no** equality constraint at the boundary (the boundary set
`closure Θ₀ ∩ closure Θ₁` of `PowerContinuity.isUMPU_of_isUMP_on_boundary` is empty), the
optimality problem degenerates to an ordinary one-sided Neyman–Pearson problem, and the
two-sided test loses to the one-sided one. Explicit counterexamples are recorded at each
theorem; both use the Gaussian location family `E.base = N(0,1)`, `E.stat = id`,
`E.P θ = N(θ,1)`, `natSet = ℝ`, `P θ = E.P θ` everywhere, `α = 0.05`.
The minimal repair is to require `Ξ` to be *open* (`IsOpen Ξ`), or more weakly to require
the null value(s) to lie in `closure Θ₁`; with `Ξ` open, `θ₀ ∈ closure (Ξ \ {θ₀})` and
`θ₁, θ₂ ∈ closure {θ ∈ Ξ | θ < θ₁ ∨ θ₂ < θ}`, which is exactly what the boundary device
consumes. The amendment is *not* applied here (public signatures are frozen for this pass);
it is reported so that a signature revision can be made deliberately. Note that the
amendment restores truth but does not by itself make the theorems provable from the current
stock — see the per-theorem `TODO`s for the remaining analytic bricks.

**Bibliographic comments.** UMP unbiased two-sided tests for exponential families are due to
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37), whose earlier fundamental
lemma ("On the problem of the most efficient tests of statistical hypotheses," *Phil. Trans.
R. Soc. A* **231** (1933), 289–337) supplies, in its multi-constraint form, the optimality
of tests subject to the two displayed side conditions.
-/

open MeasureTheory
open scoped InnerProductSpace

open StatLean.PointEstimation

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ## Analytic toolkit for the two repaired theorems

Everything in this section is `private`: it is the machinery the two amended statements
consume — σ-finiteness of the reference measure, the tilted representation of the power
function, integrability of `T·e^{θT}` at interior natural parameters, and the strict
convexity of `t ↦ e^{ct}` in the form of a *separating line* through two prescribed
abscissae. -/

/-- On `ℝ` the real inner product is multiplication. -/
private lemma inner_real (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp [Inner.inner, mul_comm]

/-- A measure carrying an integrable, everywhere strictly positive function is σ-finite:
the sets `{f > 1/(n+1)}` have finite measure by Markov and exhaust the space. -/
private lemma sigmaFinite_of_integrable_pos {μ : Measure 𝓧} {f : 𝓧 → ℝ}
    (hf : Integrable f μ) (hpos : ∀ x, 0 < f x) : SigmaFinite μ := by
  refine ⟨⟨⟨fun n => {x | (1 : ℝ) / (n + 1) < f x}, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · exact hf.measure_gt_lt_top (by positivity)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_one_div_lt (hpos x)

/-- The natural parameter set of a one-parameter family, spelled with multiplication. -/
private lemma integrable_exp_of_mem_natSet (E : ExpFamily 𝓧 ℝ) {θ : ℝ} (hθ : θ ∈ E.natSet) :
    Integrable (fun x => Real.exp (θ * E.stat x)) E.base := by
  simpa only [ExpFamily.natSet, Set.mem_setOf_eq, inner_real] using hθ

/-- **Tilted representation.** Every integral against the canonical member `P_θ` is the
ratio of the two exponential integrals against the reference measure. No integrability
hypothesis: both sides are junk-compatible. -/
private lemma integral_expFamily_eq (E : ExpFamily 𝓧 ℝ) (θ : ℝ) (g : 𝓧 → ℝ) :
    ∫ x, g x ∂(E.P θ)
      = (∫ x, g x * Real.exp (θ * E.stat x) ∂E.base)
        / ∫ x, Real.exp (θ * E.stat x) ∂E.base := by
  rw [ExpFamily.P, integral_tilted]
  simp only [inner_real, smul_eq_mul]
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **Integrability of `T·e^{θT}` at an interior natural parameter.** In one dimension the
`2^s` sign-vector envelope of the general theory is the two-point bound
`|t| ≤ δ⁻¹(e^{δt} + e^{-δt})`, valid because `u ≤ e^u`. -/
private lemma integrable_stat_mul_exp (E : ExpFamily 𝓧 ℝ) {θ : ℝ}
    (hθ : θ ∈ interior E.natSet) :
    Integrable (fun x => E.stat x * Real.exp (θ * E.stat x)) E.base := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior θ hθ
  have hmem : ∀ s : ℝ, |s| < ε → θ + s ∈ E.natSet := by
    intro s hs
    refine interior_subset (hball ?_)
    simpa [Real.dist_eq, abs_sub_comm] using hs
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδε : |δ| < ε := by rw [abs_of_pos hδ]; simp only [hδdef]; linarith
  have hp : Integrable (fun x => Real.exp ((θ + δ) * E.stat x)) E.base :=
    integrable_exp_of_mem_natSet E (hmem δ hδε)
  have hm : Integrable (fun x => Real.exp ((θ - δ) * E.stat x)) E.base := by
    have h := integrable_exp_of_mem_natSet E (hmem (-δ) (by rwa [abs_neg]))
    simpa only [← sub_eq_add_neg] using h
  have hdom : Integrable (fun x => (Real.exp ((θ + δ) * E.stat x)
      + Real.exp ((θ - δ) * E.stat x)) / δ) E.base := (hp.add hm).div_const δ
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (E.stat_meas.mul ((measurable_const.mul E.stat_meas).exp)).aestronglyMeasurable
  · set s := E.stat x with hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), le_div_iff₀ hδ]
    have h1 : δ * |s| ≤ Real.exp (δ * |s|) := by
      have := Real.add_one_le_exp (δ * |s|)
      linarith
    have h2 : Real.exp (δ * |s|) ≤ Real.exp (δ * s) + Real.exp (-(δ * s)) := by
      rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; linarith [Real.exp_pos (-(δ * s))]
      · rw [h, mul_neg]; linarith [Real.exp_pos (δ * s)]
    have hexp1 : Real.exp ((θ + δ) * s) = Real.exp (θ * s) * Real.exp (δ * s) := by
      rw [← Real.exp_add]; ring_nf
    have hexp2 : Real.exp ((θ - δ) * s) = Real.exp (θ * s) * Real.exp (-(δ * s)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp1, hexp2]
    have hE := Real.exp_pos (θ * s)
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hE.le]

/-- **Tangent-line form of the strict convexity of `t ↦ e^{ct}`** (`c ≠ 0`): the tangent at
`s` lies strictly below the graph at every other point. Immediate from `u + 1 < e^u`. -/
private lemma exp_tangent_lt {c : ℝ} (hc : c ≠ 0) {s t : ℝ} (h : t ≠ s) :
    Real.exp (c * s) * (1 + c * (t - s)) < Real.exp (c * t) := by
  have hu : c * (t - s) ≠ 0 := mul_ne_zero hc (sub_ne_zero.mpr h)
  have h1 := Real.add_one_lt_exp hu
  have hpos := Real.exp_pos (c * s)
  have hkey : Real.exp (c * s) * (1 + c * (t - s))
      < Real.exp (c * s) * Real.exp (c * (t - s)) := by nlinarith
  rwa [← Real.exp_add, show c * s + c * (t - s) = c * t by ring] at hkey

/-- **Strict convexity of `t ↦ e^{ct}`** (`c ≠ 0`), in two-point form. -/
private lemma exp_strictConvex {c : ℝ} (hc : c ≠ 0) {x y a b : ℝ} (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.exp (c * (a * x + b * y)) < a * Real.exp (c * x) + b * Real.exp (c * y) := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  set m := a * x + (1 - a) * y with hm
  have hmx : x ≠ m := by
    intro h
    have h0 : (1 - a) * (x - y) = 0 := by rw [hm] at h; linear_combination h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (ne_of_gt hb)
    · exact hxy (by linarith)
  have hmy : y ≠ m := by
    intro h
    have h0 : a * (y - x) = 0 := by rw [hm] at h; linear_combination h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (ne_of_gt ha)
    · exact hxy (by linarith)
  have h1 := exp_tangent_lt hc (s := m) (t := x) hmx
  have h2 := exp_tangent_lt hc (s := m) (t := y) hmy
  have hEq : a * (Real.exp (c * m) * (1 + c * (x - m)))
      + (1 - a) * (Real.exp (c * m) * (1 + c * (y - m))) = Real.exp (c * m) := by
    have hlin : a * (1 + c * (x - m)) + (1 - a) * (1 + c * (y - m)) = 1 := by
      rw [hm]; ring
    linear_combination Real.exp (c * m) * hlin
  have g1 := mul_lt_mul_of_pos_left h1 ha
  have g2 := mul_lt_mul_of_pos_left h2 hb
  linarith

/-- **Separating line.** For `c ≠ 0` and `C₁ ≤ C₂` there is an affine function agreeing with
`t ↦ e^{ct}` at `C₁` and `C₂` (the secant; the tangent when `C₁ = C₂`) which lies strictly
*below* the exponential outside `[C₁, C₂]` and strictly *above* it inside. This is the
one-dimensional geometric content of the two-multiplier Neyman–Pearson construction. -/
private lemma exists_sep_line {c : ℝ} (hc : c ≠ 0) {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) :
    ∃ A B : ℝ, A + B * C₁ = Real.exp (c * C₁) ∧ A + B * C₂ = Real.exp (c * C₂) ∧
      (∀ t, t < C₁ ∨ C₂ < t → A + B * t < Real.exp (c * t)) ∧
      (∀ t, C₁ < t → t < C₂ → Real.exp (c * t) < A + B * t) := by
  rcases eq_or_lt_of_le hC with heq | hlt
  · -- degenerate case `C₁ = C₂`: the tangent line at `C₁`
    subst heq
    refine ⟨Real.exp (c * C₁) * (1 - c * C₁), Real.exp (c * C₁) * c, by ring, by ring, ?_, ?_⟩
    · intro t ht
      have htne : t ≠ C₁ := by
        rcases ht with h | h
        · exact ne_of_lt h
        · exact ne_of_gt h
      have hkey := exp_tangent_lt hc (s := C₁) (t := t) htne
      have hre : Real.exp (c * C₁) * (1 - c * C₁) + Real.exp (c * C₁) * c * t
          = Real.exp (c * C₁) * (1 + c * (t - C₁)) := by ring
      rw [hre]; exact hkey
    · intro t h1 h2; linarith
  · -- generic case: the secant through `(C₁, e^{cC₁})` and `(C₂, e^{cC₂})`
    have hne : C₂ - C₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    obtain ⟨A, B, hAC₁, hAC₂⟩ : ∃ A B : ℝ, A + B * C₁ = Real.exp (c * C₁) ∧
        A + B * C₂ = Real.exp (c * C₂) := by
      refine ⟨Real.exp (c * C₁)
          - (Real.exp (c * C₂) - Real.exp (c * C₁)) / (C₂ - C₁) * C₁,
        (Real.exp (c * C₂) - Real.exp (c * C₁)) / (C₂ - C₁), by ring, ?_⟩
      field_simp
      ring
    refine ⟨A, B, hAC₁, hAC₂, ?_, ?_⟩
    · rintro t (ht | ht)
      · -- `t < C₁`: write `C₁` as a convex combination of `C₂` and `t`
        have hden : (0 : ℝ) < C₂ - t := by linarith
        have ha : 0 < (C₁ - t) / (C₂ - t) := div_pos (by linarith) hden
        have hb : 0 < (C₂ - C₁) / (C₂ - t) := div_pos (by linarith) hden
        have hab : (C₁ - t) / (C₂ - t) + (C₂ - C₁) / (C₂ - t) = 1 := by
          field_simp; ring
        have hcomb : (C₁ - t) / (C₂ - t) * C₂ + (C₂ - C₁) / (C₂ - t) * t = C₁ := by
          field_simp; ring
        have hcv := exp_strictConvex hc (x := C₂) (y := t)
          (ne_of_gt (lt_trans ht hlt)) ha hb hab
        rw [hcomb] at hcv
        have haff : (C₁ - t) / (C₂ - t) * (A + B * C₂)
            + (C₂ - C₁) / (C₂ - t) * (A + B * t) = A + B * C₁ := by
          field_simp; ring
        rw [hAC₁, hAC₂] at haff
        have hstep : (C₂ - C₁) / (C₂ - t) * (A + B * t)
            < (C₂ - C₁) / (C₂ - t) * Real.exp (c * t) := by linarith
        exact lt_of_mul_lt_mul_left hstep hb.le
      · -- `C₂ < t`: write `C₂` as a convex combination of `t` and `C₁`
        have hden : (0 : ℝ) < t - C₁ := by linarith
        have ha : 0 < (C₂ - C₁) / (t - C₁) := div_pos (by linarith) hden
        have hb : 0 < (t - C₂) / (t - C₁) := div_pos (by linarith) hden
        have hab : (C₂ - C₁) / (t - C₁) + (t - C₂) / (t - C₁) = 1 := by
          field_simp; ring
        have hcomb : (C₂ - C₁) / (t - C₁) * t + (t - C₂) / (t - C₁) * C₁ = C₂ := by
          field_simp; ring
        have hcv := exp_strictConvex hc (x := t) (y := C₁)
          (ne_of_gt (lt_trans hlt ht)) ha hb hab
        rw [hcomb] at hcv
        have haff : (C₂ - C₁) / (t - C₁) * (A + B * t)
            + (t - C₂) / (t - C₁) * (A + B * C₁) = A + B * C₂ := by
          field_simp; ring
        rw [hAC₁, hAC₂] at haff
        have hstep : (C₂ - C₁) / (t - C₁) * (A + B * t)
            < (C₂ - C₁) / (t - C₁) * Real.exp (c * t) := by linarith
        exact lt_of_mul_lt_mul_left hstep ha.le
    · intro t h1 h2
      have ha : 0 < (C₂ - t) / (C₂ - C₁) := div_pos (by linarith) (by linarith)
      have hb : 0 < (t - C₁) / (C₂ - C₁) := div_pos (by linarith) (by linarith)
      have hab : (C₂ - t) / (C₂ - C₁) + (t - C₁) / (C₂ - C₁) = 1 := by
        field_simp; ring
      have hcomb : (C₂ - t) / (C₂ - C₁) * C₁ + (t - C₁) / (C₂ - C₁) * C₂ = t := by
        field_simp; ring
      have hcv := exp_strictConvex hc (x := C₁) (y := C₂) (ne_of_lt hlt) ha hb hab
      rw [hcomb] at hcv
      have haff : (C₂ - t) / (C₂ - C₁) * (A + B * C₁)
          + (t - C₁) / (C₂ - C₁) * (A + B * C₂) = A + B * t := by
        field_simp; ring
      rw [hAC₁, hAC₂] at haff
      linarith

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
  -- FALSE AS STATED — verified counterexample (see the file header for the general diagnosis).
  -- Gaussian location family: `E.base = N(0,1)`, `E.stat = id`, so `E.P θ = N(θ,1)` and
  -- `E.natSet = interior E.natSet = ℝ`; put `P θ = E.P θ`, `α = 0.05`.
  -- Take the SPARSE parameter set `Ξ = {0, 2}` and `θ₀ = 0`, so `Θ₁ = {2}`.
  -- Take `C₁ = -1.959964`, `C₂ = 1.959964`, `γ₁ = γ₂ = 0`, `φ = 1{|x| > 1.959964}`.
  --   `hφ_one/hφ_zero/hφ_γ₁/hφ_γ₂` hold; `hsize`: `P₀(|X| > 1.959964) = 0.05 = α`;
  --   `hderiv`: `∫ x·φ dP₀ = 0` by symmetry and `α·∫ x dP₀ = 0.05·0 = 0`.
  -- All hypotheses hold. But the one-sided competitor `ψ = 1{x > 1.644854}` is a critical
  -- function that is UNBIASED at level `α` for this `Θ₀ = {0}`, `Θ₁ = {2}`:
  --   `power ψ 0 = 0.05 ≤ α` and `power ψ 2 = 0.638760 ≥ α`,
  -- while `power φ 2 = 0.516005 < 0.638760 = power ψ 2`, contradicting the optimality clause
  -- of `IsUMPU`. (With `Ξ` an interval around `0`, `ψ` would fail unbiasedness at negative
  -- `θ ∈ Θ₁`, where `power ψ θ < α`; sparseness of `Ξ` is exactly what breaks the theorem.)
  -- REPAIR: add `(hΞopen : IsOpen Ξ)`, which puts `θ₀ ∈ closure Θ₁` and makes the boundary
  -- device `isUMPU_of_isUMP_on_boundary` bite (its continuity input is now available from the
  -- closed `continuous_power_expFamily`, via `continuous_power_of_isCanonicalRepr`).
  -- STILL MISSING after the repair, so the `sorry` would remain:
  --  (a) the derivative constraint on competitors: unbiasedness makes `θ₀` an interior minimum
  --      of `power P ψ`, so `hasFDerivAt_integral_exp_inner` + `IsLocalMin.hasDerivAt_eq_zero`
  --      give `∫ T·ψ dP_{θ₀} = α ∫ T dP_{θ₀}`; not yet packaged for `power`;
  --  (b) the two-multiplier construction: `NeymanPearson.Generalized.isMax_of_multiplier_form`
  --      (m = 2, PROVED) supplies optimality once `HasMultiplierShape` is verified, which needs
  --      `k₁, k₂` solving `k₁e^{θ₀t} + k₂·t·e^{θ₀t} = e^{θ't}` at `t = C₁, C₂` together with the
  --      sign lemma "`(a + bt)e^{θ₀t} − e^{θ't}` has at most two zeros" (Rolle on the ratio);
  --      neither the solve nor the sign lemma exists in the repo.
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
  -- FALSE AS STATED — verified counterexample (see the file header for the general diagnosis).
  -- Same Gaussian location family `E.P θ = N(θ,1)`, `P θ = E.P θ`, `α = 0.05`.
  -- Take the SPARSE parameter set `Ξ = [0,1] ∪ {2}`, `θ₁ = 0`, `θ₂ = 1`, so
  -- `Θ₀ = [0,1]` and `Θ₁ = {2}` (note `θ₁, θ₂ ∉ closure Θ₁ = {2}`).
  -- Take `C₁ = -1.681477`, `C₂ = 2.681477`, `γ₁ = γ₂ = 0`, `φ = 1{x < C₁ ∨ x > C₂}`; by the
  -- reflection `x ↦ 1 − x` the interval is symmetric about `1/2`, so
  --   `hsize₁ : power φ 0 = 0.05 = α` and `hsize₂ : power φ 1 = 0.05 = α`.
  -- All hypotheses hold. But `ψ = 1{x > 2.644854}` is a critical function, UNBIASED at level
  -- `α`: `power ψ θ ≤ power ψ 1 = 0.05 ≤ α` for every `θ ∈ Θ₀ = [0,1]` (monotone in `θ`;
  -- e.g. `0.004086` at `0`, `0.015982` at `1/2`), and `power ψ 2 = 0.259511 ≥ α`.
  -- Yet `power φ 2 = 0.247901 < 0.259511 = power ψ 2`, contradicting the optimality clause of
  -- `IsUMPU`. (`power φ 1/2 = 0.029148 ≤ α`, so `φ`'s own level on `Θ₀` is not the issue.)
  -- REPAIR: add `(hΞopen : IsOpen Ξ)`, putting `θ₁, θ₂ ∈ closure Θ₁` so that unbiasedness
  -- forces similarity at both endpoints and the boundary device `isUMPU_of_isUMP_on_boundary`
  -- applies (`ωB = {θ₁, θ₂}`).
  -- STILL MISSING after the repair, so the `sorry` would remain:
  --  (a) `IsLevel P Θ₀ φ α`, i.e. `power φ θ ≤ α` for `θ₁ < θ < θ₂`. This is the
  --      variation-diminishing property of the exponential kernel: `φ − α` changes sign in the
  --      pattern `+,−,+` on the `T`-scale, so `θ ↦ ∫ (φ − α) dP_θ` has at most two zeros; they
  --      are `θ₁, θ₂` by `hsize₁/hsize₂`, and the middle sign is negative. Karlin total
  --      positivity; absent from the repo (`MLR/TwoSided.lean` has only the finite sign-change
  --      separation `twoSidedVal_sub_sep`, and its four headline theorems are all `sorry`).
  --  (b) the two-multiplier construction: `NeymanPearson.Generalized.isMax_of_multiplier_form`
  --      (m = 2, PROVED) closes optimality once `HasMultiplierShape` is verified for
  --      `f = (e^{θ₁t}, e^{θ₂t}, e^{θ'T})`, which needs `k₁, k₂` solving the 2×2 system
  --      `k₁e^{θ₁Cᵢ} + k₂e^{θ₂Cᵢ} = e^{θ'Cᵢ}` (`i = 1,2`; nonsingular iff `C₁ ≠ C₂`, so the
  --      `hC : C₁ ≤ C₂` tolerance needs the degenerate branch handled separately) plus the
  --      three-term sign lemma "`k₁e^{θ₁t} + k₂e^{θ₂t} − e^{θ't}` has at most two zeros"
  --      (Rolle after dividing by `e^{θ₁t}`). Neither exists in the repo.
  sorry

end StatLean.HypothesisTesting
