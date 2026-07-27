import StatLean.HypothesisTesting.NeymanPearson.Generalized
import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.Unbiased.PowerContinuity
import StatLean.PointEstimation.ExponentialFamily.Defs
import StatLean.PointEstimation.ExponentialFamily.Smoothness

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

/-- **Positivity of the partition integral.** If the member `P θ` is a probability measure
then `∫ e^{θT} dν > 0`: otherwise the tilted representation would read `1 = 0/0`. -/
private lemma partition_pos (E : ExpFamily 𝓧 ℝ) {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {Ξ : Set ℝ}
    (hP : ∀ θ ∈ Ξ, P θ = E.P θ) {θ : ℝ} (hθ : θ ∈ Ξ) :
    0 < ∫ x, Real.exp (θ * E.stat x) ∂E.base := by
  have hnn : (0 : ℝ) ≤ ∫ x, Real.exp (θ * E.stat x) ∂E.base :=
    integral_nonneg fun x => (Real.exp_pos _).le
  rcases eq_or_lt_of_le hnn with h | h
  · exfalso
    have h1 : ∫ _x, (1 : ℝ) ∂(E.P θ) = 1 := by
      rw [← hP θ hθ]; simp
    have h2 := integral_expFamily_eq E θ (fun _ => (1 : ℝ))
    rw [h1, ← h] at h2
    simp at h2
  · exact h

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

/-- **Chord separation for a convex function on `[0,∞)`.** Given `0 < w₁ ≤ w₂` and a
supporting line at `w₁` (used only in the degenerate case `w₁ = w₂`), the secant through
`(w₁, G w₁)` and `(w₂, G w₂)` dominates `G` on `[w₁, w₂]` and is dominated by `G` outside. -/
private lemma exists_chord_of_convexOn {G : ℝ → ℝ} (hG : ConvexOn ℝ (Set.Ici (0 : ℝ)) G)
    {w₁ w₂ : ℝ} (h1 : 0 < w₁) (h12 : w₁ ≤ w₂)
    (hsupp : ∃ b : ℝ, ∀ w, 0 ≤ w → G w₁ + b * (w - w₁) ≤ G w) :
    ∃ a b : ℝ, (∀ w, w₁ ≤ w → w ≤ w₂ → G w ≤ a + b * w) ∧
      (∀ w, 0 ≤ w → (w ≤ w₁ ∨ w₂ ≤ w) → a + b * w ≤ G w) := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · obtain ⟨b, hb⟩ := hsupp
    refine ⟨G w₁ - b * w₁, b, ?_, ?_⟩
    · intro w hw1 hw2
      have hww : w = w₁ := le_antisymm hw2 hw1
      subst hww
      linarith
    · intro w hw _
      have := hb w hw
      linarith
  · have hne : w₂ - w₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    obtain ⟨a, b, hA1, hA2⟩ : ∃ a b : ℝ, a + b * w₁ = G w₁ ∧ a + b * w₂ = G w₂ := by
      refine ⟨G w₁ - ((G w₂ - G w₁) / (w₂ - w₁)) * w₁, (G w₂ - G w₁) / (w₂ - w₁), by ring, ?_⟩
      field_simp
      ring
    have hcvx : ∀ x y u v : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → u + v = 1 →
        G (u * x + v * y) ≤ u * G x + v * G y := by
      intro x y u v hx hy hu hv huv
      simpa using hG.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hu hv huv
    refine ⟨a, b, ?_, ?_⟩
    · intro w hw1 hw2
      have hu : 0 ≤ (w₂ - w) / (w₂ - w₁) := div_nonneg (by linarith) (by linarith)
      have hv : 0 ≤ (w - w₁) / (w₂ - w₁) := div_nonneg (by linarith) (by linarith)
      have huv : (w₂ - w) / (w₂ - w₁) + (w - w₁) / (w₂ - w₁) = 1 := by field_simp; ring
      have hcomb : (w₂ - w) / (w₂ - w₁) * w₁ + (w - w₁) / (w₂ - w₁) * w₂ = w := by
        field_simp; ring
      have h := hcvx w₁ w₂ _ _ h1.le (by linarith) hu hv huv
      rw [hcomb] at h
      have haff : (w₂ - w) / (w₂ - w₁) * (a + b * w₁) + (w - w₁) / (w₂ - w₁) * (a + b * w₂)
          = a + b * w := by field_simp; ring
      rw [hA1, hA2] at haff
      linarith
    · rintro w hw (hc | hc)
      · -- `w ≤ w₁`: write `w₁` as a convex combination of `w₂` and `w`
        have hden : (0 : ℝ) < w₂ - w := by linarith
        have hu : 0 ≤ (w₁ - w) / (w₂ - w) := div_nonneg (by linarith) (by linarith)
        have hv : 0 < (w₂ - w₁) / (w₂ - w) := div_pos (by linarith) hden
        have huv : (w₁ - w) / (w₂ - w) + (w₂ - w₁) / (w₂ - w) = 1 := by field_simp; ring
        have hcomb : (w₁ - w) / (w₂ - w) * w₂ + (w₂ - w₁) / (w₂ - w) * w = w₁ := by
          field_simp; ring
        have h := hcvx w₂ w ((w₁ - w) / (w₂ - w)) ((w₂ - w₁) / (w₂ - w)) (by linarith) hw hu
          hv.le huv
        rw [hcomb] at h
        have haff : (w₁ - w) / (w₂ - w) * (a + b * w₂) + (w₂ - w₁) / (w₂ - w) * (a + b * w)
            = a + b * w₁ := by field_simp; ring
        rw [hA1, hA2] at haff
        have hstep : (w₂ - w₁) / (w₂ - w) * (a + b * w) ≤ (w₂ - w₁) / (w₂ - w) * G w := by
          linarith
        exact le_of_mul_le_mul_left hstep hv
      · -- `w₂ ≤ w`: write `w₂` as a convex combination of `w` and `w₁`
        have hden : (0 : ℝ) < w - w₁ := by linarith
        have hu : 0 < (w₂ - w₁) / (w - w₁) := div_pos (by linarith) hden
        have hv : 0 ≤ (w - w₂) / (w - w₁) := div_nonneg (by linarith) (by linarith)
        have huv : (w₂ - w₁) / (w - w₁) + (w - w₂) / (w - w₁) = 1 := by field_simp; ring
        have hcomb : (w₂ - w₁) / (w - w₁) * w + (w - w₂) / (w - w₁) * w₁ = w₂ := by
          field_simp; ring
        have h := hcvx w w₁ ((w₂ - w₁) / (w - w₁)) ((w - w₂) / (w - w₁)) hw h1.le hu.le hv huv
        rw [hcomb] at h
        have haff : (w₂ - w₁) / (w - w₁) * (a + b * w) + (w - w₂) / (w - w₁) * (a + b * w₁)
            = a + b * w₂ := by field_simp; ring
        rw [hA1, hA2] at haff
        have hstep : (w₂ - w₁) / (w - w₁) * (a + b * w) ≤ (w₂ - w₁) / (w - w₁) * G w := by
          linarith
        exact le_of_mul_le_mul_left hstep hu

/-- The concave companion of `exists_chord_of_convexOn`, by negation. -/
private lemma exists_chord_of_concaveOn {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ)) G)
    {w₁ w₂ : ℝ} (h1 : 0 < w₁) (h12 : w₁ ≤ w₂)
    (hsupp : ∃ b : ℝ, ∀ w, 0 ≤ w → G w ≤ G w₁ + b * (w - w₁)) :
    ∃ a b : ℝ, (∀ w, w₁ ≤ w → w ≤ w₂ → a + b * w ≤ G w) ∧
      (∀ w, 0 ≤ w → (w ≤ w₁ ∨ w₂ ≤ w) → G w ≤ a + b * w) := by
  have hsupp' : ∃ b : ℝ, ∀ w, 0 ≤ w → (-G) w₁ + b * (w - w₁) ≤ (-G) w := by
    obtain ⟨b, hb⟩ := hsupp
    refine ⟨-b, fun w hw => ?_⟩
    have := hb w hw
    simp only [Pi.neg_apply]
    linarith
  obtain ⟨a, b, hin, hout⟩ := exists_chord_of_convexOn hG.neg h1 h12 hsupp'
  refine ⟨-a, -b, fun w hw1 hw2 => ?_, fun w hw hc => ?_⟩
  · have := hin w hw1 hw2
    simp only [Pi.neg_apply] at this
    linarith
  · have := hout w hw hc
    simp only [Pi.neg_apply] at this
    linarith

/-- **Two-constraint Neyman–Pearson comparison, unpacked.** The `Fin`-indexed
`isMax_of_multiplier_form` at `m = 2`, restated with the three functions spelled out. -/
private lemma np_two_compare (μ : Measure 𝓧) [SigmaFinite μ] {g₀ g₁ g₂ : 𝓧 → ℝ}
    (hm₀ : Measurable g₀) (hm₁ : Measurable g₁) (hm₂ : Measurable g₂)
    (hi₀ : Integrable g₀ μ) (hi₁ : Integrable g₁ μ) (hi₂ : Integrable g₂ μ)
    {c₀ c₁ k₀ k₁ : ℝ} {φ ψ : 𝓧 → ℝ} (hφ : IsCriticalFn φ) (hψ : IsCriticalFn ψ)
    (hφ₀ : ∫ x, φ x * g₀ x ∂μ = c₀) (hφ₁ : ∫ x, φ x * g₁ x ∂μ = c₁)
    (hψ₀ : ∫ x, ψ x * g₀ x ∂μ = c₀) (hψ₁ : ∫ x, ψ x * g₁ x ∂μ = c₁)
    (hs₁ : ∀ x, k₀ * g₀ x + k₁ * g₁ x < g₂ x → φ x = 1)
    (hs₀ : ∀ x, g₂ x < k₀ * g₀ x + k₁ * g₁ x → φ x = 0) :
    ∫ x, ψ x * g₂ x ∂μ ≤ ∫ x, φ x * g₂ x ∂μ := by
  have hmeas : ∀ i : Fin 3, Measurable ((![g₀, g₁, g₂] : Fin 3 → 𝓧 → ℝ) i) := by
    intro i; fin_cases i <;> simpa
  have hint : ∀ i : Fin 3, Integrable ((![g₀, g₁, g₂] : Fin 3 → 𝓧 → ℝ) i) μ := by
    intro i; fin_cases i <;> simpa
  have hconφ : ∀ i : Fin 2,
      ∫ x, φ x * (![g₀, g₁, g₂] : Fin 3 → 𝓧 → ℝ) i.castSucc x ∂μ
        = (![c₀, c₁] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simpa
  have hconψ : ∀ i : Fin 2,
      ∫ x, ψ x * (![g₀, g₁, g₂] : Fin 3 → 𝓧 → ℝ) i.castSucc x ∂μ
        = (![c₀, c₁] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simpa
  have hshape : HasMultiplierShape μ (![g₀, g₁, g₂] : Fin 3 → 𝓧 → ℝ) ![k₀, k₁] φ := by
    constructor
    · refine Filter.Eventually.of_forall fun x hx => hs₁ x ?_
      simpa [Fin.sum_univ_two] using hx
    · refine Filter.Eventually.of_forall fun x hx => hs₀ x ?_
      simpa [Fin.sum_univ_two] using hx
  have key := isMax_of_multiplier_form (m := 2) μ hmeas hint hφ hconφ hshape ψ hψ hconψ
  simpa using key

/-- **Unbiasedness forces the two side conditions at an interior null value.**

If `ψ` has power at most `α` at `θ₀` and at least `α` at every other parameter of the *open*
set `Ξ`, then its power function — an analytic ratio of exponential integrals — attains a
local minimum at `θ₀`; continuity upgrades the level inequality to equality, and vanishing of
the derivative is exactly `E_{θ₀}[Tψ] = α·E_{θ₀}[T]`. -/
private lemma unbiased_side_conditions (E : ExpFamily 𝓧 ℝ) {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {Ξ : Set ℝ} {θ₀ α : ℝ} {ψ : 𝓧 → ℝ}
    (hP : ∀ θ ∈ Ξ, P θ = E.P θ) (hΞ : Ξ ⊆ interior E.natSet) (hΞopen : IsOpen Ξ)
    (hθ₀ : θ₀ ∈ Ξ) (hψ : IsCriticalFn ψ)
    (hle : ∫ x, ψ x ∂(P θ₀) ≤ α)
    (hge : ∀ θ ∈ Ξ, θ ≠ θ₀ → α ≤ ∫ x, ψ x ∂(P θ)) :
    ∫ x, ψ x ∂(P θ₀) = α ∧
      ∫ x, E.stat x * ψ x ∂(P θ₀) = α * ∫ x, E.stat x ∂(P θ₀) := by
  -- the two exponential integrals and their ratio
  set nu : ℝ → ℝ := fun θ => ∫ x, ψ x * Real.exp (θ * E.stat x) ∂E.base with hnu
  set de : ℝ → ℝ := fun θ => ∫ x, Real.exp (θ * E.stat x) ∂E.base with hde
  have hBeq : ∀ θ ∈ Ξ, nu θ / de θ = ∫ x, ψ x ∂(P θ) := by
    intro θ hθ
    rw [hP θ hθ, integral_expFamily_eq E θ ψ]
  have hd₀ : 0 < de θ₀ := partition_pos E hP hθ₀
  -- the inner product on `ℝ` is multiplication; the differential is a `smulRight`
  have hclm : ∀ v : ℝ, (innerSL ℝ v : ℝ →L[ℝ] ℝ)
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v := by
    intro v
    ext w
    simp only [innerSL_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, inner_real]
    ring
  -- `|ψ| ≤ 1` puts the natural set inside the `ψ`-weighted one
  have hwsub : E.natSet ⊆ E.weightedNatSet ψ := by
    intro η hη
    refine (hη : Integrable _ _).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hψ.1.abs.aestronglyMeasurable).mul
        ((((innerSL ℝ η).continuous.measurable.comp E.stat_meas)).exp.aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc |ψ x| * Real.exp ⟪η, E.stat x⟫_ℝ ≤ 1 * Real.exp ⟪η, E.stat x⟫_ℝ := by
            gcongr
            rw [abs_of_nonneg (hψ.2 x).1]; exact (hψ.2 x).2
        _ = Real.exp ⟪η, E.stat x⟫_ℝ := one_mul _
  have hwone : E.weightedNatSet (fun _ : 𝓧 => (1 : ℝ)) = E.natSet := by
    ext η; simp [ExpFamily.weightedNatSet, ExpFamily.natSet]
  -- differentiability of numerator and denominator at `θ₀`
  have hnu' : HasDerivAt nu (∫ x, ψ x * Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) θ₀ := by
    have hfd := E.hasFDerivAt_integral_exp_inner hψ.1 (interior_mono hwsub (hΞ hθ₀))
    rw [hclm] at hfd
    have h := hasDerivAt_iff_hasFDerivAt.mpr hfd
    simpa only [inner_real, smul_eq_mul] using h
  have hde' : HasDerivAt de (∫ x, Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) θ₀ := by
    have hmem : θ₀ ∈ interior (E.weightedNatSet fun _ : 𝓧 => (1 : ℝ)) := by
      rw [hwone]; exact hΞ hθ₀
    have hfd := E.hasFDerivAt_integral_exp_inner (f := fun _ : 𝓧 => (1 : ℝ))
      measurable_const hmem
    rw [hclm] at hfd
    have h := hasDerivAt_iff_hasFDerivAt.mpr hfd
    simpa only [inner_real, smul_eq_mul, one_mul] using h
  have hB' : HasDerivAt (fun θ => nu θ / de θ)
      (((∫ x, ψ x * Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) * de θ₀
        - nu θ₀ * ∫ x, Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) / de θ₀ ^ 2) θ₀ :=
    hnu'.div hde' (ne_of_gt hd₀)
  -- the power function has a local minimum at `θ₀`
  have hmin : IsLocalMin (fun θ => nu θ / de θ) θ₀ := by
    filter_upwards [hΞopen.mem_nhds hθ₀] with θ hθ
    rcases eq_or_ne θ θ₀ with rfl | hne
    · exact le_rfl
    · rw [hBeq θ hθ, hBeq θ₀ hθ₀]
      exact le_trans hle (hge θ hθ hne)
  have hzero := hmin.hasDerivAt_eq_zero hB'
  -- continuity plus non-isolation of `θ₀` upgrades the level inequality to equality
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΞopen θ₀ hθ₀
  have hsmall : ∀ n : ℕ, (0 : ℝ) < ε / 2 * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  have hseqmem : ∀ n : ℕ, θ₀ + ε / 2 * (1 / ((n : ℝ) + 1)) ∈ Ξ := by
    intro n
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (hsmall n)]
    have hb : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith [hsmall n]
  have htend : Filter.Tendsto (fun n : ℕ => θ₀ + ε / 2 * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds θ₀) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε / 2)
    simpa using Filter.Tendsto.const_add θ₀ h0
  have hlim := (hB'.continuousAt.tendsto).comp htend
  have hval : α ≤ nu θ₀ / de θ₀ := by
    refine ge_of_tendsto' hlim fun n => ?_
    rw [Function.comp_apply, hBeq _ (hseqmem n)]
    refine hge _ (hseqmem n) fun h => ?_
    have := hsmall n
    linarith [h]
  have hsize : nu θ₀ / de θ₀ = α := by
    rw [hBeq θ₀ hθ₀] at hval ⊢
    exact le_antisymm hle hval
  refine ⟨by rw [← hBeq θ₀ hθ₀]; exact hsize, ?_⟩
  -- unwind the vanishing derivative
  have hnum : nu θ₀ = α * de θ₀ := by
    rwa [div_eq_iff (ne_of_gt hd₀)] at hsize
  have hkey : (∫ x, ψ x * Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base)
      = α * ∫ x, Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base := by
    have hd2 : de θ₀ ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hd₀)
    rcases div_eq_zero_iff.mp hzero with h | h
    · rw [hnum] at h
      have h2 : de θ₀ * ((∫ x, ψ x * Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base)
          - α * ∫ x, Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (ne_of_gt hd₀)
      · linarith
    · exact absurd h hd2
  -- rewrite both sides as integrals against `P θ₀`
  have hL : ∫ x, E.stat x * ψ x ∂(P θ₀)
      = (∫ x, ψ x * Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) / de θ₀ := by
    rw [hP θ₀ hθ₀, integral_expFamily_eq E θ₀ (fun x => E.stat x * ψ x)]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x, E.stat x ∂(P θ₀)
      = (∫ x, Real.exp (θ₀ * E.stat x) * E.stat x ∂E.base) / de θ₀ := by
    rw [hP θ₀ hθ₀, integral_expFamily_eq E θ₀ (fun x => E.stat x)]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hL, hR, hkey, mul_div_assoc]

/-- **The two-multiplier comparison for the point-null problem.**

Against the reference measure `ν` the three Neyman–Pearson data are the `θ₀`-density, the
`θ₀`-density weighted by `T`, and the `θ'`-density. The separating line of `exists_sep_line`
for `c = θ' − θ₀` supplies the multipliers: the rejection region `{T < C₁} ∪ {T > C₂}` is
exactly where the `θ'`-density exceeds the affine combination. -/
private lemma expFamily_np_compare (E : ExpFamily 𝓧 ℝ) {P : ℝ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {Ξ : Set ℝ} {θ₀ θ' α C₁ C₂ : ℝ} {φ ψ : 𝓧 → ℝ}
    (hP : ∀ θ ∈ Ξ, P θ = E.P θ) (hΞ : Ξ ⊆ interior E.natSet)
    (hθ₀ : θ₀ ∈ Ξ) (hθ' : θ' ∈ Ξ) (hne : θ' ≠ θ₀) (hC : C₁ ≤ C₂)
    (hφ : IsCriticalFn φ) (hψ : IsCriticalFn ψ)
    (hφ_one : ∀ x, E.stat x < C₁ ∨ C₂ < E.stat x → φ x = 1)
    (hφ_zero : ∀ x, C₁ < E.stat x → E.stat x < C₂ → φ x = 0)
    (hφ0 : ∫ x, φ x ∂(P θ₀) = α) (hψ0 : ∫ x, ψ x ∂(P θ₀) = α)
    (hφ1 : ∫ x, E.stat x * φ x ∂(P θ₀) = α * ∫ x, E.stat x ∂(P θ₀))
    (hψ1 : ∫ x, E.stat x * ψ x ∂(P θ₀) = α * ∫ x, E.stat x ∂(P θ₀)) :
    ∫ x, ψ x ∂(P θ') ≤ ∫ x, φ x ∂(P θ') := by
  set d₀ : ℝ := ∫ x, Real.exp (θ₀ * E.stat x) ∂E.base with hd₀def
  set d' : ℝ := ∫ x, Real.exp (θ' * E.stat x) ∂E.base with hd'def
  have hd₀ : 0 < d₀ := partition_pos E hP hθ₀
  have hd' : 0 < d' := partition_pos E hP hθ'
  have hie₀ : Integrable (fun x => Real.exp (θ₀ * E.stat x)) E.base :=
    integrable_exp_of_mem_natSet E (interior_subset (hΞ hθ₀))
  have hie' : Integrable (fun x => Real.exp (θ' * E.stat x)) E.base :=
    integrable_exp_of_mem_natSet E (interior_subset (hΞ hθ'))
  haveI : SigmaFinite E.base := sigmaFinite_of_integrable_pos hie₀ fun x => Real.exp_pos _
  -- the three densities
  set g₀ : 𝓧 → ℝ := fun x => Real.exp (θ₀ * E.stat x) / d₀ with hg₀
  set g₁ : 𝓧 → ℝ := fun x => E.stat x * Real.exp (θ₀ * E.stat x) / d₀ with hg₁
  set g₂ : 𝓧 → ℝ := fun x => Real.exp (θ' * E.stat x) / d' with hg₂
  have hm₀ : Measurable g₀ :=
    ((measurable_const.mul E.stat_meas).exp).div_const _
  have hm₁ : Measurable g₁ :=
    (E.stat_meas.mul ((measurable_const.mul E.stat_meas).exp)).div_const _
  have hm₂ : Measurable g₂ :=
    ((measurable_const.mul E.stat_meas).exp).div_const _
  have hi₀ : Integrable g₀ E.base := hie₀.div_const _
  have hi₁ : Integrable g₁ E.base := (integrable_stat_mul_exp E (hΞ hθ₀)).div_const _
  have hi₂ : Integrable g₂ E.base := hie'.div_const _
  -- the three constraint/objective functionals, in terms of the model measures
  have hpull₀ : ∀ g : 𝓧 → ℝ, ∫ x, g x * g₀ x ∂E.base = ∫ x, g x ∂(P θ₀) := by
    intro g
    rw [hP θ₀ hθ₀, integral_expFamily_eq E θ₀ g, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [hg₀]; ring)
  have hpull₂ : ∀ g : 𝓧 → ℝ, ∫ x, g x * g₂ x ∂E.base = ∫ x, g x ∂(P θ') := by
    intro g
    rw [hP θ' hθ', integral_expFamily_eq E θ' g, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [hg₂]; ring)
  have hpull₁ : ∀ g : 𝓧 → ℝ,
      ∫ x, g x * g₁ x ∂E.base = ∫ x, E.stat x * g x ∂(P θ₀) := by
    intro g
    rw [hP θ₀ hθ₀, integral_expFamily_eq E θ₀ (fun x => E.stat x * g x), ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [hg₁]; ring)
  -- the separating line and the induced multipliers
  obtain ⟨A, B, hA1, hA2, hout, hin⟩ :=
    exists_sep_line (c := θ' - θ₀) (sub_ne_zero.mpr hne) hC
  have hL : ∀ x, (A * d₀ / d') * g₀ x + (B * d₀ / d') * g₁ x
      = (A + B * E.stat x) * Real.exp (θ₀ * E.stat x) / d' := by
    intro x
    rw [hg₀, hg₁]
    field_simp
  have hR : ∀ x, g₂ x
      = Real.exp ((θ' - θ₀) * E.stat x) * Real.exp (θ₀ * E.stat x) / d' := by
    intro x
    have h : Real.exp ((θ' - θ₀) * E.stat x) * Real.exp (θ₀ * E.stat x)
        = Real.exp (θ' * E.stat x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hg₂, h]
  have hiff : ∀ x, ((A * d₀ / d') * g₀ x + (B * d₀ / d') * g₁ x < g₂ x
      ↔ A + B * E.stat x < Real.exp ((θ' - θ₀) * E.stat x)) := by
    intro x
    rw [hL, hR, div_lt_div_iff_of_pos_right hd', mul_lt_mul_iff_of_pos_right (Real.exp_pos _)]
  have hiff' : ∀ x, (g₂ x < (A * d₀ / d') * g₀ x + (B * d₀ / d') * g₁ x
      ↔ Real.exp ((θ' - θ₀) * E.stat x) < A + B * E.stat x) := by
    intro x
    rw [hL, hR, div_lt_div_iff_of_pos_right hd', mul_lt_mul_iff_of_pos_right (Real.exp_pos _)]
  -- the multiplier shape is the shape hypothesis on `φ`
  have hs₁ : ∀ x, (A * d₀ / d') * g₀ x + (B * d₀ / d') * g₁ x < g₂ x → φ x = 1 := by
    intro x hx
    have h := (hiff x).mp hx
    refine hφ_one x ?_
    rcases lt_trichotomy (E.stat x) C₁ with h1 | h1 | h1
    · exact Or.inl h1
    · exfalso; rw [h1] at h; linarith [hA1]
    · rcases lt_trichotomy (E.stat x) C₂ with h2 | h2 | h2
      · exact absurd (hin _ h1 h2) (not_lt.mpr h.le)
      · exfalso; rw [h2] at h; linarith [hA2]
      · exact Or.inr h2
  have hs₀ : ∀ x, g₂ x < (A * d₀ / d') * g₀ x + (B * d₀ / d') * g₁ x → φ x = 0 := by
    intro x hx
    have h := (hiff' x).mp hx
    refine hφ_zero x ?_ ?_
    · rcases lt_trichotomy (E.stat x) C₁ with h1 | h1 | h1
      · exact absurd (hout _ (Or.inl h1)) (not_lt.mpr h.le)
      · exfalso; rw [h1] at h; linarith [hA1]
      · exact h1
    · rcases lt_trichotomy (E.stat x) C₂ with h2 | h2 | h2
      · exact h2
      · exfalso; rw [h2] at h; linarith [hA2]
      · exact absurd (hout _ (Or.inr h2)) (not_lt.mpr h.le)
  have key := np_two_compare E.base hm₀ hm₁ hm₂ hi₀ hi₁ hi₂ (c₀ := α)
    (c₁ := α * ∫ x, E.stat x ∂(P θ₀)) hφ hψ
    (by rw [hpull₀]; exact hφ0) (by rw [hpull₁]; exact hφ1)
    (by rw [hpull₀]; exact hψ0) (by rw [hpull₁]; exact hψ1) hs₁ hs₀
  rwa [hpull₂, hpull₂] at key

/-- **UMP unbiased test of a point null in a one-parameter exponential family.**

For `H : θ = θ₀` against `K : θ ≠ θ₀`, the test rejecting outside `[C₁, C₂]` on the natural
statistic scale is UMP unbiased at level `α`, provided the constants satisfy **both**

* the size condition `E_{θ₀}[φ] = α`, and
* the derivative condition `E_{θ₀}[T·φ] = α·E_{θ₀}[T]`

(the latter being the analytic form of "the power function has a minimum at `θ₀`").

**FLAGGED SIGNATURE AMENDMENT — `(hΞopen : IsOpen Ξ)` was added.** Without it the statement
is FALSE, by the following verified counterexample. Gaussian location family
`E.base = N(0,1)`, `E.stat = id`, so `E.P θ = N(θ,1)` and `E.natSet = interior E.natSet = ℝ`;
put `P θ = E.P θ`, `α = 0.05`. Take the SPARSE parameter set `Ξ = {0, 2}` and `θ₀ = 0`, so
`Θ₁ = {2}`. Take `C₁ = -1.959964`, `C₂ = 1.959964`, `γ₁ = γ₂ = 0`,
`φ = 1{|x| > 1.959964}`. Then `hφ_one/hφ_zero/hφ_γ₁/hφ_γ₂` hold, `hsize` holds
(`P₀(|X| > 1.959964) = 0.05 = α`) and `hderiv` holds (`∫ x·φ dP₀ = 0` by symmetry, while
`α·∫ x dP₀ = 0.05·0 = 0`). Yet the one-sided competitor `ψ = 1{x > 1.644854}` is a critical
function which is *unbiased* at level `α` for `Θ₀ = {0}`, `Θ₁ = {2}` (`power ψ 0 = 0.05 ≤ α`
and `power ψ 2 = 0.638760 ≥ α`), while `power φ 2 = 0.516005 < 0.638760 = power ψ 2`,
contradicting the optimality clause of `IsUMPU`. The defect is sparseness of `Ξ`: the null
value need not be a limit point of the alternative set, so unbiasedness imposes no equality
constraint at `θ₀` and the two-sided problem degenerates to a one-sided one. Openness of `Ξ`
is the minimal repair; it is what the classical statement means by "`θ` ranges over an
interval interior to the natural parameter set", and it is exactly what the proof consumes,
in two places: `θ₀` is not isolated in `Ξ` (so continuity of the power function upgrades
`power ψ θ₀ ≤ α` to `= α`) and `θ₀` is an *interior* minimum of the power function of any
unbiased test (so its derivative vanishes there).

**Proof.** Both side conditions are, for any unbiased competitor, forced
(`unbiased_side_conditions`); the displayed pair is then exactly the constraint set of the
two-constraint Neyman–Pearson lemma `isMax_of_multiplier_form`, whose multiplier shape is
supplied by the secant/tangent line of `exists_sep_line` for the strictly convex function
`t ↦ e^{(θ' − θ₀)t}` (`expFamily_np_compare`). Unbiasedness of `φ` itself is the comparison
with the constant test `α`, which satisfies both side conditions. -/
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
    -- USER-INPUT (AMENDMENT): the parameter set is open. Without it the statement is FALSE:
    -- see the counterexample in the docstring above
    (hΞopen : IsOpen Ξ)
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
  subst hT
  have hconstα : IsCriticalFn (fun _ : 𝓧 => α) :=
    ⟨measurable_const, fun _ => ⟨hα₀.le, hα₁.le⟩⟩
  have hconst0 : ∫ _x, (α : ℝ) ∂(P θ₀) = α := by simp
  have hconst1 : ∫ x, E.stat x * (α : ℝ) ∂(P θ₀) = α * ∫ x, E.stat x ∂(P θ₀) := by
    rw [integral_mul_const, mul_comm]
  -- the two-multiplier comparison, once and for all
  have hcmp : ∀ θ' ∈ Ξ, θ' ≠ θ₀ → ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ →
      ∫ x, ψ x ∂(P θ₀) = α → ∫ x, E.stat x * ψ x ∂(P θ₀) = α * ∫ x, E.stat x ∂(P θ₀) →
      ∫ x, ψ x ∂(P θ') ≤ ∫ x, φ x ∂(P θ') := fun θ' hθ' hne ψ hψ h0 h1 =>
    expFamily_np_compare E hP hΞ hθ₀ hθ' hne hC hφ hψ hφ_one hφ_zero hsize h0 hderiv h1
  refine ⟨hφ, ⟨?_, ?_⟩, ?_⟩
  · -- level: the null set is the single point `θ₀`, where the size condition is exact
    intro θ hθ
    rw [Set.mem_singleton_iff.mp hθ]
    exact le_of_eq hsize
  · -- unbiasedness: the constant test `α` satisfies both side conditions
    rintro θ' ⟨hθ'Ξ, hθ'ne⟩
    have h := hcmp θ' hθ'Ξ hθ'ne (fun _ => α) hconstα hconst0 hconst1
    simp only [power]
    calc α = ∫ _x, (α : ℝ) ∂(P θ') := by simp
      _ ≤ ∫ x, φ x ∂(P θ') := h
  · -- optimality: every unbiased competitor satisfies both side conditions
    rintro ψ hψ hunb θ' ⟨hθ'Ξ, hθ'ne⟩
    obtain ⟨h0, h1⟩ := unbiased_side_conditions E hP hΞ hΞopen hθ₀ hψ
      (hunb.1 θ₀ rfl) (fun θ hθ hne => hunb.2 θ ⟨hθ, hne⟩)
    exact hcmp θ' hθ'Ξ hθ'ne ψ hψ h0 h1

/-- **UMP unbiased test of an interval null in a one-parameter exponential family.**

For `H : θ₁ ≤ θ ≤ θ₂` against `K : θ < θ₁ or θ > θ₂`, the same reject-outside-an-interval
test is UMP unbiased at level `α`, now with the constants pinned by the **two size
equations** `E_{θ₁}[φ] = E_{θ₂}[φ] = α` (the boundary of the testing problem consists of the
two points `θ₁, θ₂`, and unbiasedness with a continuous power function forces similarity
there).

**FLAGGED SIGNATURE AMENDMENT — `(hΞopen : IsOpen Ξ)` was added.** Without it the statement
is FALSE, by the following verified counterexample. Gaussian location family
`E.P θ = N(θ,1)`, `P θ = E.P θ`, `α = 0.05`. Take the SPARSE parameter set
`Ξ = [0,1] ∪ {2}`, `θ₁ = 0`, `θ₂ = 1`, so `Θ₀ = [0,1]` and `Θ₁ = {2}` (note
`θ₁, θ₂ ∉ closure Θ₁ = {2}`). Take `C₁ = -1.681477`, `C₂ = 2.681477`, `γ₁ = γ₂ = 0`,
`φ = 1{x < C₁ ∨ x > C₂}`; by the reflection `x ↦ 1 − x` the interval is symmetric about
`1/2`, so `hsize₁ : power φ 0 = 0.05 = α` and `hsize₂ : power φ 1 = 0.05 = α`, and all the
other hypotheses hold. Yet `ψ = 1{x > 2.644854}` is a critical function, *unbiased* at level
`α` — `power ψ θ ≤ power ψ 1 = 0.05 ≤ α` for every `θ ∈ Θ₀ = [0,1]` (monotone in `θ`; e.g.
`0.004086` at `0`, `0.015982` at `1/2`) and `power ψ 2 = 0.259511 ≥ α` — while
`power φ 2 = 0.247901 < 0.259511 = power ψ 2`, contradicting the optimality clause of
`IsUMPU`. (`power φ (1/2) = 0.029148 ≤ α`, so `φ`'s own level on `Θ₀` is not the issue.) As
in `isUMPU_twoSided_expFamily`, the defect is sparseness of `Ξ`: the null endpoints need not
be limit points of the alternative set, so unbiasedness imposes no similarity constraint
there. Openness of `Ξ` is the minimal repair, and is exactly what the classical statement
means by "`θ` ranges over an interval interior to the natural parameter set". -/
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
    -- USER-INPUT (AMENDMENT): the parameter set is open. Without it the statement is FALSE:
    -- see the counterexample in the docstring above
    (hΞopen : IsOpen Ξ)
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
  -- REPAIRED (`hΞopen` added), NOT YET CLOSED. This is PROOF-HARD, not repair-unclear: the
  -- amended statement is the classical `TSH4 §4.2` theorem and the route is fixed. Three
  -- pieces, in the same style as the now-closed `isUMPU_twoSided_expFamily`:
  --  (a) LEVEL on the interior of the null interval. For `θ₁ < θ < θ₂` the classical argument
  --      is the sign pattern of a three-exponential combination: choose `a, b` with
  --      `q(t) = a e^{θ₁t} + b e^{θ₂t} − e^{θt}` vanishing at `C₁, C₂`; then `(φ − α)·q ≥ 0`
  --      pointwise (both factors change sign exactly at `C₁, C₂`, in the same pattern), so
  --      `0 ≤ ∫(φ−α)q dν = a·0 + b·0 − ∫(φ−α)dP_θ·d(θ)`, i.e. `power φ θ ≤ α`.
  --  (b) OPTIMALITY. `expFamily_np_compare` transposed: constraint densities at `θ₁` and `θ₂`
  --      instead of `(1, T)` at `θ₀`, objective at `θ' ∉ [θ₁, θ₂]`, multipliers again from the
  --      three-exponential separation.
  --  (c) SIMILARITY of competitors at `θ₁, θ₂`, from `continuous_power_expFamily` plus
  --      `hΞopen` (each endpoint is a limit of alternatives, so `power ψ θⱼ ≥ α`, and `≤ α`
  --      because `θⱼ ∈ Θ₀`). This piece is a routine variant of the sequence argument inside
  --      `unbiased_side_conditions`.
  -- MISSING BRICK for (a) and (b): the three-exponential separating combination. Substituting
  -- `w = e^{(θ₂−θ₁)t} ∈ (0,∞)` turns `q` into `a + b w − w^λ` with `λ = (θ−θ₁)/(θ₂−θ₁)`; the
  -- needed sign pattern is exactly "the secant of `w ↦ w^λ` lies below the graph inside and
  -- above it outside", i.e. `Real.strictConcaveOn_rpow` for `0 < λ < 1` (case (a)) and
  -- `strictConvexOn_rpow` for `1 < λ` (case (b), after dividing by `e^{θ₁t}` when `θ' > θ₂`
  -- and by `e^{θ₂t}` when `θ' < θ₁`, which keeps the exponent above `1` in both directions).
  -- Both Mathlib lemmas exist; what is missing here is the `exists_sep_line` analogue for a
  -- general strictly convex function on `Ioi 0` (the degenerate `C₁ = C₂` branch needs the
  -- supporting line, available from `one_add_mul_self_lt_rpow_one_add`), plus the transport
  -- of the sign pattern back through the substitution. None of it is deep; it is simply not
  -- written.
  sorry

end StatLean.HypothesisTesting
