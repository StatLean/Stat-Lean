import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Laplace (double-exponential) distribution `Laplace(0, b)`

The centered Laplace distribution with scale `b > 0`, a standard probability brick that the pinned
Mathlib lacks (it has the Gaussian and Gamma laws but not the double-exponential). Density
`f(x) = (2b)⁻¹ exp(−|x|/b)`, measure `Laplace(0, b) = volume.withDensity f`, and the symmetric-tail
identity `P(|X| > δ) = exp(−δ/b)` used to compute the Dirichlet–Laplace marginal tail.

**Reference.** Standard Laplace-distribution facts (e.g. Kotz–Kozubowski–Podgórski, *The Laplace
Distribution and Generalizations*, Birkhäuser, 2001, §2.1). A **standard Laplace-distribution brick**:
it carries no Dirichlet–Laplace-specific content of its own, but is consumed by the scale mixture
`θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(a, 1/2)` of Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace
priors for optimal shrinkage* (arXiv:1401.5398), eq. (10).

**Proof formalization notes.** `laplacePDFReal` keeps the raw prefactor `(2b)⁻¹`, so for `b ≤ 0` the
prefactor is `≤ 0` and `ENNReal.ofReal` collapses the density to `0`; hence `laplaceMeasure b = 0`
for `b ≤ 0` (a junk guard mirroring the Gaussian/Gamma conventions, keeping the object usable at
degenerate scale indices). The total-mass and tail computations reduce to `∫ exp(−x/b) dx` over a
half-line; the **tail identity** `laplaceMeasure b {δ < |x|} = exp(−δ/b)` is the Laplace
conditional-tail formula — the two symmetric exponential tails each contribute `(1/2)exp(−δ/b)`.

**Bibliographic comments.** The double-exponential law is Laplace's *first* law of errors (1774),
predating the Gaussian second law; in Bayesian shrinkage it is the prior behind the Bayesian lasso
(Park–Casella, *J. Amer. Statist. Assoc.* 103 (2008), 681–686).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- **Centered Laplace density** `f(x) = (2b)⁻¹ exp(−|x|/b)` (scale `b`, location `0`), as a real
number. For `b ≤ 0` the prefactor `(2b)⁻¹` is `≤ 0`, so downstream `ENNReal.ofReal` reads the density
as `0` (junk guard; all content lemmas assume `0 < b`). -/
noncomputable def laplacePDFReal (b x : ℝ) : ℝ := (2 * b)⁻¹ * Real.exp (-|x| / b)

/-- **Centered Laplace density** as an extended nonnegative real, `ENNReal.ofReal` of
`laplacePDFReal`. Equals `0` for `b ≤ 0` (nonpositive prefactor). -/
noncomputable def laplacePDF (b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (laplacePDFReal b x)

/-- The Laplace density in `x` is measurable, at every fixed scale `b`. -/
lemma measurable_laplacePDF (b : ℝ) : Measurable (laplacePDF b) := by
  sorry

/-- **Joint measurability** of `(b, x) ↦ laplacePDF b x`, the input needed to form the
Gamma–Laplace scale-mixture `bind` (see `Measure.bind_withDensity`). -/
lemma measurable_laplacePDF_uncurry : Measurable (Function.uncurry laplacePDF) := by
  sorry

/-- The Laplace density integrates to `1` against Lebesgue measure (total probability mass), for
positive scale. -/
lemma lintegral_laplacePDF_eq_one {b : ℝ}
    -- LEAN-ONLY: positive scale; the normalization (2b)⁻¹ gives total mass 1 only for b > 0
    (hb : 0 < b) :
    ∫⁻ x, laplacePDF b x ∂volume = 1 := by
  sorry

/-- **Laplace measure** `Laplace(0, b) = volume.withDensity ((2b)⁻¹ exp(−|·|/b))`. For `b ≤ 0` the
density vanishes, so this is the zero measure (junk guard; it is a probability measure iff `0 < b`). -/
noncomputable def laplaceMeasure (b : ℝ) : Measure ℝ := volume.withDensity (laplacePDF b)

/-- `Laplace(0, b)` is a probability measure for positive scale. -/
theorem isProbabilityMeasure_laplaceMeasure {b : ℝ}
    -- LEAN-ONLY: positive scale; Laplace(0,b) is a probability measure only for b > 0
    (hb : 0 < b) :
    IsProbabilityMeasure (laplaceMeasure b) := by
  sorry

/-- For nonpositive scale the Laplace measure degenerates to `0` (the density is identically `0`). -/
theorem laplaceMeasure_of_nonpos {b : ℝ}
    -- LEAN-ONLY: nonpositive scale is the junk branch; the density collapses to 0
    (hb : b ≤ 0) :
    laplaceMeasure b = 0 := by
  sorry

/-- **Laplace tail identity** `P(|X| > δ) = exp(−δ/b)` — the symmetric double-exponential tail, for
positive scale `b` and nonnegative threshold `δ`. This is the marginal-tail input to the
Dirichlet–Laplace mixture analysis. -/
theorem laplaceMeasure_abs_gt {b δ : ℝ}
    -- LEAN-ONLY: positive scale; the tail identity holds for the genuine Laplace law (b > 0)
    (hb : 0 < b)
    -- LEAN-ONLY: nonnegative threshold; for δ < 0 the event is all of ℝ and exp(−δ/b) > 1 fails
    (hδ : 0 ≤ δ) :
    laplaceMeasure b {x : ℝ | δ < |x|} = ENNReal.ofReal (Real.exp (-δ / b)) := by
  sorry

/-- Measurability of `b ↦ laplaceMeasure b s` for a fixed measurable set `s` (kernel measurability,
needed to form the Gamma–Laplace scale-mixture `bind`). -/
lemma measurable_laplaceMeasure_apply {s : Set ℝ}
    -- LEAN-ONLY: the evaluation set is measurable (regularity)
    (hs : MeasurableSet s) :
    Measurable (fun b => laplaceMeasure b s) := by
  sorry

end StatLean.Bayesian
