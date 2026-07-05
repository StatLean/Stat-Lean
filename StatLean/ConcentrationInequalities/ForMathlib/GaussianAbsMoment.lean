import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Absolute first moment of the standard Gaussian

For $g \sim N(0,1)$,
$$ \mathbb{E}\,|g| \;=\; \sqrt{\tfrac{2}{\pi}}, $$
an exact equality (not an inequality). Absent from Mathlib at our pin
(verified); Mathlib-only imports — candidate upstream. This is the source of
the sharp constant $\sqrt{2\pi} = 2\sqrt{\pi/2}$ (the book's display constant
$3$) in the Gaussian symmetrization Lemma 6.6.2 (upper bound).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, p. 185 ($\mathbb{E}|g_i| = \sqrt{2/\pi}$ in
the proof of Lemma 6.6.2).

**Proof formalization notes.** Route: unfold `gaussianReal 0 1` as
`withDensity` of `gaussianPDFReal` (variance ≠ 0 branch), split
$\int_{\mathbb{R}} |x|\,\varphi(x)\,dx$ at $0$ by evenness into
$2\int_0^\infty x\,\varphi(x)\,dx$, and evaluate the improper integral of
$x e^{-x^2/2}$ over `Ioi 0` by the antiderivative $-e^{-x^2/2}$
(`integral_Ioi_of_hasDerivAt_of_tendsto`); several `toReal`/`ofReal`
conversions on the density are expected. Integrability from
`memLp_id_gaussianReal` at `p = 1`. Named-sorry fallback of this work item:
`integral_abs_id_gaussianReal` itself (the integrability lemma proven);
downstream Lemma 6.6.2-upper then carries exactly one visible debt.

**Bibliographic comments.** The half-normal mean $\sqrt{2/\pi}$ is classical
(the first absolute moment of the normal law appears already in Gauss's
*Theoria motus*, 1809, and the folded-normal literature); it is standard
textbook material and not attributable to a research paper.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `|g|` is integrable for `g ∼ N(0,1)`. -/
-- LEAN-ONLY: via `memLp_id_gaussianReal` at `p = 1`; no book content.
theorem integrable_abs_id_gaussianReal :
    Integrable (fun x => |x|) (gaussianReal 0 1) := by
  sorry

/-- **Absolute first moment of the standard Gaussian** (HDP §6.6, p. 185):
`E|g| = √(2/π)`, an exact equality. Named-sorry debt candidate of this work
item. -/
theorem integral_abs_id_gaussianReal :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  sorry

end StatLean.ConcentrationInequalities
