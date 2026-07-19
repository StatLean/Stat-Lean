import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Notation

/-!
# Stein's identity for a one-parameter exponential family on the line

Let `X` have the one-parameter density `exp(η·T(x) − A(η))·h(x)` with respect to Lebesgue
measure on the line, and let `g` be differentiable with `E_η|g'(X)| < ∞`. Integration by
parts on the whole line gives
$$ E_\eta\Bigl[\Bigl(\tfrac{h'(X)}{h(X)} + \eta\,T'(X)\Bigr)\,g(X)\Bigr]
   \;=\; -\,E_\eta\bigl[g'(X)\bigr], $$
provided the boundary term `g(x)·e^{η T(x)}·h(x)` vanishes at both ends of the support. The
bracketed factor is the derivative of the log-density with respect to `x` — the "score in the
sample argument" — so the identity says that this score is orthogonal to differentiation.

* `ExpFamily.stein_identity` — the identity for a support equal to the whole line.

**Reference.** Classical exponential-family theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The setup is pinned by the hypothesis `E.base = volume.withDensity (ENNReal.ofReal ∘ h)`
  rather than by building the family with `ExpFamily.ofDensity`: this leaves the natural
  statistic `E.stat` as the family's own field, so the conclusion is stated directly about
  `E.P η` and composes with the rest of the area without a rewriting step.
* Nonnegativity of the carrier is a genuine requirement, not bookkeeping: `ENNReal.ofReal`
  truncates negative values, so without it `E.base` would not be the measure with density `h`
  and the logarithmic derivative `h'/h` would not describe it. On `{h = 0}` the quotient
  `h'/h` takes Lean's junk value `0`; that set is `E.base`-null, so the integrand is
  determined `P_η`-almost everywhere and the statement is unaffected.
* The boundary hypothesis is stated with the factor `g` included, i.e. as decay of
  `g·e^{⟨η,T⟩}·h` rather than of `e^{⟨η,T⟩}·h` alone. This is what integration by parts
  actually needs; the classical formulation, which asks only for decay of `e^{⟨η,T⟩}·h`,
  leaves the growth of `g` implicit. Ours is therefore the safe (weaker) form.
* The two integrability hypotheses are the classical `E_η|g'(X)| < ∞` together with the
  integrability of the left-hand integrand, which the classical statement leaves implicit.
  Without the latter Lean's Bochner integral would silently return `0` on the left and the
  identity would assert something false about a divergent expectation.
* The variant for a support equal to a bounded interval `(a, b)` — where the boundary
  condition becomes decay at `a` and `b` — is not formalized here; it is the same integration
  by parts with the limits taken along `𝓝[>] a` and `𝓝[<] b`.

**Bibliographic comments.** The identity for the normal distribution is due to C. Stein
("Estimation of the mean of a multivariate normal distribution," *Ann. Statist.* **9**
(1981), 1135–1151). Its extension to general exponential families, in the form used here, is
due to H. M. Hudson ("A natural identity for exponential families with applications in
multiparameter estimation," *Ann. Statist.* **6** (1978), 473–484).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology

namespace StatLean.PointEstimation

namespace ExpFamily

/-- **Stein's identity** for a one-parameter exponential family on the line with carrier
`densityH` against Lebesgue measure and support the whole line. -/
theorem stein_identity (E : ExpFamily ℝ ℝ) (densityH g : ℝ → ℝ) (η : ℝ)
    -- USER-INPUT: the reference measure is Lebesgue measure weighted by the carrier `h`;
    -- this is the setting in which the identity is classically stated
    (hbase : E.base = volume.withDensity fun x => ENNReal.ofReal (densityH x))
    -- USER-INPUT: the carrier is nonnegative; a density
    (hH0 : ∀ x, 0 ≤ densityH x)
    -- USER-INPUT: nondegenerate reference measure, so that `E.P η` is a probability measure
    (hbase0 : E.base ≠ 0)
    -- USER-INPUT: the carrier is differentiable, so that `h'/h` is defined
    (hHdiff : Differentiable ℝ densityH)
    -- USER-INPUT: the natural statistic is differentiable, so that `T'` is defined
    (hTdiff : Differentiable ℝ E.stat)
    -- USER-INPUT: `g` is differentiable; the classical hypothesis on the test function
    (hgdiff : Differentiable ℝ g)
    -- USER-INPUT: the natural parameter lies where the family is defined
    (hη : η ∈ E.natSet)
    -- USER-INPUT: `E_η|g'(X)| < ∞`; the classical integrability hypothesis
    (hg' : Integrable (fun x => deriv g x) (E.P η))
    -- USER-INPUT: integrability of the left-hand integrand; left implicit in the classical
    -- statement but needed for the expectation on the left to be the stated one
    (hscore : Integrable
      (fun x => (deriv densityH x / densityH x + η * deriv E.stat x) * g x) (E.P η))
    -- USER-INPUT: the boundary term vanishes at `+∞`; the classical support condition
    (hTop : Tendsto (fun x => g x * Real.exp ⟪η, E.stat x⟫_ℝ * densityH x) atTop (𝓝 0))
    -- USER-INPUT: the boundary term vanishes at `−∞`; the classical support condition
    (hBot : Tendsto (fun x => g x * Real.exp ⟪η, E.stat x⟫_ℝ * densityH x) atBot (𝓝 0)) :
    ∫ x, (deriv densityH x / densityH x + η * deriv E.stat x) * g x ∂(E.P η)
      = -∫ x, deriv g x ∂(E.P η) := by
  sorry

end ExpFamily

end StatLean.PointEstimation
