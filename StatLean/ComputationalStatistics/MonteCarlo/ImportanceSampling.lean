import StatLean.ComputationalStatistics.Core.Defs
import StatLean.ComputationalStatistics.ForMathlib.PiMoments
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Decomposition.Lebesgue

/-!
# Importance sampling

Importance sampling is the change-of-measure method of Monte Carlo (ECS §2.6):
to estimate `∫ g dP`, sample from a proposal `Q` with `P ≪ Q` and average
`g·w` where `w = dP/dQ` is the importance weight.

* `importanceWeight` — the weight `w = (dP/dQ).toReal`;
* `integral_importanceWeight_mul` — the change-of-measure identity
  `∫ g·w dQ = ∫ g dP` (a textbook-named wrapper of the pinned Mathlib
  `MeasureTheory.integral_toReal_rnDeriv_mul`, per the load-don't-reprove rule);
* `importanceSampling_unbiased`, `importanceSampling_variance` — moments of the
  importance-sampling estimator `(1/n)·Σᵢ g(Xᵢ)·w(Xᵢ)`, `Xᵢ ~ Q` i.i.d.
  (ECS §2.6, eq. (2.11));
* `lintegral_sq_le_lintegral_sq_div`, `lintegral_sq_div_optimalImportance` —
  the optimal-importance-function bound `(∫ f dν)² ≤ ∫ f²/p dν` over densities
  `p`, with equality at `p* = f/∫f` (ECS §2.6, the Jensen-inequality display):
  the mathematical content of "sample more heavily where `f` is large".

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.6 (reducing variance; importance sampling,
eq. (2.11) and the optimal-density display on p. 60).  (`ECS §2.6`.)

**Proof formalization notes.**

* The estimator statements are over the canonical product `Measure.pi
  (fun _ : Fin n => Q)`; they are `PiMoments` lemmas at the integrand `g·w`.
* Absolute continuity `P ≪ Q` is the book's support condition ("the majorizing
  density must not vanish where the target is positive"); without it the
  estimator is not even well-posed, so it appears as a hypothesis, not a
  conclusion.
* The optimal-importance bound is stated in `ℝ≥0∞` with the `0/0 = 0`, `x/0 = ∞`
  junk conventions, which make it hypothesis-free beyond measurability and
  `∫⁻ p dν = 1`: where `p` vanishes but `f` does not, the right-hand side is
  `∞` and the bound is trivial.  The optimizer `p* = f/∫⁻f` achieves equality
  for every measurable `f`, including the degenerate cases `∫⁻ f ∈ {0, ∞}`.

**Bibliographic comments.** Importance sampling goes back to Kahn–Marshall
(*J. Oper. Res. Soc. Amer.* **1** (1953), 263–278); the optimal-density result
is Rubinstein's Theorem 4.3.1 (*Simulation and the Monte Carlo Method*, Wiley,
1981) and appears in ECS §2.6 via Jensen's inequality.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P Q : Measure 𝓧}

/-- The **importance weight** `w = dP/dQ` (ECS §2.6): the Radon–Nikodym
derivative of the target with respect to the proposal, as a real function.
Edge behaviour: `w = 0` wherever the derivative is infinite (a `Q`-null set
when `P ≪ Q` and `P` is finite). -/
noncomputable def importanceWeight (P Q : Measure 𝓧) : 𝓧 → ℝ :=
  fun z => (P.rnDeriv Q z).toReal

/-- **The importance-sampling identity** (ECS §2.6, p. 60 display):
`∫ g·(dP/dQ) dQ = ∫ g dP` under `P ≪ Q`.  Wrapper of the pinned Mathlib
`integral_toReal_rnDeriv_mul`. -/
theorem integral_importanceWeight_mul [SigmaFinite P] [SigmaFinite Q] {g : 𝓧 → ℝ}
    -- USER-INPUT: the target is dominated by the proposal; ECS §2.6
    (hPQ : P ≪ Q) :
    ∫ z, g z * importanceWeight P Q z ∂Q = ∫ z, g z ∂P := by
  sorry

/-- **Unbiasedness of the importance-sampling estimator** (ECS §2.6,
eq. (2.11)): sampling i.i.d. from the proposal `Q` and averaging `g·w` has
expectation `∫ g dP`. -/
theorem importanceSampling_unbiased [IsProbabilityMeasure Q] [SigmaFinite P]
    {n : ℕ} [NeZero n] {g : 𝓧 → ℝ}
    -- USER-INPUT: the target is dominated by the proposal; ECS §2.6
    (hPQ : P ≪ Q)
    -- USER-INPUT: the weighted integrand has a finite first moment under the proposal; ECS §2.6
    (hgw : Integrable (fun z => g z * importanceWeight P Q z) Q) :
    ∫ x, mcEstimate (fun z => g z * importanceWeight P Q z) x
        ∂(Measure.pi fun _ : Fin n => Q)
      = ∫ z, g z ∂P := by
  sorry

/-- **Variance of the importance-sampling estimator** (ECS §2.6):
`Var(Î_IS) = Var_Q(g·w)/n`. -/
theorem importanceSampling_variance [IsProbabilityMeasure Q] {n : ℕ} [NeZero n]
    {g : 𝓧 → ℝ}
    -- USER-INPUT: the weighted integrand has a finite second moment under the proposal; ECS §2.6
    (hgw : MemLp (fun z => g z * importanceWeight P Q z) 2 Q) :
    variance (mcEstimate fun z => g z * importanceWeight P Q z)
        (Measure.pi fun _ : Fin n => Q)
      = variance (fun z => g z * importanceWeight P Q z) Q / n := by
  sorry

variable {ν : Measure 𝓧}

/-- **The optimal-importance-function lower bound** (ECS §2.6, p. 60): for any
importance density `p` with `∫⁻ p dν = 1`, the second moment of the weighted
integrand satisfies `(∫⁻ f dν)² ≤ ∫⁻ f²/p dν`.  Stated in `ℝ≥0∞`, so no
support condition is needed: where `p = 0 < f` the right-hand side is `∞`. -/
theorem lintegral_sq_le_lintegral_sq_div {f p : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hf : Measurable f)
    -- LEAN-ONLY: measurability of the importance density (regularity)
    (hp : Measurable p)
    -- USER-INPUT: `p` is a probability density w.r.t. the base measure; ECS §2.6
    (hp1 : ∫⁻ z, p z ∂ν = 1) :
    (∫⁻ z, f z ∂ν) ^ 2 ≤ ∫⁻ z, f z ^ 2 / p z ∂ν := by
  sorry

/-- **The optimal importance function achieves the bound** (ECS §2.6, p. 60):
at `p* = f / ∫⁻ f dν`, the second moment equals `(∫⁻ f dν)²`.  Holds for every
measurable `f`, including the degenerate cases `∫⁻ f ∈ {0, ∞}`, by the `ℝ≥0∞`
division conventions. -/
theorem lintegral_sq_div_optimalImportance {f : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hf : Measurable f) :
    ∫⁻ z, f z ^ 2 / (f z / ∫⁻ y, f y ∂ν) ∂ν = (∫⁻ z, f z ∂ν) ^ 2 := by
  sorry

end StatLean.ComputationalStatistics
