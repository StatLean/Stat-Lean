import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Conditional characteristic-function calculus for MDS arrays

The analytic bricks of the Brown/Hall–Heyde martingale CLT
(`MartingaleCLT/BrownCLT.lean` assembles them):

* the **conditional Taylor estimate**: a.e.,
  `‖E[e^{iuX} | 𝓖] − (1 − u²/2 · E[X² | 𝓖])‖` is controlled by the conditional
  Lindeberg mass at any level `ε` plus `|u|³ ε · E[X² | 𝓖]`;
* the **tower telescope**: for an MDS row, the gap between `E[e^{iuS_n}]` and
  `E[∏_i (1 − u²/2 · E[X_i²|𝓕_i])]` is at most the summed conditional Taylor errors
  (peel factors from the right by the tower property; the martingale-difference
  property kills the linear terms);
* the **product comparison**: on the event where the conditional variance process is
  close to `σ²` and the summands are uniformly small,
  `∏_i (1 − u²/2 · E[X_i²|𝓕_i])` is close to `e^{−u²σ²/2}`.

**Reference.** Hall & Heyde (1980), §3.2 (proof of Thm 3.2), after Brown (1971) §3.
(`Hall–Heyde §3.2` in tags.)

**Proof formalization notes.**
* Conditional expectations of complex-valued integrands are taken componentwise
  (`Complex.re/im` through Mathlib's real `condExp`); the statements below pre-split
  them so the closure sessions never need a ℂ-valued `condExp` API.
* All statements are a.e. inequalities between real quantities — no conditional
  independence is ever invoked (that is the point of the martingale method).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

section CondTaylor

variable {Ω : Type*}

/-- **Conditional Taylor estimate** (Hall–Heyde Lemma 3.1-adjacent): for a
square-integrable `X` with `E[X | 𝓖] = 0` and any `ε > 0`, a.e.
`‖(E[cos uX | 𝓖] + i E[sin uX | 𝓖]) − (1 − u²/2 E[X²|𝓖])‖
  ≤ u² E[X² 1_{|X| ≥ ε} | 𝓖] + |u|³ ε E[X² | 𝓖]`.

Binder convention: ambient `mΩ` is a plain implicit bound after `m` and before `μ`
(see `Mixing/Relations.lean`). -/
theorem norm_condexp_exp_sub_one_sub_le {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable X) (hL2 : MemLp X 2 μ)
    (hcond : μ[X | m] =ᵐ[μ] 0) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ,
      ‖(⟨μ[fun ω' => Real.cos (u * X ω') | m] ω,
          μ[fun ω' => Real.sin (u * X ω') | m] ω⟩ : ℂ)
          - (1 - u ^ 2 / 2 * μ[fun ω' => X ω' ^ 2 | m] ω)‖
        ≤ u ^ 2 * μ[fun ω' => X ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |X x|}
              (fun _ => (1 : ℝ)) ω' | m] ω
          + |u| ^ 3 * ε * μ[fun ω' => X ω' ^ 2 | m] ω := by
  sorry

end CondTaylor

section Arrays

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Tower telescope** (the heart of Brown's proof): for an MDS row, peeling the
factors of `e^{iuS}` from the right against the filtration replaces each by its
conditional Taylor polynomial, at total cost the summed conditional errors. -/
theorem norm_integral_exp_rowSum_sub_prod_le [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) (n : ℕ) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
        - ∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) * (μ[fun ω' => X n i ω' ^ 2
            | F n i.castSucc] ω : ℝ)) ∂μ‖
      ≤ ∑ i, (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
            (fun _ => (1 : ℝ)) ω ∂μ)
        + ∑ i, (|u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ) := by
  sorry

/-- **Product comparison**: if the conditional variance process converges to `σ²` in
probability and the individual conditional variances are uniformly asymptotically
negligible, the Taylor product converges to the Gaussian factor. -/
theorem tendsto_integral_prod_one_sub_condVar [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: uniform asymptotic negligibility of the conditional variances
    (hunif : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ μ[fun ω' => X n i ω' ^ 2
          | F n i.castSucc] ω}).toReal) atTop (𝓝 0))
    -- LEAN-ONLY: a uniform L¹ bound on the variance process, ruling out mass escape
    (hbdd : ∃ B : ℝ, ∀ n, ∫ ω, mdsCondVariance k X F μ n ω ∂μ ≤ B)
    (u : ℝ) :
    Tendsto (fun n => ∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) *
        (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ)) ∂μ) atTop
      (𝓝 (Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ)))) := by
  sorry

end Arrays

end StatLean.TimeSeries
