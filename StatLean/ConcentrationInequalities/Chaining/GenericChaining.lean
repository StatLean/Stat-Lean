import StatLean.ConcentrationInequalities.Chaining.GammaTwo
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.TailToExpectation
import StatLean.ConcentrationInequalities.Chaining.DyadicNets

/-!
# Generic chaining (Talagrand's γ₂ bound)

For a mean-zero process $(X_t)_{t \in T}$ with sub-Gaussian increments
(Eq. 8.1) on a metric space $(T, d)$,
$$ \mathbb{E} \sup_{t \in T} X_t \;\le\; C K \,\gamma_2(T, d), $$
where $\gamma_2$ is the Talagrand functional over admissible sequences
(Definition 8.5.1, `Chaining/GammaTwo.lean`).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2 (proof Steps 1–3,
Eqs. (8.48)–(8.50)); Remark 8.5.3 for the mean-zero-free $|X_t - X_{t_0}|$
form.

**Proof formalization notes.** Finite-`T` core per the batch sup policy
(book WLOG, p. 247 Step 1). The high-probability form
(`generic_chaining_tail`) carries per-level thresholds
$2^{k/2}(\sqrt{2\log 2} + 1) + u$ over the admissible-sequence levels and a
union bound over $|T_k|\cdot|T_{k-1}| \le 2^{2^{k+1}}$ chain pairs; the
expectation forms integrate it via
`Chaining/TailToExpectation.lean`. **Frozen constants** (formula + numeral):
tail threshold factor `(6 + 2u)` (from $\sum_k 2^{k/2}\,2^{-k/2}$-style
geometric bookkeeping at the designed thresholds); expectation constant
`10` (book's absolute `C`; formula $6 + 2\sqrt{\pi} \le 10$). Per batch
reconciliation R4, the mean-zero assemblies carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means (the
per-pair increment means are then genuine). Work-item single named-sorry
fallback: `generic_chaining_tail` (the per-level event bookkeeping); the
integration and `iInf` steps to Theorem 8.5.2 must close against it.

**Bibliographic comments.** Generic chaining and the majorizing-measure
theory are due to X. Fernique (1975) and M. Talagrand ("Regularity of
Gaussian processes," *Acta Math.* 159 (1987), 99–149; *Upper and Lower
Bounds for Stochastic Processes*, Springer 2014). The admissible-sequence
formulation follows Talagrand via HDP §8.5; the matching lower bound
(majorizing measure theorem, HDP Theorem 8.5.5) is out of Batch-10 scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Generic chaining, high-probability form** (HDP §8.5.2, Theorem 8.5.2
proof Steps 2–3, Eqs. (8.48)–(8.50)): for any admissible sequence `A`, the
sup of increments exceeds `(6 + 2u)·K·γ(A)` with probability at most
`2 exp(−u²)`. This work item's single named-sorry fallback. -/
theorem generic_chaining_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG p.247 Step 1; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index so the sup is genuine
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment sup; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (6 + 2 * u) * K * (gammaFunctional A).toReal <
        ⨆ t ∈ T, |X t ω - X t₀ ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by sorry

/-- Generic chaining, expectation form at a fixed admissible sequence (HDP
§8.5.2 + Remark 8.5.3 — no mean-zero for the `|X_t − X_{t₀}|` form).
Frozen constant `10` (formula `6 + 2√π ≤ 10`), integrating
`generic_chaining_tail` via `TailToExpectation`. -/
theorem generic_chaining_of_admissible {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ) ≤
      10 * K * gammaFunctional A := by sorry

/-- **Theorem 8.5.2 (generic chaining bound)** (HDP §8.5.2; book's absolute
constant frozen `C = 10`): mean-zero process with sub-Gaussian increments
has `E sup X ≤ 10·K·γ₂(T,d)`, in `ofReal` form. -/
theorem generic_chaining {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability of the process, ruling out Bochner-junk
    -- means (batch reconciliation R4; the book's E X_t = 0 presupposes it)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, X t ω ∂μ) ≤ 10 * K * gammaTwo T := by
  sorry

/-- Theorem 8.5.2, real display (LEAN-ONLY: via `gammaTwo_lt_top_of_finite`
the `ℝ≥0∞` bound descends to `ℝ`). -/
theorem generic_chaining_real {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability (R4, as above)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ 10 * K * (gammaTwo T).toReal := by sorry

end StatLean.ConcentrationInequalities
