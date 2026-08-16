import StatLean.ConcentrationInequalities.Chaining.GenericChaining
import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

/-!
# Generic chaining with a genuine supremum over the index set

Honest `sup_{t ∈ T}` forms of the generic chaining bound (HDP Theorem 8.5.2
via the Remark 8.5.3 anchoring) over an arbitrary — possibly uncountable —
metric-space index set: countable-subset cores against `gammaFunctional A`
and `gammaTwo T`, tail forms on the junk-free existential event and the
formal supremum, separable-supremum expectation forms (absolute and
anchored), and the real display under the `γ₂ ≠ ⊤` junk-guard. As in the
per-finite-subset family, NO covering package appears anywhere: admissible
sequences carry all the geometry and `gammaTwo` is an honest `ℝ≥0∞`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2, Remark 8.5.3, Eq. (8.50);
the uncountable forms realize the p. 227 / p. 249 footnotes ("assuming T is
finite to avoid measurability issues; the general case typically follows by
approximation") through separable versions.

**Proof formalization notes.** Frozen constants unchanged: `20` for the
expectation forms, `(12 + 4u)` for the tail. The anchored separable form
`generic_chaining_separable` carries NO mean-zero/integrability hypotheses
(Lean-side strengthening: the anchored carrier is dominated by the absolute
one at the same constant; under `hmean` its LHS dominates every
Remark-7.2.1 finite maximum of `X` itself — see `generic_chaining`). The
countable-subset integrability plumbing has no covering package to bound
increments with; it branches on `K = 0` and `gammaFunctional A = ⊤` and
otherwise bounds `dist t t₀` through the level-0 singleton
(`ofReal_infDist_zero_le_gammaFunctional`). Named-sorry fallback of this
work item: `generic_chaining_of_admissible_countable_subset` (that
integrability plumbing).

**Bibliographic comments.** M. Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, Springer 2014, §2.2–2.3 (the majorizing-measure
γ₂ theory); separable versions per van Handel, *Probability in High
Dimension*, §5.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Generic chaining along an admissible sequence, countable-subset
supremum core** (HDP §8.5.2): `∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·γ(A)` in
`ℝ≥0∞` for any countable `C ⊆ T`; the `γ(A) = ⊤` branch is trivial. -/
theorem generic_chaining_of_admissible_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaFunctional A := by
  sorry

/-- **Generic chaining, absolute form, countable-subset supremum core**
(HDP §8.5.2, Theorem 8.5.2 via Remark 8.5.3):
`∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·γ₂(T,d)` in `ℝ≥0∞`, by the infimum
over admissible sequences. -/
theorem generic_chaining_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T := by
  sorry

/-- **Generic chaining, tail form, existential countable-subset core**
(HDP §8.5.2, Eq. (8.50)): with probability at least `1 − 2e^{−u²}`, no
member of the countable subfamily `C ⊆ T` has anchored increment exceeding
`(12 + 4u)·K·γ(A)`. The junk-free engine stage of the formal-supremum
displays. -/
theorem generic_chaining_tail_exists {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    μ {ω | ∃ t ∈ C, (12 + 4 * u) * K * (gammaFunctional A).toReal
        < |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **Generic chaining, tail form, separable supremum** (HDP §8.5.2,
Eq. (8.50), general `T`): for a separable version, the anchored increment
supremum over `T` exceeds `(12 + 4u)·K·γ(A)` with probability at most
`2e^{−u²}`. -/
theorem generic_chaining_tail_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal
        < ⨆ t ∈ T, |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **Generic chaining, absolute form, separable supremum** (HDP §8.5.2 via
Remark 8.5.3, general `T`): `∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·γ₂(T,d)`
in `ℝ≥0∞` for a separable version, NO mean-zero. -/
theorem generic_chaining_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T := by
  sorry

/-- **Theorem 8.5.2 (generic chaining bound), separable supremum**
(HDP §8.5.2, general `T`): `∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 20·K·γ₂(T,d)`
in `ℝ≥0∞` for a separable version. Lean-side strengthening: NO
mean-zero/integrability hypotheses — the anchored carrier is dominated by
`generic_chaining_abs_separable` at the SAME frozen constant `20`; under
mean-zero the LHS dominates every Remark-7.2.1 finite maximum of `X` itself
(see `generic_chaining`), so this is the honest sup-form of the book's
`E sup_{t∈T} X_t ≤ C·K·γ₂(T,d)`. -/
theorem generic_chaining_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point (Remark 8.5.3 device)
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ 20 * K * gammaTwo T := by
  sorry

/-- **Generic chaining, absolute form, separable supremum, real display**
(HDP §8.5.2): under the `γ₂ ≠ ⊤` junk-guard,
`∫ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·(γ₂(T,d)).toReal` as real numbers. -/
theorem generic_chaining_abs_separable_real {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite γ₂ so the real RHS is honest (junk-guard)
    (hγ : gammaTwo T ≠ ⊤) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  sorry

/-- **Generic chaining, absolute form, countable supremum** (HDP §8.5.2):
the `C := T` display of the countable-subset core. -/
theorem generic_chaining_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T := by
  sorry

/-- **Generic chaining, tail form, countable supremum** (HDP §8.5.2,
Eq. (8.50)): the `C := T` display of the tail core, on the formal
supremum. -/
theorem generic_chaining_tail_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal
        < ⨆ t ∈ T, |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  sorry

/-- **Generic chaining, absolute form, countable supremum, real display**
(HDP §8.5.2): the countable-`T` real display under the `γ₂ ≠ ⊤`
junk-guard. -/
theorem generic_chaining_abs_countable_real {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite γ₂ so the real RHS is honest (junk-guard)
    (hγ : gammaTwo T ≠ ⊤) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  sorry

end StatLean.ConcentrationInequalities
