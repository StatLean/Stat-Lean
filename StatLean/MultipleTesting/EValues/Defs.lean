import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# E-variables and p-variables — definitions

Concept-layer data model for **e-values** (Candès, Lecture 15, Defs. 3–4, STAT 300C Notes).

For testing a (simple) null hypothesis represented by a probability measure `μ` on the sample
space `Ω`:

* an **e-variable** is a nonnegative statistic `E : Ω → ℝ` whose expectation under the null is at
  most one, `Eμ[E] ≤ 1` (Def. 3). Its realized values are *e-values*. E-variables are the natural
  currency for *optional continuation* (sequential testing with data-dependent stopping), where
  p-values fail.
* a **p-variable** is a statistic `P : Ω → ℝ` with `μ{P ≤ α} ≤ α` for every `α ∈ (0,1)` (Def. 4) —
  exactly the [[`SuperUniform`]] property restricted to `(0,1)`. Its realized values are *p-values*.

The two notions are linked by the conversion `P = 1/E` (Prop. 3), proved in the sibling assembly
file `EValues/Conversion.lean`. These definitions are theorem-agnostic.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsEVariable E μ`: the statistic `E : Ω → ℝ` is an **e-variable** for the simple null `μ`
(Candès, Lecture 15, Def. 3, STAT 300C) — nonnegative with `Eμ[E] ≤ 1`. -/
structure IsEVariable (E : Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (Candès, L15, Def. 3): an e-variable is a *nonnegative* random variable. -/
  nonneg : ∀ ω, 0 ≤ E ω
  /-- Constitutive (Candès, L15, Def. 3): `E` is a statistic, hence measurable — needed for the
  expectation in `expectation_le_one` to be the genuine null expectation. -/
  measurable : Measurable E
  /-- Constitutive (Candès, L15, Def. 3): the defining inequality `Eμ[E] ≤ 1`, stated as the
  **lower integral** of `ofReal ∘ E`. For a nonnegative measurable `E` this `∫⁻` is the genuine
  (possibly `∞`) expectation, so bounding it by `1` both encodes `Eμ[E] ≤ 1` *and* witnesses
  finiteness — forcing integrability of `E`. (The Bochner form `∫ E ∂μ ≤ 1` is unsound here: a
  non-integrable nonneg `E` has Bochner integral `0 ≤ 1` *vacuously*, so it would qualify with
  infinite true expectation and break the e→p conversion.) -/
  expectation_le_one : ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ ≤ 1

/-- `IsPVariable P μ`: the statistic `P : Ω → ℝ` is a **p-variable** for the simple null `μ`
(Candès, Lecture 15, Def. 4, STAT 300C) — `μ{P ≤ α} ≤ α` for every `α ∈ (0,1)`. This is the
[[`SuperUniform`]] property on the open unit interval. -/
def IsPVariable (P : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → μ {ω | P ω ≤ α} ≤ ENNReal.ofReal α

end StatLean.MultipleTesting
