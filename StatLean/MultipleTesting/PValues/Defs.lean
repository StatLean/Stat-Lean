import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Super-uniform p-values — definition

Concept-layer definition for multiple testing. A p-value `p : Ω → ℝ` for a *true* null
hypothesis is **super-uniform** if `P(p ≤ t) ≤ t` for every `t ≥ 0` (Lu-BDA §18; the book's BH
proof uses the exact-uniform identity `P(p ≤ t) = t`, of which this is the honest provable
relaxation — see `BenjaminiHochberg.lean`).

This is the only distributional assumption the BH / Holm FWER arguments place on the null
p-values; it is theorem-agnostic and consumed by the assembly files.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `SuperUniform p μ`: the p-value `p` is *super-uniform* under `μ`, i.e. `μ {p ≤ t} ≤ t` for
every `t ≥ 0` (Lu-BDA §18). The defining null assumption; for an exactly-uniform `p` it holds
with equality. -/
def SuperUniform (p : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t → μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t

end StatLean.MultipleTesting
