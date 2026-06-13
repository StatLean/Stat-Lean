import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.ForMathlib.OptionalStopping

/-!
# Knock-off FDR control — assembly (Lu-BDA §19, Theorem `thm:knockoff`)

The knock-off filter at level `α` uses a knock-off score `W` (see `Knockoff/Defs.lean`,
Def. `kos`). With
`S⁺(t) = { j : |Wⱼ| ≥ t, Wⱼ > 0 }`, `S⁻(t) = { j : |Wⱼ| ≥ t, Wⱼ < 0 }`,
the estimated FDP is `FDPhat(t) = (#S⁻(t) + 1) / (#S⁺(t) ∨ 1)`, and the procedure rejects
`S⁺(t*)` for `t* = min{ t : FDPhat(t) ≤ α }`.

**Main result** (`knockoff_fdr_le`): `FDR ≤ α`.

Proof outline (Lu-BDA §19): `FDP(t*) ≤ α · V₊(t*)/(1+V₋(t*))` (`knockoff_fdp_le`, deterministic,
with `V±(t) = #{ j ∈ H₀ : j ∈ S±(t) }`); then `E[V₊(t*)/(1+V₋(t*))] ≤ 1`
(`knockoff_ratio_stopped_le_one`), which is the heart: `V₊/(1+V₋)` is a supermartingale over the
decreasing-threshold filtration (because the null signs are i.i.d. `Ber(½)` given the magnitudes,
Def. `kos` cond. 3), and `supermartingale_integral_stoppedValue_le` (the `thm:optstop` discharge)
applied at the stopping time `t*` gives `E[·] ≤ E[V₊(0)/(1+V₋(0))] ≤ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- `S⁺(t)`: indices with magnitude `≥ t` and positive sign (Lu-BDA §19). -/
noncomputable def Splus (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : Finset (Fin d) :=
  Finset.univ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω)

/-- `S⁻(t)`: indices with magnitude `≥ t` and negative sign (Lu-BDA §19). -/
noncomputable def Sminus (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : Finset (Fin d) :=
  Finset.univ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0)

/-- `V₊(t) = #{ j ∈ H₀ : j ∈ S⁺(t) }`, the number of *null* positives above threshold `t`. -/
noncomputable def Vplus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) : ℕ :=
  ((Splus W t ω) ∩ H₀).card

/-- `V₋(t) = #{ j ∈ H₀ : j ∈ S⁻(t) }`, the number of *null* negatives above threshold `t`. -/
noncomputable def Vminus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) : ℕ :=
  ((Sminus W t ω) ∩ H₀).card

/-- Estimated FDP `FDPhat(t) = (#S⁻(t) + 1)/(#S⁺(t) ∨ 1)` (Lu-BDA §19). -/
noncomputable def FDPhat (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ((Sminus W t ω).card + 1 : ℝ) / max ((Splus W t ω).card : ℝ) 1

/-- The knock-off threshold `t* = min{ t ∈ {|Wⱼ|} : FDPhat(t) ≤ α }` (Lu-BDA §19); `0` in the
degenerate case where no candidate threshold achieves `FDPhat ≤ α` (then nothing is rejected,
see `knockoffRejects`). -/
noncomputable def tStar (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : ℝ :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then cands.min' h else 0

/-- Knock-off rejection set: `S⁺(t*)` (Lu-BDA §19). In the degenerate case (no candidate
threshold achieves `FDPhat ≤ α`) nothing is rejected. -/
noncomputable def knockoffRejects (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : Finset (Fin d) :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then Splus W (cands.min' h) ω else ∅

/-- Deterministic FDP bound (Lu-BDA §19, first display of the proof):
`FDP(t*) ≤ α · V₊(t*)/(1 + V₋(t*))`. -/
theorem knockoff_fdp_le (α : ℝ) (hα : 0 < α) (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    FDP H₀ (knockoffRejects W α) ω
      ≤ α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) := by
  sorry

/-- **Master inequality** (Lu-BDA §19, the supermartingale + optional-stopping step):
`E[V₊(t*)/(1+V₋(t*))] ≤ 1`. The heart of the knock-off proof — `V₊/(1+V₋)` is a supermartingale
over the decreasing-threshold filtration (the null signs are i.i.d. `Ber(½)` given the
magnitudes, Def. `kos` cond. 3, so `V₊ | V₊+V₋` is hypergeometric), and the optimal stopping
theorem `supermartingale_integral_stoppedValue_le` at the stopping time `t*` gives the bound. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) :
    ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ ≤ 1 := by
  sorry

/-- **Knock-off FDR control** (Lu-BDA §19, Theorem `thm:knockoff`). For a knock-off score `W`, the
knock-off procedure at level `α` controls the false discovery rate: `FDR ≤ α`. -/
theorem knockoff_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ) (hα : 0 < α)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    -- LEAN-ONLY: no ties on null scores (`Wⱼ ≠ 0` a.s.), so the sign is well-defined; Lu-BDA §19
    (hties : ∀ j ∈ H₀, ∀ᵐ ω ∂μ, W j ω ≠ 0) :
    FDR H₀ (knockoffRejects W α) μ ≤ α := by
  sorry

end StatLean.MultipleTesting
