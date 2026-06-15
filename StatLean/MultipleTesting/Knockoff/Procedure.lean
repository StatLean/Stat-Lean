import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.Knockoff.Defs

/-!
# Knock-off procedure — definitions (Lu-BDA §19)

The deterministic data of the knock-off filter at level `α`, over a knock-off score
`W : Fin d → Ω → ℝ` and true-null set `H₀`:

* `Splus W t ω` / `Sminus W t ω` — indices with magnitude `≥ t` and positive / negative sign;
* `Vplus W H₀ t ω` / `Vminus W H₀ t ω` — counts of *null* positives / negatives above `t`;
* `FDPhat W t ω` — the estimated FDP `(#S⁻ + 1)/(#S⁺ ∨ 1)`;
* `tStar W α ω` — the threshold `min{ t ∈ {|Wⱼ|} : FDPhat ≤ α }`;
* `knockoffRejects W α ω` — the rejection set `S⁺(t*)`.

This is the shared concept layer for the knock-off assembly files (`FdpBound`, `Initial`,
`Supermartingale`, the final `Knockoff`). It is theorem-agnostic and laptop-owned.
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

/-- The knock-off threshold `t* = min{ t ∈ {|Wⱼ|} : FDPhat(t) ≤ α }` (Lu-BDA §19). In the
degenerate case (no candidate magnitude achieves `FDPhat ≤ α`) we return a value strictly **above
every magnitude**, `1 + ∑ⱼ |Wⱼ|`, so that `S⁺(t*) = S⁻(t*) = ∅` — i.e. nothing is rejected, matching
`knockoffRejects`, and the null ratio `V₊(t*)/(1+V₋(t*)) = 0`. (The former `0` convention left
`knockoffRejects = ∅` while `V₊(0)/(1+V₋(0)) ≠ 0`, an inconsistency that broke the order-statistic
bridge `ratio_eq_Yproc_hittingIdx`.) -/
noncomputable def tStar (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : ℝ :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then cands.min' h else 1 + ∑ j, |W j ω|

/-- Knock-off rejection set: `S⁺(t*)` (Lu-BDA §19). In the degenerate case (no candidate
threshold achieves `FDPhat ≤ α`) nothing is rejected. -/
noncomputable def knockoffRejects (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : Finset (Fin d) :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then Splus W (cands.min' h) ω else ∅

end StatLean.MultipleTesting
