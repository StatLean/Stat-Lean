import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzNet
import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzApprox

/-!
# Full-supremum honesty for the Lipschitz class — dense reduction chain

The deterministic, per-$\omega$ reduction of the supremum of $|X_f|$ over the
**genuine uncountable** $L$-Lipschitz class to a monotone limit of finite
maxima:
$$ \sup_{\|f\|_{\mathrm{Lip}} \le L} |X_f|
   \;\overset{\text{R1}}{=}\; L \sup_{\|f\|_{\mathrm{Lip}} \le 1} |X_f|
   \;\overset{\text{R2}}{=}\; L \sup_{f \in \mathcal{F}} |X_f|
   \;\overset{\text{R3}}{=}\; L \sup_{m \in \mathbb{N}}
      \max_{g \in N_m} |X_g|, $$
where $\mathcal{F}$ is the $[0,1]$-valued class (8.24) and $N_m$ is the
monotone finite exhaustion `lipschitzNetUnion m` of a countable
$L^\infty$-dense subfamily. No `Countable` hypothesis appears anywhere: the
recovery is deterministic, exactly as the fixed measurability/sup policy
prescribes.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, proof of Theorem 8.2.3, p. 230 (the two
"(Why?)" reductions to the class (8.24)) and Exercise 8.9 (density rate).

**Proof formalization notes.** All lemmas here are pointwise identities in
`ω`; no measure on `Ω` is involved. R1 (scaling) uses the bijection
`g ↦ L • g` with `empiricalProcess_const_mul`, `lipschitzWith_smul`, and
`Monotone.map_ciSup_of_continuousAt`; the degenerate `L = 0` case (0-Lipschitz
= constants, `X_const = 0`) is a separate lemma. R2 (translation) uses
`h := g − min g` (the min is attained: `g` continuous on the compact
`unitInterval`), `empiricalProcess_add_const` (`[NeZero n]`), and the range
bound from 1-Lipschitz-ness + `diam [0,1] ≤ 1`. R3 (dense net) uses the
deterministic oscillation bound `|X_f − X_g| ≤ 2 · dist f g`
(`abs_empiricalProcess_sub_le` + `ContinuousMap.dist_apply_le_dist`), density
`3/(m+1)` (`exists_mem_lipschitzNetUnion_dist_le`), and an ε-of-room
argument; `ℝ` is conditionally complete, so every `⨆` step carries explicit
`BddAbove` side conditions (`bddAbove_range_abs_empiricalProcess`, from
`|X_f| ≤ 2`). Edge behavior: `lipschitzNetUnion m` uses meshes `j + 1` so
every `lipschitzNet` call has its `NeZero` instance. Named-sorry fallback of
the work item `hdp-emp-dense`: `iSup_abs_empiricalProcess_eq_iSup_netUnion`
(R3; the R1/R2 rewrites must close for real).

**Bibliographic comments.** Reduction to a countable dense subclass is the
classical device for measurability of empirical suprema, systematized in
R. M. Dudley, *Uniform Central Limit Theorems*, Cambridge, 1999, §5.3, and
van der Vaart–Wellner, *Weak Convergence and Empirical Processes*, Springer,
1996, §1.7; HDP suppresses the issue (§8.2 footnote), and this file makes the
suppressed argument explicit.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure unitInterval} {n : ℕ} {X : Fin n → Ω → unitInterval}

open Classical in
/-- **Monotone finite exhaustion** of a countable `L∞`-dense subfamily of the
class (8.24): the union of the grid nets of mesh `1, …, m+1` (HDP §8.1
footnote p. 227 / Exercise 8.9). Edge behavior: meshes are `j + 1 ≥ 1`, so
`NeZero` instances are automatic; the union is monotone in `m` by
construction. -/
noncomputable def lipschitzNetUnion (m : ℕ) : Finset C(unitInterval, ℝ) :=
  (Finset.range (m + 1)).biUnion (fun j => lipschitzNet (j + 1))

/-- The exhaustion is nonempty (LEAN-ONLY; each grid net is nonempty). -/
theorem lipschitzNetUnion_nonempty (m : ℕ) : (lipschitzNetUnion m).Nonempty := by
  sorry

/-- The exhaustion is internal: `N_m ⊆ 𝓕` (LEAN-ONLY; each grid net is). -/
theorem lipschitzNetUnion_subset (m : ℕ) :
    ↑(lipschitzNetUnion m) ⊆ lipschitzUnitClass := by
  sorry

/-- The exhaustion is monotone (LEAN-ONLY; `biUnion` over a growing range). -/
theorem lipschitzNetUnion_mono : Monotone lipschitzNetUnion := by
  sorry

/-- Density at rate `3/(m+1)` (HDP Exercise 8.9): every class member is
within `L∞`-distance `3/(m+1)` of the `m`-th exhaustion stage. -/
theorem exists_mem_lipschitzNetUnion_dist_le {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (m : ℕ) :
    ∃ g ∈ lipschitzNetUnion m, dist f g ≤ 3 / (m + 1) := by
  sorry

/-- The supremand family is bounded above by `2` (LEAN-ONLY `BddAbove` side
condition for `ℝ`-valued `⨆`; from `|X_f| ≤ 2·‖f‖∞ ≤ 2` via
`abs_empiricalProcess_le`). -/
theorem bddAbove_range_abs_empiricalProcess [IsProbabilityMeasure P] (ω : Ω) :
    BddAbove (Set.range
      (fun f : lipschitzUnitClass =>
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|)) := by
  sorry

/-- **R3, dense-net reduction** (measurability/sup policy; HDP §8.2): the
full supremum over the uncountable class (8.24) equals the countable
monotone limit of finite maxima over the exhaustion — deterministically, for
every `ω`. Engine: `|X_f − X_g| ≤ 2 · dist f g` + density `3/(m+1)` +
ε-of-room. Named-sorry fallback of `hdp-emp-dense`. -/
theorem iSup_abs_empiricalProcess_eq_iSup_netUnion [IsProbabilityMeasure P]
    (ω : Ω) :
    (⨆ f : lipschitzUnitClass,
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|)
      = ⨆ m : ℕ, (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
          (fun g => |empiricalProcess P n X ⇑g ω|) := by
  sorry

/-- **R2, translation reduction** (HDP §8.2 p. 230, "(Why?)"): the supremum
over the 1-Lipschitz class equals the supremum over the `[0,1]`-valued class
(8.24), via `h := g − min g` (min attained on the compact domain) and
translation invariance `X_{g+c} = X_g`. -/
theorem iSup_abs_empiricalProcess_lipOne_eq [IsProbabilityMeasure P]
    [NeZero n] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith 1 f},
        |empiricalProcess P n X (↑f) ω|)
      = ⨆ f : lipschitzUnitClass,
          |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω| := by
  sorry

/-- **R1, scaling reduction** (HDP §8.2 p. 230, "(Why?)"): for `L ≠ 0`, the
supremum over the `L`-Lipschitz class is `L` times the supremum over the
1-Lipschitz class, via the bijection `f ↦ L • f` and
`Monotone.map_ciSup_of_continuousAt`. -/
theorem iSup_abs_empiricalProcess_lip_smul {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scaling (L = 0 is `iSup_abs_empiricalProcess_lipZero_eq`); no scope change
    (hL : L ≠ 0) [IsProbabilityMeasure P] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith L f},
        |empiricalProcess P n X (↑f) ω|)
      = (L : ℝ) * ⨆ f : {f : unitInterval → ℝ // LipschitzWith 1 f},
          |empiricalProcess P n X (↑f) ω| := by
  sorry

/-- Degenerate scaling `L = 0` (LEAN-ONLY edge case): 0-Lipschitz functions
are constants, and constants are invisible to the empirical process, so the
supremum vanishes. -/
theorem iSup_abs_empiricalProcess_lipZero_eq [IsProbabilityMeasure P]
    [NeZero n] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith 0 f},
        |empiricalProcess P n X (↑f) ω|) = 0 := by
  sorry

end StatLean.ConcentrationInequalities
