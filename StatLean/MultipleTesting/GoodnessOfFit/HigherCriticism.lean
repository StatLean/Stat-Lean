import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Higher Criticism and the detection boundary (Candès, Lecture 3, §3.3.3, Theorem 3)

Tukey's Higher-Criticism statistic and the Ingster–Donoho–Jin **detection boundary** for sparse
Gaussian mixtures (Candès, Lecture 3, §3.3.3). For the sparse mixture
`Xᵢ ∼ (1−εₙ)·N(0,1) + εₙ·N(μₙ,1)` with sparsity `εₙ = n^{−β}` (`1/2 < β < 1`) and signal
`μₙ = √(2r log n)`, the detection boundary is

`ρ*(β) = β − 1/2`           for `1/2 < β < 3/4`,
`ρ*(β) = (1 − √(1−β))²`     for `3/4 ≤ β ≤ 1`.

We formalize the two genuinely formalizable ingredients:

* `rhoStar β` — the detection boundary, a concrete piecewise function, with its basic properties
  (`rhoStar_continuous_at_junction`, `rhoStar_nonneg`, `rhoStar_one`);
* `hcStat p α₀ ω` — the Higher-Criticism statistic `max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)`.

## Deferred: the detection theorem (Donoho–Jin 2004) — research target, NOT stated as Lean

**Theorem 3 (Donoho & Jin).** *Above the boundary* (`r > ρ*(β)`), the Higher-Criticism test that
rejects when `HC*ₙ ≥ √((1+δ)·2 log log n)` has total error `P₀(type I) + P₁(type II) → 0` as
`n → ∞`; *below* it (`r ≤ ρ*(β)`) every test has `liminf (P₀ + P₁) ≥ 1` (Ingster).

This is **not** stated as a Lean theorem here, deliberately: a faithful statement is an asymptotic
over a sequence of sparse-mixture models, and encoding it now would require laundering unproven
asymptotics through hypotheses (CLAUDE.md §2 forbids this). What the proof needs, and its status:

* **Donsker invariance** (`√n(F̂ₙ−F) ⇒` Brownian bridge) — **available in this project**:
  `StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker` (`IsPDonsker`) +
  `isPDonsker_of_finite_bracketing_entropy_integral` (the half-line indicator class
  `{𝟙(−∞,t]}` has finite bracketing entropy, hence is `P`-Donsker). So the `H₀` empirical-process
  convergence underlying `hcStat` is reachable here — a tractable future sub-result.
* **Empirical-process LIL** (`max_{1/n≤t≤α₀} Wₙ(t)/√(2 log log n) →ᵈ 1`, calibrating the
  `√(2 log log n)` threshold) — **not yet available**; finer than Donsker (an iterated-logarithm /
  extreme-value statement for the normalized process near `0`).
* **Sparse-mixture large deviations** (the `H₁` detection above `ρ*(β)`) — **not yet available**.

So with the project's Donsker the `H₀` half is now within reach; the full Theorem 3 awaits the LIL
calibration + the `H₁` large-deviation analysis. Recorded as the TODO §"Batch 8" research target.
-/

open MeasureTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The **Ingster–Donoho–Jin detection boundary** `ρ*(β)` for sparse Gaussian mixtures
(Candès, Lecture 3, §3.3.3): `β − 1/2` for `1/2 < β < 3/4`, and `(1 − √(1−β))²` for `3/4 ≤ β ≤ 1`. -/
noncomputable def rhoStar (β : ℝ) : ℝ :=
  if β < 3 / 4 then β - 1 / 2 else (1 - Real.sqrt (1 - β)) ^ 2

/-- The two pieces of `rhoStar` agree at the junction `β = 3/4`
(`3/4 − 1/2 = 1/4 = (1 − √(1/4))²`): the boundary is continuous there. -/
theorem rhoStar_continuous_at_junction :
    (3 / 4 : ℝ) - 1 / 2 = (1 - Real.sqrt (1 - 3 / 4)) ^ 2 := by
  sorry

/-- The detection boundary is nonnegative on the sparse range `1/2 < β ≤ 1`. -/
theorem rhoStar_nonneg {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β ≤ 1) : 0 ≤ rhoStar β := by
  sorry

/-- At the densest sparse endpoint `β = 1`, `ρ*(1) = 1` (the Bonferroni detection threshold). -/
theorem rhoStar_one : rhoStar 1 = 1 := by
  sorry

/-- The **Higher-Criticism statistic** `HC*ₙ = max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)` (Candès,
Lecture 3, §3.3.3; `F̂ₙ` is the empirical CDF `empiricalCDF p`). -/
noncomputable def hcStat (p : Fin n → Ω → ℝ) (α₀ : ℝ) (ω : Ω) : ℝ :=
  ⨆ α ∈ Set.Ioc (0 : ℝ) α₀,
    (empiricalCDF p α ω - α) / Real.sqrt (α * (1 - α) / (n : ℝ))

end StatLean.MultipleTesting
