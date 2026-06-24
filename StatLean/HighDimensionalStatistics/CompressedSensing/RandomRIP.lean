import StatLean.HighDimensionalStatistics.CompressedSensing.GaussianChiSquared
import StatLean.HighDimensionalStatistics.CompressedSensing.Defs
import StatLean.ConcentrationInequalities.Maximal.CoveringBall

/-!
# Random Gaussian matrices are RIP with high probability (Lu §7, `thm:3s-rip`)

**Theorem.** If `X ∈ ℝ^{n×d}` has i.i.d. `N(0,1/n)` entries and
`n ≥ (96/δ²)·s·log(18d/ε)`, then `P(X is 3s-RIP with constant δ) ≥ 1 − ε`.

Proof (book):
1. *Fixed `β`:* `‖Xβ‖²/‖β‖² ∼ (1/n)χ²_n` concentrates — `gaussian_quadratic_form_tail`
   (`GaussianChiSquared.lean`): `P(|‖Xβ‖²/‖β‖²−1| > δ) ≤ 2 exp(−nδ²/8)`.
2. *Net:* a `1/4`-net of the unit ball in `ℝ^{3s}` has `≤ 9^{3s}` points
   (`coveringNumber_closedBall_le` at `ε=1/4`), and `sup_{ball}|·| ≤ 2 sup_{net}|·|`.
3. *Union bound* over the `C(d,3s)` supports `×` the net, each event at `δ/2`, gives
   `P(¬RIP) ≤ C(d,3s)·9^{3s}·2 exp(−nδ²/32)`.
4. *Sample size:* `log C(d,3s) ≤ 3s·log(…)` collapses the bound to `≤ ε` under `hn`,
   so `P(RIP) = 1 − P(¬RIP) ≥ 1 − ε`.

Constants (`96`, `18`, `8/32`) are the book's; the proof states the provable form and
documents any deviation. The random matrix is `X : Ω → Matrix (Fin n) (Fin d) ℝ` over a
probability space `(Ω, μ)`.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal NNReal InnerProductSpace
open StatLean.ConcentrationInequalities

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Random matrix is `3s`-RIP w.h.p.** (Lu, *Big Data Analysis* §7, `thm:3s-rip`).
For an i.i.d. `N(0,1/n)` matrix `X` and `n ≥ (96/δ²)·s·log(18d/ε)`,
`P(X is 3s-RIP with constant δ) ≥ 1 − ε`. -/
theorem prob_rip_of_iid_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (δ ε : ℝ)
    -- USER-INPUT: 0 < δ < 1 (target RIP constant); Lu-BDA §7 (thm:3s-rip)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: 0 < ε (target failure probability); Lu-BDA §7 (thm:3s-rip)
    (hε0 : 0 < ε)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    -- USER-INPUT: the entries Xᵢⱼ are jointly independent; Lu-BDA §7 (thm:3s-rip)
    (hindep : iIndepFun (fun (p : Fin n × Fin d) ω => X ω p.1 p.2) μ)
    -- USER-INPUT: each entry Xᵢⱼ ∼ N(0,1/n); Lu-BDA §7 (thm:3s-rip)
    (hlaw : ∀ i j, Measure.map (fun ω => X ω i j) μ
              = gaussianReal 0 (⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ : ℝ≥0))
    -- USER-INPUT: sample-size lower bound n ≥ (96/δ²)·s·log(18d/ε); Lu-BDA §7 (thm:3s-rip)
    (hn : (n : ℝ) ≥ (96 / δ ^ 2) * (s : ℝ) * Real.log (18 * (d : ℝ) / ε)) :
    μ {ω | IsRIP (X ω) (3 * s) δ} ≥ 1 - ENNReal.ofReal ε := by
  sorry

end StatLean.HighDimensionalStatistics
