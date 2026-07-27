/-
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The Gaussian boundary-shell bound for convex sets

For the standard Gaussian `γ = N(0, I_k)` on `EuclideanSpace ℝ (Fin k)` and a convex set `B`,
the mass of the `ε`-boundary shell of `B` is `O_k(ε)`:

`γ(Bᵋ) ≤ γ(B) + C_k ε`  and  `γ(B) ≤ γ(B_{-ε}) + C_k ε`,

where `Bᵋ` is the `ε`-thickening and `B_{-ε}` the `ε`-erosion. This is the missing ingredient of
the elementary convex Berry–Esseen bound
`StatLean.HypothesisTesting.berryEsseen_convex_elementary`, where the *sharp* form of the constant
(K. Ball's `4 k^{1/4}` bound on the Gaussian surface area of a convex body) is what produces the
dimension factor `k^{1/4}` of Bentkus (2003). The elementary assembly only needs *finiteness* of
`C_k` at fixed `k`, and that is what is proved here, with the explicit constant
`C_k = 8 k^{3/2}/√(2π)` (`gaussianShellConst`).

## The argument

Everything rests on one elementary observation about convex sets and *coordinate lines*.

* (Support) If `V` is convex and `x ∉ interior V` then some `u ≠ 0` supports `V` at `x`:
  `⟪u, w - x⟫ ≤ 0` for all `w ∈ V` (`exists_inner_le_zero_of_notMem_interior`). For
  `interior V ≠ ∅` this is `geometric_hahn_banach_open_point` applied to `interior V`, extended to
  `closure (interior V) = closure V ⊇ V`; for `interior V = ∅` the affine span of `V` is a proper
  affine subspace and `u` is taken orthogonal to its direction.
* (Escape) Some coordinate of a unit vector is at least `1/√k` in absolute value, so moving from
  `x` by `± c` along that coordinate axis moves *away* from the supporting hyperplane by at least
  `c/√k`; hence `infDist (x ± c • eᵢ) V ≥ c/√k` (`infDist_add_smul_single_ge`).
* (Slice) For a convex `V` and a coordinate `i`, the set `{x ∈ V : x + c • eᵢ ∉ V}` meets every
  line parallel to `eᵢ` in a set of diameter `≤ |c|` — because the trace of `V` on such a line is
  an interval. Its Gaussian mass is therefore at most `2|c|/√(2π)`, by Fubini for
  `γ = ⨂ N(0,1)` (`map_pi_eq_stdGaussian`) and the `1/√(2π)` bound on the one-dimensional
  Gaussian density (`gaussian_mem_notMem_shift_le`). This step is where the Gaussian enters; note
  that the bound is *dimension-free*, the factor `k^{3/2}` coming only from the `2k` coordinate
  directions and the `√k` loss in the escape step.

Combining: the shell `Bᵋ \ B` (resp. `B \ B_{-ε}`) is covered by the `2k` sets
`{x ∈ Bᵋ : x ± c • eᵢ ∉ Bᵋ}` with `c = 2ε√k`, giving `γ(shell) ≤ 2k · 2c/√(2π) = C_k ε`.

The same covering with `c → 0` shows `γ(V \ interior V) = 0` for every convex `V`
(`gaussian_diff_interior_eq_zero`), which is the degenerate case (`interior B = ∅`, i.e. `B` inside
a hyperplane) of the erosion bound.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped RealInnerProductSpace ENNReal NNReal Real

namespace StatLean.HypothesisTesting

section GaussianShell

variable {k : ℕ}

/-! ### One-dimensional density bounds -/

/-- The standard normal law is dominated by `(2π)^{-1/2}` times Lebesgue measure: its density is
bounded by the peak value `(2π)^{-1/2}`. -/
lemma gaussianReal_le_smul_volume (A : Set ℝ) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
  have hbound : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * π))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - 0)]
    have hpos : (0 : ℝ) ≤ (Real.sqrt (2 * π * 1))⁻¹ := by positivity
    calc gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
      _ ≤ (Real.sqrt (2 * π * 1))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = (Real.sqrt (2 * π))⁻¹ := by norm_num
  rw [gaussianReal_apply 0 one_ne_zero A]
  calc ∫⁻ x in A, gaussianPDF 0 1 x
      ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ := by
        refine lintegral_mono fun x => ?_
        exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
        rw [setLIntegral_const]

/-- A set of diameter at most `c` has standard normal mass at most `2c/√(2π)`. -/
lemma gaussianReal_le_of_diam_le {A : Set ℝ} {c : ℝ}
    (h : ∀ s ∈ A, ∀ t ∈ A, |s - t| ≤ c) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  · have hsub : A ⊆ Set.Icc (t₀ - c) (t₀ + c) := by
      intro s hs
      have := h s hs t₀ ht₀
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    calc gaussianReal 0 1 A
        ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := gaussianReal_le_smul_volume A
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume (Set.Icc (t₀ - c) (t₀ + c)) := by
          gcongr
      _ = ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : t₀ + c - (t₀ - c) = 2 * c := by ring
          rw [this]
          field_simp

/-! ### The Gaussian as a product measure -/

/-- `N(0, I_k)` is the pushforward of the `k`-fold product of `N(0,1)` under the (identity)
`toLp` map. This is `map_pi_eq_stdGaussian` combined with `multivariateGaussian_zero_one`. -/
lemma multivariateGaussian_eq_map_pi (k : ℕ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (WithLp.toLp 2) := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]

end GaussianShell

end StatLean.HypothesisTesting
