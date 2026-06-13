import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Score CLT — multivariate adapter for Theorem 7.10

This file provides the **score-sum CLT** in the form needed by Theorem 7.10
(`AsymptoticStatistics.AsymptoticRepresentation`). It is a thin adapter on top
of the project's underlying iid multivariate CLT brick
`ProbabilityTheory.tendstoInDistribution_multivariate_clt`
(in `AsymptoticStatistics/ForMathlib/MultivariateCLT.lean`).

## Why a separate file?

Theorem 7.10's proof builds an *abstract* iid setup `(P, Y)` on `(ℕ → 𝓧)` from a
parametric family `(M, μ, θ₀, ℓ)`. The CLT is consumed in the form

    WeakConverges (fun n => P.map (fun ω => (√n)⁻¹ • ∑ i ∈ range n, Y i ω))
                  (multivariateGaussian 0 J)

with hypotheses that match what the call site has on hand:

* zero mean of `Y 0` *via inner products*: `∀ u, ∫ ⟪u, Y 0 ω⟫ ∂P = 0`,
* covariance of `Y 0` *as a quadratic form on `EuclideanSpace ℝ (Fin k)`*:
  `∀ u v, ∫ ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P = u.ofLp ⬝ᵥ J.mulVec v.ofLp`.

The underlying `MultivariateCLT` brick is stated more generically (with witness
`Y' : Ω' → ℝ^k` and an arbitrary `P'`); this adapter specialises to the
`Y' := id`, `P' := multivariateGaussian 0 J` case and converts
`MeasureTheory.TendstoInDistribution` into our test-function-based
`WeakConverges`.

## Main result

* `AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`: weak convergence of the
  scaled abstract score sum to `multivariateGaussian 0 J`, under the
  inner-product zero-mean / covariance / `MemLp 2` package.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped Real Topology RealInnerProductSpace ENNReal Matrix
open AsymptoticStatistics

namespace AsymptoticStatistics.ParametricFamily
namespace ScoreCLT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Multivariate score CLT (finite-dimensional, abstract iid form).**

For an iid sequence `Y i : Ω → EuclideanSpace ℝ (Fin k)` under a probability
measure `P`, with **zero mean** (in the inner-product sense) and **covariance
matrix `J`** (in the inner-product sense), the standardised sum
`(√n)⁻¹ • ∑_{i<n} Y i` converges weakly to `multivariateGaussian 0 J`.

This is the abstract iid form consumed by `AsymptoticRepresentation` after it has built the
Kolmogorov-extension setup `P := Measure.infinitePi (fun _ => ν)` and the
coordinate map `Y i ω := ℓ (ω i)`. The hypotheses are stated against `P` and
`Y 0` directly so the call site can plug in its already-derived score
mean-zero (from `Score.score_mean_zero`) and Fisher-information identity
(from `fisherInformation` definition + the user-supplied matrix bridge `hJ`)
without further manipulation. -/
theorem clt_finDim
    (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ}
    (Y : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_iid : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    -- (consequence of DQM via `Score.score_mean_zero`).
    (h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫ ∂P = 0)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ_psd : J.PosSemidef)
    -- vdV §7.10 (Fisher-information identity, supplied by the call site).
    (h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P = u.ofLp ⬝ᵥ J.mulVec v.ofLp)
    -- (DQM gives Fisher integrability ⇒ `MemLp 2`).
    (h_L2 : MemLp (Y 0) 2 P) :
    WeakConverges
      (fun n : ℕ => P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := by
  classical
  -- Integrability of `Y 0` from the L² hypothesis.
  have h_int_Y0 : Integrable (Y 0) P := h_L2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- `P[Y 0] = 0` from `h_zero_mean` via `integral_eq_zero_of_forall_integral_inner_eq_zero`.
  have h_E_Y0 : P[Y 0] = (0 : EuclideanSpace ℝ (Fin k)) := by
    refine integral_eq_zero_of_forall_integral_inner_eq_zero (𝕜 := ℝ) (Y 0) h_int_Y0 ?_
    intro c
    exact h_zero_mean c
  -- Variance identity: `Var[⟪t, Y 0⟫; P] = t ⬝ᵥ J *ᵥ t`.
  have h_var : ∀ t : EuclideanSpace ℝ (Fin k),
      Var[fun ω => ⟪t, Y 0 ω⟫; P] = t ⬝ᵥ J *ᵥ t := by
    intro t
    have h_AEM : AEMeasurable (fun ω => ⟪t, Y 0 ω⟫) P :=
      ((Measurable.const_inner (c := t) (hY_meas 0))).aemeasurable
    have h_int_zero : ∫ ω, ⟪t, Y 0 ω⟫ ∂P = 0 := h_zero_mean t
    rw [variance_of_integral_eq_zero h_AEM h_int_zero]
    -- `∫ ⟪t, Y 0 ω⟫ ^ 2 = ∫ ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫ = t.ofLp ⬝ᵥ J.mulVec t.ofLp = t ⬝ᵥ J *ᵥ t`.
    have h_sq : (fun ω => ⟪t, Y 0 ω⟫ ^ 2) = (fun ω => ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫) := by
      funext ω; rw [sq]
    -- The `rw [h_cov t t]` produces `t.ofLp ⬝ᵥ J.mulVec t.ofLp`, which is
    -- definitionally equal to `t ⬝ᵥ J *ᵥ t` (the goal) through `WithLp`.
    rw [h_sq, h_cov t t]
  -- Build the witness `id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)` with
  -- law `multivariateGaussian 0 J`.
  haveI hG_prob : IsProbabilityMeasure (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin k)) J) := inferInstance
  have hY_id : HasLaw
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) := HasLaw.id
  -- Apply the project's underlying multivariate iid CLT.
  have h_TID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))
        atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
        (fun _ => P)
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    tendstoInDistribution_multivariate_clt
      (P := P) (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J)
      (X := Y) (Y := id) (S := J) hJ_psd h_var hY_id h_L2 hY_iid hident
  -- Replace `n • P[Y 0]` by `0` using `h_E_Y0`, simplifying the standardised sum.
  have h_eq : ∀ n : ℕ,
      (fun ω => (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))
        = (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω) := by
    intro n
    funext ω
    rw [h_E_Y0, smul_zero, sub_zero]
  -- Convert `TendstoInDistribution` to `WeakConverges` via the `ProbabilityMeasure`
  -- characterisation `tendsto_iff_forall_integral_tendsto`.
  intro f
  -- Massage the goal so the integrand on the LHS matches `h_TID` after `h_eq`.
  -- `WeakConverges` unfolds to: `Tendsto (fun n => ∫ x, f x ∂(P.map …)) atTop (𝓝 …)`.
  -- The map measure `P.map (fun ω => (√n)⁻¹ • ∑ Y k ω)` agrees with the standardised
  -- one since `P[Y 0] = 0`.
  have h_map_eq : ∀ n : ℕ,
      P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω) =
      P.map (fun ω => (Real.sqrt n)⁻¹ •
        (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0])) := by
    intro n
    rw [h_eq n]
  -- Extract the `Tendsto`-on-`ProbabilityMeasure`-objects statement from `h_TID`.
  have h_PM := h_TID.tendsto
  -- Pull this through `tendsto_iff_forall_integral_tendsto` at the bdd-cts test `f`.
  have h_int_tendsto :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_PM) f
  -- Rewrite the LHS: the map measure equals the simpler `(√n)⁻¹ • ∑` map.
  -- The RHS is `(multivariateGaussian 0 J).map id = multivariateGaussian 0 J`.
  -- Both rewrites reduce `h_int_tendsto` to the goal up to the `ProbabilityMeasure`
  -- coercion, which is definitional.
  have h_map_id :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J :=
    Measure.map_id
  -- Rewrite the LHS index by `h_map_eq` and the RHS by `h_map_id`.
  simp only [h_map_id] at h_int_tendsto
  -- The remaining task is to identify the integral of `f` against the standardised-sum
  -- pushforward (with the `n • P[Y 0]` correction term) with the integral against the
  -- simpler pushforward (no correction term). These agree by `h_map_eq` since
  -- `P[Y 0] = 0`; substitute pointwise.
  have h_pointwise : ∀ n : ℕ,
      ∫ x, f x ∂(P.map
        (fun ω => (Real.sqrt n)⁻¹ • (∑ k_idx ∈ Finset.range n, Y k_idx ω - n • P[Y 0]))) =
      ∫ x, f x ∂(P.map
        (fun ω => (Real.sqrt n)⁻¹ • ∑ k_idx ∈ Finset.range n, Y k_idx ω)) := by
    intro n
    rw [← h_map_eq n]
  -- The `ProbabilityMeasure` coercion is definitional; `simpa` rewrites both sides.
  simpa [h_pointwise] using h_int_tendsto

end ScoreCLT
end AsymptoticStatistics.ParametricFamily
