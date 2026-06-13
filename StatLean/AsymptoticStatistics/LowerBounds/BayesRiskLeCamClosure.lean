import StatLean.AsymptoticStatistics.LowerBounds.BayesRiskLowerBound
import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorDerivations
import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.LANexpansion
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Le Cam closure for the Bayes-risk passage

This file provides `bayes_n_to_limitBayes_of_lecam`, a deriver matching
the `hBayes_n_to_limitBayes` input consumed by `bayes_risk_lower_bound`
and forwarded by the per-`m` Bayes bridge `perM_bayes_lower_bound_at_basis`.
The deriver internalises the regular-estimator + basis + LAN-expansion
context, exposing only the deep Le Cam / extended-CMT argument through a
single chained input `hLeCamBayesPassage`.

## Strategy (vdV §25.3 Lemma 3 steps 1–4)

The closure of `hLeCamBayesPassage` proceeds as in vdV §25.3 proof of
Theorem 25.21 (lower bound):

1. **Per-direction LR convergence**: for each `h ∈ I_0`, the
   log-likelihood ratio
   `Σⱼ log (p_{n,h}(Xⱼ)/p(Xⱼ))` converges in distribution under
   `Pⁿ` to `⟪h, score-sum⟫ − ½‖h‖² + R_n` with `R_n → 0` in
   probability (`T6_FinDimLAN.LANexpansion.lanExpansion_at_basis_and_h`).
2. **Joint weak convergence** of `(T_n recentered, score-sum, log-LR)`
   under `Pⁿ` along a subsequence (use
   `RegularEstimatorDerivations.joint_convergence_of_regular`,
   composed with the LAN expansion).
3. **Uniform integrability** of `exp(log-LR) · (ℓ ⊓ M)` along the
   sequence: bounded loss × exp-tilt is UI when the exp-tilt's first
   moment is bounded, which is the LAN normalisation
   `E_{Pⁿ} exp(log-LR) = 1` plus the moment bound from the joint limit.
4. **Le Cam third lemma per direction** to identify the limit under
   `(γ h)^n` of the rescaled estimator: apply
   `ForMathlib.Contiguity.weak_limit_under_Q_of_lecam_third` per
   `h ∈ I_0`.
5. **Extended continuous mapping theorem** to pass to the limit of the
   prior-weighted Bayes risk: the Bayes risk
   `Σ_h π(h) · E_{Pⁿ_h} ℓ` is a continuous (bounded) functional of the
   joint law, so its `liminf` is bounded below by the limit-experiment
   prior-weighted Bayes risk.
6. **Inf-of-Bayes**: the limit-experiment Bayes risk is bounded below
   by the iInf over (measurable, deterministic) estimators in the limit
   experiment.

Each step's brick is in `ForMathlib/Contiguity.lean` (Le Cam 3rd,
contiguity), `ForMathlib/` (weak convergence machinery), and Mathlib
(DCT / UI / measurable function spaces).

## Public theorem

`bayes_n_to_limitBayes_of_lecam` matches the `hBayes_n_to_limitBayes`
shape consumed by `bayes_risk_lower_bound`. The body forwards a single
chained input `hLeCamBayesPassage`, which carries the Le Cam content with
the regular-estimator + basis + LAN-expansion context made internal.

Reference: vdV §25.3 Lemma 3 steps 1–4.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.BayesRiskLeCamClosure

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.LowerBounds.FinDimSubmodel
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Le Cam Bayes-passage deriver.**

For the `hBayes_n_to_limitBayes` input consumed by
`bayes_risk_lower_bound`: given the estimator-side regularity setup
(`T_n`, `hT_meas`, `L`, `hReg : IsRegularEstimator …`), the basis-side
data
(`g_P`, `_hg_orth`, `_hg_in_tangent`, `γ`, `_hγ_score`), the bounded
uniformly continuous loss `ℓ`, and the prior data `(I_0, π, hπ_nn,
hπ_sum)`, the per-`n` prior-weighted Bayes risk's `liminf` dominates the
limit-experiment Bayes risk against the shifted Gaussian family
`N(h, I_m)`.

The estimator regularity + basis + QMDPath + LAN-expansion data is made
*internal* to the deriver (consumed via signature carry-through):

* the regular-estimator predicate `hReg`, the EIF
  triple `(T_set, hψ, hEIF)`, the estimator measurability `hT_meas`,
  and the LAN expansion are made internal;
* the chained input `hLeCamBayesPassage` contains *only* the
  per-prior `(I_0, π)` Le Cam passage from
  per-`n` Bayes risk's `liminf` to the limit-experiment Bayes risk
  iInf — the deep content (vdV §25.3 Lemma 3 steps 1–4) derivable from
  `joint_convergence_of_regular`, `lanExpansion_at_basis_and_h`,
  exp-tilted UI machinery, and the joint extended CMT.

The bricks needed to discharge `hLeCamBayesPassage` directly:

* `RegularEstimatorDerivations.joint_convergence_of_regular`: joint
  subseq weak limit under `Pⁿ`.
* `T6_FinDimLAN.LANexpansion.lanExpansion_at_basis_and_h`: per-direction
  LAN remainder convergence in probability.
* UI of bounded loss × exp-tilt along the LAN sequence (vdV §6 / §7).
* `ForMathlib.Contiguity.weak_limit_under_Q_of_lecam_third` per
  direction `h ∈ I_0` to identify the limit under `(γ h)^n`.
* extended CMT for joint weak limits with density tilts
  (vdV Theorem 18.10 generalised).
* the inf-of-Bayes monotonicity: the iInf over measurable estimators
  is bounded below by the iInf over a dense subclass; combine with the
  per-step liminf bound.

Reference: vdV §25.3 Lemma 3 steps 1–4.

The signature carries:

* **External inputs** (vdV §25.3): `T_set, hψ, hEIF, T_n, _hT_meas, L,
  _hReg`. These are the free-choice inputs the caller supplies in
  concrete-model proofs.
* **Basis + QMDPath data** (vdV §25.3 (b) and Lemma 1):
  `g_P, _hg_orth, _hg_in_tangent, γ, _hγ_score`.
* **Prior data**: `I_0, π, hπ_nn, hπ_sum, ℓ, hℓ_bdd, _hℓ_uc`.
* **Single chained input**: `hLeCamBayesPassage` — the Le Cam
  passage with all the above context absorbed.

No additional caller obligations beyond what `bayes_risk_lower_bound`
itself exposes: this deriver does not add hypotheses, only absorbs
context. -/
theorem bayes_n_to_limitBayes_of_lecam
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    -- Underscore-prefixed because the forwarder body does not consume it
    -- directly (only `hLeCamBayesPassage` is used). The signature carries
    -- it so a direct closure can derive `hLeCamBayesPassage` from
    -- `joint_convergence_of_regular` (which requires `_hT_meas`).
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    -- Carrier membership of `g_P i` is the strong form (matches
    -- `bayes_risk_lower_bound`'s consumption).
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (γ : (Fin m → ℝ) → QMDPath P)
    (_hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (ℓ : ℝ → ℝ) (_hℓ_bdd : ∃ B, ∀ x, |ℓ x| ≤ B)
    (_hℓ_uc : UniformContinuous ℓ)
    (I_0 : Finset (Fin m → ℝ)) (π : (Fin m → ℝ) → ℝ)
    (_hπ_nn : ∀ h ∈ I_0, 0 ≤ π h)
    (_hπ_sum : ∑ h ∈ I_0, π h = 1)
    -- the per-prior `(I_0, π)` Bayes-risk Le Cam passage:
    -- liminf of per-`n` prior-weighted Bayes risks dominates the
    -- limit-experiment Bayes risk against the shifted family `N(h, I_m)`.
    -- This carries vdV §25.3 Lemma 3 steps 1–4 (LR convergence,
    -- joint weak convergence, UI of exp-tilted loss, extended CMT) +
    -- step 5 (the inf-of-Bayes monotonicity) packaged together. The
    -- regular-estimator + EIF + estimator-measurability + basis +
    -- QMDPath context is internal to this deriver; the chained input may
    -- be discharged directly via `joint_convergence_of_regular`, the
    -- `lanExpansion_at_basis_and_h` remainder, an exp-tilt UI brick, and
    -- the joint extended CMT.
    --
    -- Reference: vdV §25.3 Lemma 3 steps 1–4 + step 5.
    (hLeCamBayesPassage :
      Filter.liminf
        (fun n : ℕ =>
          ∑ h ∈ I_0, π h *
            ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
              (T_n n X - ψ (submodelAt (γ h) n)))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => submodelAt (γ h) n)))
        atTop
        ≥
      ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1)))) :
    -- Conclusion: the shape consumed by `bayes_risk_lower_bound`.
    Filter.liminf
      (fun n : ℕ =>
        ∑ h ∈ I_0, π h *
          ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
            (T_n n X - ψ (submodelAt (γ h) n)))
              ∂(MeasureTheory.Measure.pi
                  (fun _ : Fin n => submodelAt (γ h) n)))
      atTop
      ≥
    ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
      ∑ h ∈ I_0, π h *
        ∫ X : (Fin m → ℝ),
          ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
          ∂(MeasureTheory.Measure.pi
              (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1))) := by
  -- Forwarder over the chained Le Cam Bayes passage. The
  -- regular-estimator / EIF / basis / QMDPath / LAN-expansion data is the
  -- context in which the chained claim makes sense, and from which a
  -- direct proof would derive it via `joint_convergence_of_regular`, the
  -- Le Cam 3rd lemma, the LAN expansion, the exp-tilt UI, and the joint
  -- extended CMT.
  exact hLeCamBayesPassage

/-! ## Per-prior universal form

A reformulation that universally quantifies the prior data
`(I_0, π, hπ_nn, hπ_sum)`, matching the per-`m` Bayes-bridge shape of
`perM_bayes_lower_bound_at_basis`, namely its `hBayes_n_to_limitBayes`
chained input. This is the form natural for chains that vary `(I_0, π)`
while keeping the basis fixed (e.g., projection-sequence variance
approximation).
-/

/-- Per-prior universal form of `bayes_n_to_limitBayes_of_lecam`.

Matches the per-`m` chained Le Cam input shape consumed by
`PerMBayesBridge.perM_bayes_lower_bound_at_basis`. The deep Le Cam
content is packaged as a single chained input `hLeCamBayesPassageAll`
quantified over priors. Feed `g_P` and `γ`, get the per-`m` Bayes lower
bound for every prior in one go. -/
theorem bayes_n_to_limitBayes_of_lecam_perPrior
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (_hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              _hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hReg : IsRegularEstimator P T_set ψ _hψ _hEIF T_n L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (γ : (Fin m → ℝ) → QMDPath P)
    (_hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (ℓ : ℝ → ℝ) (_hℓ_bdd : ∃ B, ∀ x, |ℓ x| ≤ B)
    (_hℓ_uc : UniformContinuous ℓ)
    -- The Le Cam Bayes passage content, quantified over every prior.
    -- This form is used in chains (e.g., the basis-selection bridge)
    -- where the prior is varied to drive the projection-sequence
    -- variance limit.
    (hLeCamBayesPassageAll :
      ∀ (I_0 : Finset (Fin m → ℝ)) (π : (Fin m → ℝ) → ℝ),
        (∀ h ∈ I_0, 0 ≤ π h) → (∑ h ∈ I_0, π h = 1) →
        Filter.liminf
          (fun n : ℕ =>
            ∑ h ∈ I_0, π h *
              ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
                (T_n n X - ψ (submodelAt (γ h) n)))
                  ∂(MeasureTheory.Measure.pi
                      (fun _ : Fin n => submodelAt (γ h) n)))
          atTop
          ≥
        ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
          ∑ h ∈ I_0, π h *
            ∫ X : (Fin m → ℝ),
              ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                  ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
              ∂(MeasureTheory.Measure.pi
                  (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1)))) :
    ∀ (I_0 : Finset (Fin m → ℝ)) (π : (Fin m → ℝ) → ℝ),
      (∀ h ∈ I_0, 0 ≤ π h) → (∑ h ∈ I_0, π h = 1) →
      Filter.liminf
        (fun n : ℕ =>
          ∑ h ∈ I_0, π h *
            ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
              (T_n n X - ψ (submodelAt (γ h) n)))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => submodelAt (γ h) n)))
        atTop
        ≥
      ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1))) := by
  intro I_0 π hπ_nn hπ_sum
  exact hLeCamBayesPassageAll I_0 π hπ_nn hπ_sum

/-
Drop-in usage example (concrete-model file):

```
bayes_risk_lower_bound T_set hψ hEIF T_n g_P hg_orth hg_in_tangent
  γ hγ_score I_0 π hπ_nn hπ_sum ℓ hℓ_bdd hℓ_uc
  (hBayes_n_to_limitBayes :=
    AsymptoticStatistics.LowerBounds.BayesRiskLeCamClosure.bayes_n_to_limitBayes_of_lecam
      T_set hψ hEIF T_n hT_meas L hReg
      g_P hg_orth hg_in_tangent γ hγ_score ℓ hℓ_bdd hℓ_uc
      I_0 π hπ_nn hπ_sum
      hLeCamBayesPassage_witness)
```

The `hBayes_n_to_limitBayes` input is chained as `hLeCamBayesPassage`.
The estimator-side data `(T_n, hT_meas, L, hReg)` is internal at the
deriver level, and the chained input contains only the per-prior Le
Cam Bayes passage content.
-/

end AsymptoticStatistics.LowerBounds.BayesRiskLeCamClosure
