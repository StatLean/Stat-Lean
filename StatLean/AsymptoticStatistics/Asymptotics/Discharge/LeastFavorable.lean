import StatLean.AsymptoticStatistics.Asymptotics.LeastFavorable
import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
import StatLean.AsymptoticStatistics.ParametricFamily.BartlettIdentity

/-!
# MLE via approximate least-favorable submodel: discharge layer

Closes the bundled `asympLinear_25_77` field of `ApproxLeastFavAssumptions`
(vdV thm:25.77) from book-level primitives.

vdV's own argument (§25.11, p.409) reduces thm:25.77 to thm:25.54 verbatim:
"For easy reference we reformulate the theorem. Theorem 25.54, with `ℓ̃`
replaced by `κ̃`, yields the asymptotic efficiency of `θ̂_n`." The only extra
content over thm:25.54 is that the estimated scores `κ̃_{θ,η}` are *proper*
score functions of approximately-least-favorable submodels (eq:25.75 at the
origin), whose value at the true parameter `(θ₀,η₀)` equals the efficient
score `ℓ̃`. The MLE's first-order stationarity along the submodel supplies the
estimating equation `√n · 𝕡_n κ̃_{θ̂_n,η̂_n} = o_P(1)` that drives the 25.54
argument.

This file therefore **instantiates the existing 25.54 Taylor discharge**
(`zEstimator_asympLinear_of_taylor`) with the least-favorable submodel scores,
rather than re-proving the Donsker / Taylor empirical-process analysis. The
single substantive bridge is the least-favorable identity (eq:25.75 at `s = 0`):
it converts the abstract efficient-score representative used by the 25.54 layer
(`score_truth =ᵐ efficientScore`) into the submodel-score representative
(`score_truth =ᵐ (submodel_path 0).score`), so the `submodel_score_at_zero`
identity, although unused by the final assembly proof, is required by the
discharge theorem that constructs its asymptotic-linearity premise.

Reference: vdV §25.11 — eq:25.75 (no-bias, p.409), eq:25.76 (Donsker /
L²-consistency, p.409), thm:25.77 (MLE semiparametric efficiency, p.409);
inherits vdV §25.5 (thm:25.54) machinery + §7.2 (Theorem 7.2, Lemma 7.6)
DQM-Taylor. Headline declarations: `LeastFavorableTaylorHyp`,
`mle_asympLinear_of_leastFavorable`, `toApproxLeastFavAssumptions`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.LeastFavorable

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.LeastFavorable
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
open AsymptoticStatistics.Asymptotics.Discharge.ZEstimator.ZEstimatorTaylorCore
open AsymptoticStatistics.EmpiricalProcess

variable {Ω : Type} [MeasurableSpace Ω]

/-- *Book-level primitives for vdV thm:25.77 (MLE semiparametric efficiency
via an approximately-least-favorable submodel).*

Mirrors `ZEstimatorTaylorCore` (the 25.54 Taylor discharge bundle), with two
differences that encode vdV's "proper score function" reduction (§25.11):

1. the model carries an **approximately-least-favorable submodel**
   `submodel_path : Θ → QMDPath P` (vdV §25.11, eq:25.75), and the truth
   representative `score_truth` is tied to the **submodel score at the
   origin** `(submodel_path 0).score` rather than to the abstract efficient
   score directly (field `truth_aeEq`);
2. the least-favorable identity at `s = 0` (field `submodel_score_at_zero`,
   vdV §25.11 eq:25.75) bridges the two: `(submodel_path 0).score = ℓ̃`. This
   is the *only* substantive addition over thm:25.54; it is what converts the
   submodel-score representative into the efficient-score representative that
   the 25.54 argument consumes via Lemma 19.24.

All remaining fields are the thm:25.54 primitives, re-indexed against
`κ̃_{θ̂_n,η̂_n} = score_func_seq` (the estimated submodel scores) instead of
`ℓ̃_{θ̂_n,η̂_n}`. The estimating equation `score_eq` is, in the MLE setting, the
first-order stationarity of the log-likelihood along the submodel
(`√n · 𝕡_n κ̃_{θ̂_n,η̂_n} = o_P(1)`; vdV §25.11 p.409, "the function
`t ↦ log lik(…)` is maximal at `t = 0` and hence … satisfies the stationary
equation").

**Parameters** (in addition to the standard model identity):
- `submodel_path : Θ → QMDPath P` — the approximately-least-favorable
  parametric submodel (vdV §25.11, eq:25.75).
- `score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)` — the random function
  `(n, X) ↦ κ̃_{θ̂_n(X), η̂_n(X)}` (estimated submodel score), viewed as a
  measurable element of `L²(P)` per sample.
- `score_truth : Ω → ℝ` — a measurable representative of the submodel score at
  the origin `(submodel_path 0).score`, equal `P`-a.e. (and, via
  `submodel_score_at_zero`, to `ℓ̃`).
- `donsker_class : Set (Ω → ℝ)` — the `P_{θ₀,η₀}`-Donsker class with
  square-integrable envelope containing `score_truth` and (w.p.a.1) the random
  functions `score_func_seq n` (vdV §25.11, eq:25.76 / thm:25.77 hyp).
- `score_l_dot : Lp ℝ 2 P` — the L²(P)-derivative `κ̇` of `θ ↦ κ̃_{θ,η}` at θ₀
  (vdV §7.2 Lemma 7.6 derivative).

Reference: vdV §25.11, thm:25.77; eq:25.75, eq:25.76 (book primitives);
inherits vdV §25.5 thm:25.54 + Lemma 19.24 + §7.2. -/
structure LeastFavorableTaylorHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (submodel_path : Θ → QMDPath P)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop where
  /-- vdV §25.11 (eq:25.75 at `s = 0`): the submodel's score at the origin
  matches the efficient score of the full semiparametric model. Combined with
  `truth_aeEq`, this identity gives `score_truth =ᵐ ℓ̃`, the representative used
  by the thm:25.54 discharge to construct the asymptotic-linearity premise. -/
  submodel_score_at_zero :
    (submodel_path 0).score = efficientScore S_θ T_nuis v
  /-- vdV §25.4: efficient information `Ĩ_{θ₀,η₀}` is positive. Required to
  invert `Ĩ` in the influence function `(1/Ĩ) • ℓ̃`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- The truth representative `score_truth` is measurable. Feeds Lemma 19.24
  (via the thm:25.54 layer). -/
  truth_meas : Measurable score_truth
  /-- `score_truth` is in `L²(P)` (square-integrable envelope, vdV §25.11
  thm:25.77 hyp). -/
  truth_memLp : MemLp score_truth 2 P
  /-- The truth representative agrees `P`-a.e. with the submodel score at the
  origin. With `submodel_score_at_zero` this identifies `score_truth` with the
  efficient-score coercion the 25.54 discharge requires. -/
  truth_aeEq :
    ((((submodel_path 0).score : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ)
      =ᵐ[P] score_truth
  /-- vdV §25.11 thm:25.77 hyp: the truth `score_truth` belongs to the Donsker
  class. -/
  truth_in_donsker : score_truth ∈ donsker_class
  /-- vdV §25.11 thm:25.77 hyp / eq:25.76: the submodel scores form a
  `P_{θ₀,η₀}`-Donsker class (with square-integrable envelope, w.p.a.1). -/
  is_donsker : IsPDonsker donsker_class P
  /-- `score_func_seq n` is jointly measurable in (sample, ω). Empirical-process
  measurability boilerplate. -/
  score_func_meas : ∀ n,
    Measurable (fun p : (Fin n → Ω) × Ω => score_func_seq n p.1 p.2)
  /-- vdV §25.11 thm:25.77 hyp (w.p.a.1 form): each random submodel score
  `score_func_seq n X` belongs to the Donsker class. -/
  score_func_in_donsker : ∀ n (X : Fin n → Ω), score_func_seq n X ∈ donsker_class
  /-- vdV §25.11 (eq:25.76, expectation form): the L²(P)-distance between the
  estimated submodel scores `κ̃_{θ̂_n,η̂_n}` and the truth `κ̃_{θ₀,η₀}` tends to
  zero in expectation under `Pⁿ`. -/
  score_l2_consistency :
    Tendsto (fun n =>
      ∫ X, (∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P)
        ∂(Measure.pi (fun _ : Fin n => P)))
      atTop (𝓝 0)
  /-- Outer integrability of the squared L²-distance under `Pⁿ`
  (Vaart–Wellner §2.3 admissibility); strengthens `score_l2_consistency` to
  the integrability form consumed by the equicontinuity step. -/
  score_l2_int : ∀ n, MeasureTheory.Integrable
    (fun X : Fin n → Ω => ∫ x, (score_func_seq n X x - score_truth x) ^ 2 ∂P)
    (Measure.pi (fun _ : Fin n => P))
  /-- vdV §25.11 thm:25.77 hyp: the MLE `θ̂_n` is consistent for `θ₀` under
  `Pⁿ` ("provided that it is consistent", p.409). -/
  consistency : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | ε ≤ |estimator n X - θ₀|})
    atTop (𝓝 0)
  /-- `estimator n` is measurable for every `n`. Trivially holds for any
  concretely constructed MLE. -/
  estimator_meas : ∀ n, Measurable (estimator n)
  /-- vdV §7.2 (Theorem 7.2 + Lemma 7.6, DQM-in-θ Taylor identity for the
  submodel score `θ ↦ κ̃_{θ,η}`): the empirical L²-Taylor remainder
  `Σᵢ (κ̃_{θ̂_n,η̂_n}(X_i) − κ̃_{θ₀,η₀}(X_i) − (θ̂_n − θ₀)·κ̇(X_i))²` vanishes
  faster than `1/n` under `Pⁿ`. -/
  score_l2_taylor : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ ∑ i : Fin n,
          (score_func_seq n X (X i)
            - score_truth (X i)
            - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2})
    atTop (𝓝 0)
  /-- Semiparametric Bartlett identity `E_P[κ̇] = -Ĩ` (vdV §7.2, by
  differentiating `E_{P_{θ,η}}[κ̃_{θ,η}] = 0` in θ). -/
  score_l_dot_bartlett :
    ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v
  /-- vdV §25.11 (p.409, MLE first-order stationarity along the submodel):
  the MLE solves the estimating equation up to `o_P(n^{-1/2})`,
  `√n · 𝕡_n κ̃_{θ̂_n,η̂_n} = o_P(1)` under `Pⁿ`. ("`t ↦ log lik(θ + t, η_t(θ̂,η̂))`
  is maximal at `t = 0` and hence … satisfies the stationary equation.") -/
  score_eq : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |(Real.sqrt n)⁻¹ *
              (∑ i : Fin n, score_func_seq n X (X i))|})
    atTop (𝓝 0)

namespace LeastFavorableTaylorHyp

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {v : Θ}
variable {submodel_path : Θ → QMDPath P}
variable {estimator : ∀ n, (Fin n → Ω) → ℝ}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)}
variable {score_truth : Ω → ℝ}
variable {donsker_class : Set (Ω → ℝ)}
variable {score_l_dot : Lp ℝ 2 P}
variable {θ₀ : ℝ}

/-- *The `score_l_dot_bartlett` field is derived, not assumed.*

The semiparametric Bartlett identity `∫ κ̇ dP = −Ĩ` carried as the `score_l_dot_bartlett`
field of `LeastFavorableTaylorHyp` is a **consequence** of QMD regularity, not an independent
hypothesis on the submodel. It is the **diagonal** second Bartlett / information identity
`ParametricFamily.DifferentiableScoreSubmodel.bartlett_identity_diag`
(`∫ ℓ̇₀ dP = −∫ ℓ₀² dP`, obtained by differentiating the first Bartlett identity
`∫ ℓ_θ dP_θ = 0` under the integral sign), combined with the two identifications tying the
abstract efficient-score data to the concrete QMD submodel `M`:

* `h_dot` — the `L²(P)`-derivative representative `κ̇ = score_l_dot` coincides `P`-a.e. with
  the submodel score-derivative `M.scoreDot = ℓ̇₀`;
* `h_info` — the efficient information `Ĩ = efficientInformation S_θ T_nuis v` equals the
  Fisher information `∫ ℓ₀² dP` of the submodel score.

This adapter exhibits the derivation; it does **not** change the `LeastFavorableTaylorHyp`
signature. A caller constructing the bundle from a concrete QMD submodel supplies
`score_l_dot_bartlett := score_l_dot_bartlett_of_differentiableScoreSubmodel M h_diag h_dot
h_info`, so the field is discharged rather than assumed.

Reference: vdV §5.3 / §7.2 (Bartlett is a DQM consequence). -/
theorem score_l_dot_bartlett_of_differentiableScoreSubmodel
    (M : AsymptoticStatistics.ParametricFamily.DifferentiableScoreSubmodel P)
    (h_diag : M.densityScore = M.scoreCurve 0)
    (h_dot : (fun ω => (score_l_dot : Ω → ℝ) ω) =ᵐ[P] M.scoreDot)
    (h_info : ∫ ω, (M.scoreCurve 0 ω) ^ 2 ∂P = efficientInformation S_θ T_nuis v) :
    ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v :=
  calc ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P
      = ∫ ω, M.scoreDot ω ∂P := integral_congr_ae h_dot
    _ = - ∫ ω, (M.scoreCurve 0 ω) ^ 2 ∂P := M.bartlett_identity_diag h_diag
    _ = -efficientInformation S_θ T_nuis v := by rw [h_info]

/-- *Bridge: the least-favorable submodel primitives instantiate the thm:25.54
Taylor discharge bundle.*

Re-expresses a `LeastFavorableTaylorHyp` as the `ZEstimatorTaylorCore` bundle
expected by `zEstimator_asympLinear_of_taylor`. Every field is shared verbatim
except `truth_aeEq`: the LFM version compares `score_truth` against the submodel
score at the origin, and the least-favorable identity `submodel_score_at_zero`
(vdV §25.11 eq:25.75) rewrites that into the efficient-score comparison the
thm:25.54 layer requires.

Reference: vdV §25.11 p.409 ("Theorem 25.54, with `ℓ̃` replaced by `κ̃`"). -/
def toZEstimatorTaylorCore
    (h : LeastFavorableTaylorHyp P Θ S_θ T_nuis v submodel_path
            estimator score_func_seq score_truth donsker_class score_l_dot θ₀) :
    ZEstimatorTaylorCore P Θ S_θ T_nuis v
      estimator score_func_seq score_truth donsker_class score_l_dot θ₀ where
  hI_pos := h.hI_pos
  truth_meas := h.truth_meas
  truth_memLp := h.truth_memLp
  truth_aeEq := by
    -- `score_truth =ᵐ (submodel_path 0).score` rewritten through the
    -- least-favorable identity `(submodel_path 0).score = ℓ̃`.
    have hid := h.submodel_score_at_zero
    have hae := h.truth_aeEq
    rw [hid] at hae
    exact hae
  truth_in_donsker := h.truth_in_donsker
  is_donsker := h.is_donsker
  score_func_meas := h.score_func_meas
  score_func_in_donsker := h.score_func_in_donsker
  score_l2_consistency := h.score_l2_consistency
  score_l2_int := h.score_l2_int
  consistency := h.consistency
  estimator_meas := h.estimator_meas
  score_l2_taylor := h.score_l2_taylor
  score_l_dot_bartlett := h.score_l_dot_bartlett
  score_eq := h.score_eq

/-- *vdV thm:25.77 — discharge of `asympLinear_25_77` from book primitives.*

Given the least-favorable submodel primitives `LeastFavorableTaylorHyp`, the MLE
`estimator` is asymptotically linear at `P` with influence function
`(1/Ĩ_{θ₀,η₀}) • ℓ̃_{θ₀,η₀}` and centering `θ₀`.

Proof: reduce to thm:25.54 verbatim (vdV §25.11 p.409), i.e. instantiate
`zEstimator_asympLinear_of_taylor` with the least-favorable submodel scores via
`toZEstimatorTaylorCore`. -/
theorem mle_asympLinear_of_leastFavorable
    (h : LeastFavorableTaylorHyp P Θ S_θ T_nuis v submodel_path
            estimator score_func_seq score_truth donsker_class score_l_dot θ₀) :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀ :=
  zEstimator_asympLinear_of_taylor h.toZEstimatorTaylorCore

/-- **Least-favorable Taylor assumptions as an efficiency bundle.**

Constructs `ApproxLeastFavAssumptions` from `LeastFavorableTaylorHyp` and the
EIF-construction inputs `h_mem` and `h_dψ`. The score identity
`submodel_score_at_zero` is inherited from `h`, and `asympLinear_25_77` is supplied by
`mle_asympLinear_of_leastFavorable`.

Reference: vdV §25.11, Theorem 25.77 (p.409). -/
def toApproxLeastFavAssumptions
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : LeastFavorableTaylorHyp P Θ S_θ T_nuis v submodel_path
            estimator score_func_seq score_truth donsker_class score_l_dot θ₀)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    ApproxLeastFavAssumptions P Θ S_θ T_nuis v T dψ
      submodel_path estimator θ₀ where
  h_mem := h_mem
  h_dψ := h_dψ
  hI_pos := h.hI_pos
  submodel_score_at_zero := h.submodel_score_at_zero
  asympLinear_25_77 := h.mle_asympLinear_of_leastFavorable

/-- *Composed scalar headline — vdV thm:25.77 (scalar direction) from book primitives.*

One-shot: from the least-favorable Taylor primitives `LeastFavorableTaylorHyp` plus the
EIF-construction inputs (`h_mem`, `h_dψ`) and `ψ P = θ₀`, the MLE is semiparametrically
efficient at `P`. Chains `toApproxLeastFavAssumptions` into
`mle_semiparametricallyEfficient`.

Reference: vdV §25.11, thm:25.77 (p.409). -/
theorem mle_semiparametricallyEfficient_of_leastFavorable
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : LeastFavorableTaylorHyp P Θ S_θ T_nuis v submodel_path
            estimator score_func_seq score_truth donsker_class score_l_dot θ₀)
    (h_mem : (1 / efficientInformation S_θ T_nuis v)
              • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T, dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T :=
  mle_semiparametricallyEfficient (h.toApproxLeastFavAssumptions h_mem h_dψ) h_ψ

end LeastFavorableTaylorHyp

end AsymptoticStatistics.Asymptotics.Discharge.LeastFavorable
