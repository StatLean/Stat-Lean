import StatLean.AsymptoticStatistics.StrictModel.EfficientScore
import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
import StatLean.AsymptoticStatistics.Core.QMDPath

/-!
# MLE via approximate least-favorable submodel

In a semiparametric model with a scalar parameter of interest, one constructs a
one-parameter submodel $s \mapsto p_{s,\hat\eta_s}$ passing through the truth whose score
at $s = 0$ equals the efficient score $\tilde\ell = $ `efficientScore S_θ T_nuis v` of the
full model — the *least-favorable* (Stein) submodel. The maximum-likelihood estimator
$\hat\theta_n = \arg\max_s \mathbb{P}_n \log p_{s,\hat\eta_s}$ along this submodel is then
asymptotically linear,
$$\sqrt{n}\,(\hat\theta_n - \theta_0) = \frac{1}{\sqrt n}\sum_{i=1}^n
  \frac{1}{\tilde I}\,\tilde\ell(X_i) + o_{P}(1),$$
with influence function $(1/\tilde I)\,\tilde\ell$, where $\tilde I$ is the efficient
information. Consequently $\hat\theta_n$ is asymptotically efficient for the functional
$\psi$ relative to the target tangent space $T$.

The submodel is *approximate* in van der Vaart's sense: at $s = 0$ its score matches the
efficient score of the full semiparametric model exactly; for $s \neq 0$ the submodel need
only be differentiable in quadratic mean with score sufficiently close to a
smooth-in-$s$ family, with the slack absorbed by the Donsker / no-bias condition
(Eq (25.76)).

Scope deviation from the book: here the parameter of interest is scalar and the score
direction is one-dimensional ($\theta \in \mathbb{R}$ via the Hilbert direction
`v : Θ`); van der Vaart's Theorem 25.77 allows an infinite-dimensional nuisance with a
least-favorable direction in a Banach space.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 25
(Semiparametric Models), §25.11 (Approximately Least-Favorable Submodels), Theorem 25.77; Eq (25.75)
(least-favorable score identity at $s = 0$), Eq (25.76) (Donsker / no-bias condition along
the least-favorable submodel).

**Proof formalization notes.** Headline declarations: `ApproxLeastFavAssumptions`,
`mle_semiparametricallyEfficient`. The proof of `mle_semiparametricallyEfficient` follows
the template shared with `ZEstimator` and `OneStep`:
* **Step A** — produce the efficient influence function via `eif_from_efficientScore`.
* **Step B** — unwrap the asymptotic-linearity bundle `asympLinear_25_77` modulo
  $\psi(P) = \theta_0$.
* **Step C** — combine via `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The least-favorable score identity (Eq (25.75) at $s = 0$) is bundled as
`submodel_score_at_zero` and is not used directly in this proof: it shapes
`asympLinear_25_77` for downstream consumers. The "approximate" qualifier means only the
origin score must match exactly; $s \neq 0$ drifts are absorbed into the empirical-process
bundle.

**Bibliographic comments.** The least-favorable-submodel construction for the MLE of a
scalar parameter in a semiparametric model originates with T. A. Severini and W. H. Wong,
"Profile Likelihood and Conditionally Parametric Models," *The Annals of Statistics* 20(4)
(1992), 1768–1802. They estimate the scalar parameter by first forming a one-dimensional
subproblem that is *least favorable in the sense of Stein* and then maximizing the induced
"generalized profile likelihood"; van der Vaart's §25.11 is a textbook synthesis of this
program. (The Stein least-favorable terminology traces to C. Stein, "Efficient
nonparametric testing and estimation," *Proc. Third Berkeley Symp. Math. Statist. Probab.*
1 (1956), 187–195.)
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.LeastFavorable

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Bundled assumptions for vdV thm:25.77 (MLE semiparametric efficiency via approximate
least-favorable submodel).

Structure parameters: model identity (`S_θ`, `T_nuis`, `v`, `T`, `dψ`) + the parametric
submodel `submodel_path : Θ → QMDPath P` + MLE sequence `estimator` + centering `θ₀`.
Structure body: EIF hypotheses + the LFM score identity + the empirical-process
consequence (`asympLinear_25_77`).

Reference: vdV §25.11, eqs:25.75, 25.76, thm:25.77.

Edge behavior:
* `efficientInformation = 0` ⇒ `hI_pos` fails ⇒ uninhabited.
* `submodel_path` always lives in `QMDPath P`, so QMD regularity is built into the type;
  no separate field needed.
* The LFM identity at the *origin* of the parameter space (i.e. at `submodel_path 0`) is
  exact; for `s ≠ 0` the submodel can drift, with the drift absorbed in
  `asympLinear_25_77`. This matches vdV's "approximate" qualifier on §25.11. -/
structure ApproxLeastFavAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (submodel_path : Θ → QMDPath P)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF `(1 / Ĩ) • ℓ̃` lies in the target tangent
  space `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): `dψ` acts on `T` as `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): efficient information is positive at `v`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.11 (eq:25.75 at `s = 0`): the submodel's score at the origin matches the
  efficient score of the full semiparametric model. This is the *least-favorable* property
  in vdV §25.11: among parametric paths inside the model, the chosen `submodel_path` is one
  whose score is `ℓ̃`.

  vdV's "approximate" qualifier permits `s ≠ 0` perturbations: those drifts are absorbed
  in the empirical-process bundle below; the origin score must match exactly. -/
  submodel_score_at_zero :
    (submodel_path 0).score = efficientScore S_θ T_nuis v
  /-- vdV §25.11 (eq:25.76 + MLE first-order condition along the LFM):

  the MLE `estimator` is asymptotically linear at `P` with influence function `(1 / Ĩ) • ℓ̃`
  and centering `θ₀`. Concrete model files prove this from the MLE's first-order condition
  along `submodel_path` together with eq:25.76 Donsker / no-bias machinery applied to the
  LFM derivative. -/
  asympLinear_25_77 :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀

/-- vdV §25.11 thm:25.77 — MLE semiparametric efficiency via approximate least-favorable
submodel.

If the bundled `ApproxLeastFavAssumptions` holds for the model triple `(S_θ, T_nuis, v)`,
target tangent space `T`, derivative `dψ`, parametric submodel `submodel_path`, MLE
sequence `estimator`, and centering `θ₀ = ψ P`, then `estimator` is semiparametrically
efficient at `P` for the parameter functional `ψ` relative to `T`.

Reference: vdV §25.11, thm:25.77.

Proof template (shared with `ZEstimator`, `OneStep`):
* **Step A** — produce the EIF via `eif_from_efficientScore`.
* **Step B** — unwrap `asympLinear_25_77` modulo `ψ P = θ₀`.
* **Step C** — combine via `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The LFM score identity (eq:25.75 at `s = 0`) is bundled as `submodel_score_at_zero` and is
not used directly in this proof: it shapes `asympLinear_25_77` for downstream consumers. -/
theorem mle_semiparametricallyEfficient
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {submodel_path : Θ → QMDPath P}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : ApproxLeastFavAssumptions P Θ S_θ T_nuis v T dψ
            submodel_path estimator θ₀)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) :=
    eif_from_efficientScore S_θ T_nuis v T h.h_mem dψ h.h_dψ
  have hAL : AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) (ψ P) := by
    rw [h_ψ]
    exact h.asympLinear_25_77
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

end AsymptoticStatistics.Asymptotics.LeastFavorable
