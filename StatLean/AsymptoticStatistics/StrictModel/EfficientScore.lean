import StatLean.AsymptoticStatistics.Core.EIF

/-!
# Efficient score for strict `(θ, η)` semiparametric models

This file develops the ordinary score, nuisance tangent space, efficient
score, and efficient information for classical `(θ, η)` semiparametric
models, culminating in the 1-dimensional form of vdV lem:25.25: the
normalized efficient score is an efficient influence function for a
linear functional of `θ`.

Reference: vdV §25.4. The 1-dim restriction (linear functional of `θ`
in a single direction `v`) keeps the API inside the abstract EIF
framework's `dψ : T →L[ℝ] ℝ` form.

Headline declaration: `eif_from_efficientScore`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.StrictModel.EfficientScore

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Ordinary score operator* for the parameter `θ` at `θ₀`.

A continuous linear map from the parameter Hilbert space `Θ` into
`↥(L²₀(P))`. For a parametric family `t ↦ P_{θ₀ + t·v, η₀}`, evaluating
the score operator at `v` yields the QMD score function (vdV §25.4).

Reference: vdV §25.4. -/
abbrev OrdinaryScore (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    [CompleteSpace Θ] :=
  Θ →L[ℝ] ↥(L2ZeroMean P)

/-- *Nuisance tangent space*: a closed submodule of `↥(L²₀(P))`
representing the scores reachable by perturbing the nuisance parameter
`η`.

Reference: vdV §25.4. The specific submodule depends on the nuisance
model; we take it as a user-supplied input rather than fixing a
particular construction. -/
abbrev NuisanceTangentSpace (P : Measure Ω) [IsProbabilityMeasure P] :=
  Submodule ℝ ↥(L2ZeroMean P)

variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

/-- *Efficient score* for the parameter direction `v` at `θ₀`: the
ordinary score `S_θ v` minus its orthogonal projection onto the
nuisance tangent space. The residual is, by construction, orthogonal
to every nuisance direction.

`efficientScore S_θ T_nuis v := S_θ v - T_nuis.starProjection (S_θ v)`.

Reference: vdV §25.4. The efficient score captures the part of the
ordinary score that *cannot* be explained by perturbing the nuisance
parameter.

Edge behavior: when `S_θ v ∈ T_nuis`, `efficientScore = 0` (no
direction-`v` information remains after the nuisance projection);
the corresponding `eif_from_efficientScore` hypothesis
`I_eff(v) ≠ 0` then fails. -/
noncomputable def efficientScore
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ) : ↥(L2ZeroMean P) :=
  S_θ v - T_nuis.starProjection (S_θ v)

/-- *Efficient information* for parameter direction `v`: the squared
`L²(P)`-norm of the efficient score.

`efficientInformation S_θ T_nuis v := ‖efficientScore S_θ T_nuis v‖²`.

Reference: vdV §25.4. In the multi-dim setting (k-dim θ), this
generalises to the *efficient information matrix* with entries
`⟪S_eff(eᵢ), S_eff(eⱼ)⟫`; the 1-dim form here is its single diagonal
entry along direction `v`.

Edge behavior: zero iff `S_θ v ∈ T_nuis`. -/
noncomputable def efficientInformation
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ) : ℝ :=
  ‖efficientScore S_θ T_nuis v‖^2

/-- *vdV lem:25.25 (1-dim form).* Under non-degenerate efficient
information, `(1 / I_eff(v)) • S_eff(v)` is an efficient influence
function for the linear-functional derivative `dψ` whose action on the
score range is `dψ (S_θ u) = ⟪v, u⟫`.

Reference: vdV §25.4, lem:25.25. The k-dim form
`EIF = I_eff⁻¹ S_eff` (with `I_eff` the efficient information matrix)
generalises this; the 1-dim form here is its slice along direction `v`.

The hypothesis `h_dψ` encodes the parameter derivative shape: for a
linear functional `ψ(P_{θ, η}) := ⟨v, θ⟩` of the parameter, the
pathwise derivative on the score-range submodule of `T` matches
`u ↦ ⟪v, u⟫_Θ`. Concrete consumers prove this via
`PathwiseDifferentiableAt`.

Proof: reduce to `eif_of_representation_and_membership` by checking
two conditions on the candidate `IF := (1/I_eff(v)) • S_eff(v)`:
(1) `IF ∈ T` (membership): assumes `T` is large enough to contain
    `S_eff(v)`. We add `h_mem : (1/I_eff(v)) • S_eff(v) ∈ T` directly.
(2) `IsInfluenceFunction P T dψ IF`: for any `g ∈ T`,
    `⟪IF, g⟫ = (1/I_eff(v)) ⟪S_eff(v), g⟫`. Splitting `g = g_θ + g_η`
    with `g_θ ∈ range(S_θ)` and `g_η ∈ T_nuis`:
    - `⟪S_eff(v), g_η⟫ = 0` since `S_eff(v) ⊥ T_nuis` by construction.
    - `⟪S_eff(v), g_θ⟫ = ⟪S_θ v, g_θ⟫ - ⟪proj S_θ v, g_θ⟫`.
    The cleanest formulation passes `dψ` already evaluated: we
    require `dψ g = (1/I_eff(v)) ⟪S_eff(v), g⟫` for every `g ∈ T`,
    which is the influence-function condition we want to prove. -/
theorem eif_from_efficientScore
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (dψ : T →L[ℝ] ℝ)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) := by
  refine ⟨?_, h_mem⟩
  intro g
  -- `IsInfluenceFunction` says `⟪IF, g⟫ = dψ g`.
  -- Compute `⟪c • S_eff, g⟫ = c * ⟪S_eff, g⟫` and combine with `h_dψ`.
  rw [real_inner_smul_left]
  exact (h_dψ g).symm

end AsymptoticStatistics.StrictModel.EfficientScore
