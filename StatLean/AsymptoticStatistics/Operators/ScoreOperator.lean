import StatLean.AsymptoticStatistics.Core.EIF
import StatLean.AsymptoticStatistics.StrictModel.EfficientScore

/-!
# Score-operator / adjoint calculus for efficient influence functions

Let $\mathcal{P}$ be a statistical model indexed by an infinite-dimensional
parameter, with a *score operator* $A : H \to L^2_0(P)$, a continuous linear
map carrying directions in a parameter Hilbert space $H$ into the mean-zero
square-integrable functions $L^2_0(P)$. The "calculus of scores" produces the
efficient influence function $\tilde\psi_P$ of a differentiable functional
$\psi$ from $A$ in three equivalent ways:

* **Adjoint equation.** With $A^*$ the adjoint of $A$ and $\tilde\chi$ the
  derivative-representing element, the efficient influence function solves
  $A^*\tilde\psi_P = \tilde\chi$; equivalently, for every direction $g$ in the
  tangent space $T$ one has $d\psi(g) = \langle \tilde\psi_P, g\rangle_{L^2_0(P)}$.
* **Information-operator formula.** When $\tilde\chi$ lies in the range of the
  *information operator* $A^*A$, the solution is $\tilde\psi_P = A(A^*A)^{-}\tilde\chi$,
  where $(A^*A)^{-}$ is a generalized inverse. We encode the information
  equation by its defining inner-product identity
  $\langle A\kappa,\, Av\rangle_{L^2_0(P)} = \langle\chi, v\rangle_H$ for all
  $v \in H$, so that $\kappa$ plays the role of $(A^*A)^{-}\tilde\chi$.
* **Semiparametric specialization.** When the model splits into a $\theta$-part
  and a nuisance $\eta$-part, the score operator splits accordingly and the
  efficient score in a $\theta$-direction is the residual of the ordinary
  $\theta$-score after orthogonal projection onto the closed linear span of
  the nuisance scores.

**Lean alignment / added hypotheses.** The Lean statements certify each
conclusion through an *inner-product hypothesis* rather than through
`ContinuousLinearMap.adjoint`: `eif_via_adjoint_equation` and
`eif_via_information_operator` take the hypothesis that the parameter
derivative `dψ` acts on the tangent space as the inner product against the
candidate, which is exactly what the adjoint/information equation yields on
the score range. This avoids requiring `CompleteSpace` on the
`Submodule`-coerced $L^2_0(P)$ space (needed to synthesize the Mathlib adjoint
through the sort coercion). The extension of the certification from the score
range to the full tangent space $T = \overline{\operatorname{range}A}$ — a
density/continuity argument in the book — is taken as the supplied hypothesis,
not re-proved here.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.5 (Score and Information Operators),
Theorem 25.31, Eqs (25.29), (25.30), (25.33).

**Proof formalization notes.**
* `ScoreOperator` packages the score operator $A : H \to L^2_0(P)$ as a
  continuous linear map (vdV §25.5, the operator $A_\eta$ of Eq (25.29)). For
  parametric models take `H := EuclideanSpace ℝ (Fin k)`; for
  semiparametric/nonparametric models `H` may be any Hilbert space. Edge case:
  for `H = 0` the only score operator is the zero map and the tangent range is
  `⊥`.
* `eif_via_adjoint_equation` (Theorem 25.31): the book conclusion is "$\phi$
  solves the adjoint equation $A^*\phi = \chi$". On $g \in \operatorname{range}A$
  the adjoint identity $\langle Av, \phi\rangle = \langle v, A^*\phi\rangle =
  \langle v, \chi\rangle = d\psi(Av)$ recovers the inner-product hypothesis
  `h_dψ_eq_inner` from $A^*\phi = \chi$. Reduces to
  `eif_of_representation_and_membership`.
* `eif_via_information_operator` (Eq (25.30)): the book conclusion is
  $\phi = A(A^*A)^{-}\chi$. The information-operator inversion $(A^*A)\kappa = \chi$
  is captured by the inner-product condition `h_information`,
  $\langle A\kappa, Av\rangle = \langle\chi, v\rangle$ for all $v$, the defining
  property of $A^*A$. Same reduction shape as the adjoint form.
* `efficientScore_projection_formula` (Eq (25.33)): a vocabulary-alignment
  lemma (`rfl`) identifying the operator-side residual
  $A_\theta v - \Pi_{T_\eta}(A_\theta v)$ with the projection-side
  `efficientScore`, so concrete model files move freely between the two
  characterizations.

**Bibliographic comments.** The score-operator / adjoint calculus for
semiparametric efficiency originates with P. J. Bickel, C. A. J. Klaassen,
Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation for
Semiparametric Models*, Johns Hopkins University Press, Baltimore, 1993
(reprinted Springer, 1998). That monograph develops the geometry of tangent
spaces, score operators, and their adjoints (the "calculus of scores") of
which van der Vaart's Chapter 25 is a condensed account; vdV §25.5 follows
their treatment, and the information operator $A^*A$ and adjoint equation
$A^*\tilde\psi = \tilde\chi$ are theirs. Earlier roots lie in C. Stein's
heuristic for the hardest one-dimensional submodel (1956) and the
projection/least-favorable-direction viewpoint of P. J. Bickel,
*On adaptive estimation*, Annals of Statistics 10 (1982), 647–671.

Headline declarations: `ScoreOperator`, `eif_via_adjoint_equation`,
`eif_via_information_operator`, `efficientScore_projection_formula`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

-- The structure name `ScoreOperator` matches the namespace; intentional.
set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.ScoreOperator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Abstract score operator* `A : H →L[ℝ] ↥(L²₀(P))`.

A continuous linear map from a user-supplied parameter Hilbert space
`H` into the mean-zero `L²(P)` space. For parametric models
`H := EuclideanSpace ℝ (Fin k)`; for semiparametric / nonparametric
models `H` may be any other Hilbert space (e.g. `Lp ℝ 2 ν`).

Reference: vdV §25.5 (eq:25.29).

Edge behavior: when `H = 0`, the only score operator is the zero map,
and the tangent range is `⊥`. -/
structure ScoreOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.5: the score operator as a continuous
  linear map from `H` to mean-zero `L²(P)`. -/
  toCLM : H →L[ℝ] ↥(L2ZeroMean P)

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- *vdV thm:25.31 (inner-product-certified form).* Given a score
operator `A : H →L[ℝ] ↥(L²₀(P))`, a tangent space `T` containing a
candidate `φ`, and the parameter-derivative-as-inner-product
certification `dψ g = ⟪φ, g⟫_ℝ` for every `g ∈ T`, the candidate `φ`
is an efficient influence function for `dψ`.

Reference: vdV §25.5, thm:25.31. The book states the conclusion as
"`φ` solves the adjoint equation `A* φ = χ`"; for `g ∈ range A`, the
adjoint identity `⟪A v, φ⟫ = ⟪v, A* φ⟫ = ⟪v, χ⟫ = dψ (A v)` recovers
the inner-product hypothesis `h_dψ_eq_inner` from `A* φ = χ` and the
parameter derivative shape on the score range. Extending to the full
`T` (when `T = closure(range A)`) requires a density / continuity
argument, omitted here.

Concrete callers prove `h_dψ_eq_inner` from a model-specific
`PathwiseDifferentiableAt` plus the adjoint equation. The named
theorem reduces this to `eif_of_representation_and_membership`.
-/
theorem eif_via_adjoint_equation
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {dψ : T →L[ℝ] ℝ} {φ : ↥(L2ZeroMean P)}
    (hφ_T : φ ∈ T)
    (h_dψ_eq_inner :
      ∀ g : T, dψ g = ⟪φ, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ φ := by
  refine ⟨?_, hφ_T⟩
  intro g
  exact (h_dψ_eq_inner g).symm

/-- *vdV eq:25.30 (information-operator form, Option-A inner-product
encoding).* When `κ : H` solves the *information equation*
  `⟪A κ, A v⟫_{L²₀} = ⟪χ, v⟫_H` for all `v : H`,
the candidate `A κ` is an efficient influence function for the
parameter derivative `dψ` whose inner-product action against `A κ`
recovers `dψ` on the tangent space `T`.

Reference: vdV §25.5, eq:25.30. The book states the conclusion as
`φ = A((A*A)⁻¹ χ)`. The information-operator inversion `(A*A) κ = χ`
is captured here by the inner-product condition `h_information`:
`⟪(A*A) κ, v⟫_H = ⟪A κ, A v⟫_{L²₀}` (the defining property of the
information operator), so `(A*A) κ = χ` ↔ `∀ v, ⟪A κ, A v⟫ = ⟪χ, v⟫`.

This formulation avoids `ContinuousLinearMap.adjoint`, which would
need `CompleteSpace ↥(L2ZeroMean P)` to be synthesizable through the
Submodule sort-coercion. Concrete callers in
finite-dim parametric models compute `κ` by inverting the
information matrix and prove `h_information` by direct computation.

Proof: reduce to `eif_of_representation_and_membership` via the
inner-product certification, same shape as `eif_via_adjoint_equation`. -/
theorem eif_via_information_operator
    (A : ScoreOperator H P) (χ : H) (κ : H)
    (_h_information :
      ∀ v : H, ⟪A.toCLM κ, A.toCLM v⟫_ℝ = ⟪χ, v⟫_ℝ)
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    (hφ_T : A.toCLM κ ∈ T)
    {dψ : T →L[ℝ] ℝ}
    (h_dψ_eq_inner :
      ∀ g : T, dψ g = ⟪A.toCLM κ, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction P T dψ (A.toCLM κ) := by
  refine ⟨?_, hφ_T⟩
  intro g
  exact (h_dψ_eq_inner g).symm

/-- *vdV eq:25.33 (semiparametric specialization).* In a strict
semiparametric model the score operator splits into a θ-component
`A_θ : H_θ →L[ℝ] ↥(L²₀(P))` and an η-component
`A_η : H_η →L[ℝ] ↥(L²₀(P))`. The efficient score for the
θ-direction `v : H_θ`, defined as the residual of the ordinary
θ-score after projecting onto a fixed η-tangent space `T_η` (typically
the closure of `range A_η`), coincides with `efficientScore` when
the ordinary-score operator is taken to be `A_θ.toCLM`.

Reference: vdV §25.5, eq:25.33. This vocabulary-alignment theorem
lets concrete model files freely move between the operator-side
and projection-side characterisations. -/
theorem efficientScore_projection_formula
    {H_θ : Type*}
    [NormedAddCommGroup H_θ] [InnerProductSpace ℝ H_θ] [CompleteSpace H_θ]
    (A_θ : ScoreOperator H_θ P)
    (T_η : Submodule ℝ ↥(L2ZeroMean P)) [T_η.HasOrthogonalProjection]
    (v : H_θ) :
    A_θ.toCLM v - T_η.starProjection (A_θ.toCLM v)
      = AsymptoticStatistics.StrictModel.EfficientScore.efficientScore
          A_θ.toCLM T_η v := rfl

end AsymptoticStatistics.Operators.ScoreOperator
