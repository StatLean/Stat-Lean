import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.HighDimensionalStatistics.LinearModel.Defs

/-!
# Lasso — definitions

Book setup (Lu, *Big Data Analysis* §8): the Lasso estimator
`β̂ ∈ argmin_β  (1/2n)‖Y − X β‖² + λ ‖β‖₁`, the restricted cone
`C_α(S) = {Δ : ‖Δ_{Sᶜ}‖₁ ≤ α ‖Δ_S‖₁}`, and the **restricted eigenvalue
condition** `RE(κ, α)`:
`(1/n)‖X Δ‖² ≥ κ ‖Δ‖²` for all `Δ ∈ C_α(S)` (`def:re`, used by `thm:re`).

Reuses the ℓ¹ norm and support restriction from `ForMathlib/VecNorms.lean`
and the design map from `LinearModel/Defs.lean`. Concept-layer, theorem-agnostic;
consumed by `Lasso/DeterministicRate.lean` (`thm:re`) and
`Lasso/RandomNoise.lean` (`cor:lasso-rate`).
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- The **restricted cone** `C_α(S) = {Δ : ‖Δ_{Sᶜ}‖₁ ≤ α ‖Δ_S‖₁}` (Lu §8):
deviations whose mass off the support `S` is at most `α` times the mass on `S`.
`Δ_S` is `restrict S Δ` and `Δ_{Sᶜ}` is `restrict Sᶜ Δ` from `VecNorms`. -/
def reCone (S : Finset (Fin d)) (α : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {Δ | l1Norm (restrict Sᶜ Δ) ≤ α * l1Norm (restrict S Δ)}

/-- **Restricted eigenvalue condition** `RE(κ, α)` for design `X` and support `S`
(Lu §8, `def:re`): the loss is `κ`-curved along the cone `C_α(S)`, i.e.
`(1/n)‖X Δ‖² ≥ κ ‖Δ‖²` for every `Δ ∈ C_α(S)`. -/
def RestrictedEigenvalue (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (κ α : ℝ) : Prop :=
  ∀ Δ ∈ reCone S α, (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 ≥ κ * ‖Δ‖ ^ 2

/-- The **Lasso objective** `L_n(β) = (1/2n)‖Y − X β‖² + λ‖β‖₁` (Lu §8). -/
noncomputable def lassoObjective (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (2 * (n : ℝ))) * ‖Y - designMap X β‖ ^ 2 + lam * l1Norm β

/-- **Lasso estimator predicate** (Lu §8): `β̂` minimises the Lasso objective at
tuning parameter `λ` over all `β` (zero-order/minimiser characterisation). -/
def IsLassoEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (βhat : EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ β, lassoObjective X Y lam βhat ≤ lassoObjective X Y lam β

end StatLean.HighDimensionalStatistics
