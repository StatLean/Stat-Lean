import StatLean.AsymptoticStatistics.ParametricFamily.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Asymptotic Statistics — Fisher information.

The bilinear form `(u, v) ↦ P_θ (⟨u, ℓ⟩ ⟨v, ℓ⟩)`. In a finite-dimensional basis
this is the matrix `P_θ ℓ_θ ℓ_θᵀ`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- Fisher information as a bilinear form on the parameter space.

`fisherInformation M μ θ ℓ` sends `(u, v) ↦ ∫ ⟨u, ℓ x⟩ ⟨v, ℓ x⟩ dμ(x) · p_θ(x)`,
or equivalently `P_θ (⟨u, ℓ⟩ ⟨v, ℓ⟩)`.

In a finite-dimensional basis this is exactly the matrix `P_θ ℓ_θ ℓ_θᵀ`. -/
noncomputable def fisherInformation
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ) (ℓ : 𝓧 → Θ) :
    Θ → Θ → ℝ :=
  fun u v => ∫ x, (⟪u, ℓ x⟫ * ⟪v, ℓ x⟫) * M.density θ x ∂μ

end AsymptoticStatistics
