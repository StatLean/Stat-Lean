import StatLean.NonparametricStatistics.RKHS.Basic

/-! Temporary elaboration probe for the stub gate — DELETED before fan-out. -/

open RKHS

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

noncomputable instance probeInst (H₀ : Submodule 𝕜 H) : RKHS 𝕜 H₀ X 𝕜 where
  coeCLM := (coeCLM 𝕜).comp H₀.subtypeL
  coeCLM_injective := by sorry

-- V0a: does the binder satisfy the plain goal?
example (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] : CompleteSpace H₀ := inferInstance
-- V0b: with explicit coeSort in the goal
example (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] : CompleteSpace (↥H₀) := inferInstance
-- V1: the failing shape from Subspace.lean
noncomputable def probe1 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x : X) : H :=
  (kernelFun H₀ x : H)
-- V2: explicit coeSort at the use site
noncomputable def probe2 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x : X) : H :=
  (kernelFun (↥H₀) x : H)
-- V3: no ascription, subtype-valued
noncomputable def probe3 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x : X) : ↥H₀ :=
  kernelFun H₀ x
-- V4: Mathlib's kerFun directly
noncomputable def probe4 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (x : X) : ↥H₀ :=
  RKHS.kerFun (↥H₀) x 1
-- V5: starProjection under the same binders
noncomputable def probe5 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (v : H) : H :=
  H₀.starProjection v

end StatLean.NonparametricStatistics
