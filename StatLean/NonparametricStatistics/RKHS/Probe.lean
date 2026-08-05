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
-- V5: starProjection under the same binders
noncomputable def probe5 (H₀ : Submodule 𝕜 H) [CompleteSpace H₀] (v : H) : H :=
  H₀.starProjection v

-- V9: IsClosed instance-binder (canonical Mathlib route)
noncomputable def probe9 (H₀ : Submodule 𝕜 H) [IsClosed (H₀ : Set H)] (x : X) : ↥H₀ :=
  kernelFun H₀ x

-- V10: explicit @-application of the binder instance (default-transparency check)
noncomputable def probe10 (H₀ : Submodule 𝕜 H) [hc : CompleteSpace H₀] (x : X) : ↥H₀ :=
  @kernelFun 𝕜 _ X ↥H₀ _ _ hc _ x

end StatLean.NonparametricStatistics
