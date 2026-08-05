import StatLean.NonparametricStatistics.RKHS.InnerKernel

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

example (w v : ℂ) : letI := dualRKHS ℂ ℂ; (w : ℂ → ℂ) v = ⟪v, w⟫_ℂ := rfl

example :
    letI := dualRKHS ℂ ℂ
    Set.range (fun w : ℂ => (w : ℂ → ℂ)) ≠ {g : ℂ → ℂ | ∃ T : ℂ →L[ℂ] ℂ, g = T} := by
  letI := dualRKHS ℂ ℂ
  intro h
  have hmem : (fun v : ℂ => conj v) ∈ Set.range (fun w : ℂ => (w : ℂ → ℂ)) := by
    refine ⟨1, ?_⟩
    funext v
    show ⟪v, (1 : ℂ)⟫_ℂ = conj v
    rw [RCLike.inner_apply, one_mul]
  rw [h] at hmem
  obtain ⟨T, hT⟩ := hmem
  have h1 : T 1 = (1 : ℂ) := by
    have := congrFun hT 1
    simpa using this.symm
  have hI : T Complex.I = -Complex.I := by
    have := congrFun hT Complex.I
    simpa using this.symm
  have h2 : T Complex.I = Complex.I := by
    have hs : Complex.I • (1 : ℂ) = Complex.I := by simp
    rw [← hs, map_smul, h1, smul_eq_mul, mul_one]
  rw [hI] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

end StatLean.NonparametricStatistics
