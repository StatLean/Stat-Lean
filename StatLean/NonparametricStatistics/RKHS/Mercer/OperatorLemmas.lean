import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Norm-attaining vectors of positive operators are eigenvectors

Two Hilbert-space lemmas feeding the constructive proof of Mercer's theorem:

* if `‖A h‖ = ‖A‖` for a unit vector `h`, then `A` maps the orthogonal complement of `h`
  into the orthogonal complement of `A h` (a first-derivative argument on
  `t ↦ ‖A(cos t · h + sin t · k)‖²`);
* consequently, a unit vector at which a *positive* operator attains its norm is an
  eigenvector with eigenvalue `‖P‖`.

**Bibliographic comments.** Classical operator theory; see F. Riesz and B. Sz.-Nagy,
*Functional Analysis* (1955), §93 (norm-attaining vectors of symmetric operators).
-/

open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- If a bounded operator attains its norm at the unit vector `h`, then vectors
orthogonal to `h` are mapped to vectors orthogonal to `A h`. -/
theorem inner_map_eq_zero_of_norm_attaining (A : E →L[𝕜] E) {h : E}
    -- USER-INPUT: unit vector attaining the operator norm
    (hh : ‖h‖ = 1) (hA : ‖A h‖ = ‖A‖)
    {k : E} (hk : ⟪h, k⟫_𝕜 = 0) :
    ⟪A h, A k⟫_𝕜 = 0 := by
  sorry

/-- **Norm-attaining vectors of positive operators are eigenvectors**: if a positive
operator `P` attains its norm at the unit vector `h`, then `P h = ‖P‖ • h`. -/
theorem isEigenvector_of_norm_attaining {P : E →L[𝕜] E}
    -- USER-INPUT: positivity of the operator
    (hP : P.IsPositive) {h : E}
    -- USER-INPUT: unit vector attaining the operator norm
    (hh : ‖h‖ = 1) (hn : ‖P h‖ = ‖P‖) :
    P h = ((‖P‖ : ℝ) : 𝕜) • h := by
  sorry

end StatLean.NonparametricStatistics
