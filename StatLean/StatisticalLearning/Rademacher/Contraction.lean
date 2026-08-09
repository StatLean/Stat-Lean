import StatLean.StatisticalLearning.Rademacher.Defs

/-!
# The contraction lemma for Rademacher complexity

SSBD Lemma 26.9 (Kakade–Tewari form of Talagrand's contraction): applying a
`ρ`-Lipschitz function `φᵢ` to each coordinate does not increase the
Rademacher complexity by more than the factor `ρ`:
`R(φ ∘ A) ≤ ρ R(A)`.

**Reference.** SSBD §26.1, Lemma 26.9. Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** This is **not** the coefficient contraction already in
`ConcentrationInequalities/Symmetrization/Contraction.lean` (HDP Thm 6.6.1,
`E‖∑ aᵢεᵢxᵢ‖ ≤ E‖∑ εᵢxᵢ‖`) — the SSBD lemma contracts a *Lipschitz
composition inside a sup* and is proved coordinate-by-coordinate: condition on
the signs off coordinate `i`, write the `σᵢ`-average of sups as an average of
two sups, pair maximizers `a, a'` and use
`φᵢ(aᵢ) − φᵢ(a'ᵢ) ≤ ρ|aᵢ − a'ᵢ|`, absorbing the absolute value by the
`a ↔ a'` symmetry (SSBD Eqs. (26.12)–(26.13)). The finite-average `signAvg`
makes the conditioning a literal finite-sum split. Stated for a `Finset` class
per the sup policy (sups must be attained). The book's display has a typo
(`φ_m(y_m)` for `φ_m(a_m)`) — statement follows the corrected reading. -/

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ}

/-- **SSBD Lemma 26.9 (contraction)**: for per-coordinate `ρ`-Lipschitz maps
`φᵢ : ℝ → ℝ`, `R({(φ₁(a₁),…,φₙ(aₙ)) : a ∈ A}) ≤ ρ · R(A)` for a finite
nonempty class `A`. -/
theorem radComplexity_contraction (A : Finset (Fin n → ℝ))
    (φ : Fin n → ℝ → ℝ) {ρ : ℝ}
    -- USER-INPUT: nonempty class; SSBD Lemma 26.9 (implicit)
    (hne : A.Nonempty)
    -- USER-INPUT: `ρ ≥ 0` (Lipschitz constant); SSBD Lemma 26.9
    (hρ : 0 ≤ ρ)
    -- USER-INPUT: each `φᵢ` is `ρ`-Lipschitz; SSBD Lemma 26.9
    (hφ : ∀ i a b, |φ i a - φ i b| ≤ ρ * |a - b|) :
    radComplexity
        (↑(A.image fun a => fun i => φ i (a i)) : Set (Fin n → ℝ)) ≤
      ρ * radComplexity (↑A : Set (Fin n → ℝ)) := by
  sorry

end StatLean.StatisticalLearning
