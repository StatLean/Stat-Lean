import StatLean.StatisticalLearning.Stability.Defs
import StatLean.StatisticalLearning.Core.SampleLaw

/-!
# Replace-one exchangeability of the i.i.d. sample law

The measure-theoretic engine of SSBD Theorem 13.2: on
`(sampleLaw D n).prod D`, swapping the `i`-th coordinate with the extra
point — `(s, z') ↦ (s[i ↦ z'], sᵢ)` — is measure-preserving (exchangeability
of i.i.d. draws), together with the two evaluation identities it feeds:
`E[ℓ(A(S), z')] = E_S[L_D(A(S))]` and `n⁻¹∑ᵢ E[ℓ(A(S), sᵢ)] = E_S[L_S(A(S))]`.

**Reference.** SSBD Theorem 13.2 proof ("since `S` and `z'` are drawn i.i.d.,
swap the roles of `zᵢ` and `z'`"). Transcription:
`notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.** The swap reduces to a coordinate permutation of the
`(n+1)`-fold product via `(Fin n → Z) × Z ≃ᵐ (Fin (n+1) → Z)`
(`MeasurableEquiv.piFinSuccAbove`-style, cf. CLAUDE.md §7.14–15) and
permutation invariance of `Measure.pi`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

/-- **Replace-one exchangeability** (SSBD Thm 13.2 proof step): the swap
`(s, z') ↦ (replaceOne s i z', sᵢ)` preserves `(sampleLaw D n).prod D`. -/
theorem measurePreserving_replaceOne_swap (i : Fin n) :
    MeasurePreserving
      (fun p : Sample Z n × Z => (replaceOne p.1 i p.2, p.1 i))
      ((sampleLaw D n).prod D) ((sampleLaw D n).prod D) := by
  sorry

/-- The fresh point evaluates the true risk (SSBD Thm 13.2 proof:
`E_S[L_D(A(S))] = E_{S,z'}[ℓ(A(S), z')]`). -/
theorem integral_loss_fresh_eq_integral_risk (ℓ : H → Z → ℝ)
    (A : Sample Z n → H)
    -- LEAN-ONLY: joint integrability of the fresh-point loss (the book's
    -- expectations presuppose it)
    (hint : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D)) :
    ∫ p : Sample Z n × Z, ℓ (A p.1) p.2 ∂((sampleLaw D n).prod D) =
      ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) := by
  sorry

/-- The index-averaged in-sample loss evaluates the empirical risk
(SSBD Thm 13.2 proof: `E_S[L_S(A(S))] = E_{S,i}[ℓ(A(S), zᵢ)]`). -/
theorem sum_integral_loss_at_coord_eq_integral_empRisk (ℓ : H → Z → ℝ)
    (A : Sample Z n → H)
    -- LEAN-ONLY: integrability of each in-sample loss coordinate
    (hint : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ * ∑ i : Fin n,
        ∫ s, ℓ (A s) (s i) ∂(sampleLaw D n) =
      ∫ s, empRisk ℓ s (A s) ∂(sampleLaw D n) := by
  sorry

end StatLean.StatisticalLearning
