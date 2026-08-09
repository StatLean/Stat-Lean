import StatLean.StatisticalLearning.Rademacher.Defs

/-!
# Structural properties of Rademacher complexity, and Massart's lemma

Scaling/translation invariance (SSBD Lemma 26.6), the sub-Gaussian sign-MGF
bound `(e^a + e^{−a})/2 ≤ e^{a²/2}` (SSBD Lemma A.6), and **Massart's lemma**
(SSBD Lemma 26.8): for a finite `A = {a₁,…,a_N} ⊆ ℝⁿ` with mean `ā`,
`R(A) ≤ max_{a∈A} ‖a − ā‖₂ · √(2 log N)/n`, plus the center-form consumer
shape `R(A) ≤ r √(2 log |A|)/n` when every `a ∈ A` lies in the `ℓ₂`-ball of
radius `r` around a fixed center.

**Reference.** SSBD §26.1 (Lemmas 26.6, 26.8), Appendix A (Lemma A.6).
Transcriptions: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Everything here is finite real analysis — the sign
average is a finite sum, so Massart's proof is the book's verbatim:
log-sum-exp + Jensen + Lemma A.6 termwise + the optimization
`λ⋆ = √(2 log N / max ‖a‖²)`, with the WLOG-centering step made explicit via
`radComplexity_translate`. The Euclidean norm on `Fin n → ℝ` is spelled
`√(∑ᵢ (aᵢ − cᵢ)²)` (the ambient `pi` norm is the sup norm — deliberately
avoided). Classes are `Finset (Fin n → ℝ)` so `N = A.card`.
-/

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ}

/-- **Translation invariance** (SSBD Lemma 26.6, translation part):
`R(A + a₀) = R(A)` — the shift is killed by `E σᵢ = 0`. -/
theorem radComplexity_translate (A : Set (Fin n → ℝ)) (a₀ : Fin n → ℝ)
    -- LEAN-ONLY: nonempty class (both sides junk-`0` otherwise)
    (hne : A.Nonempty)
    -- LEAN-ONLY: bounded sups on the untranslated class (junk-safety; a
    -- `Finset` image satisfies it)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => a + a₀) '' A) = radComplexity A := by
  sorry

/-- **Scaling** (SSBD Lemma 26.6, scaling part): `R(c • A) ≤ |c| R(A)`. -/
theorem radComplexity_smul_le (A : Set (Fin n → ℝ)) (c : ℝ)
    -- LEAN-ONLY: nonempty class (both sides junk-`0` otherwise)
    (hne : A.Nonempty)
    -- LEAN-ONLY: bounded sups (junk-safety)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => c • a) '' A) ≤ |c| * radComplexity A := by
  sorry

/-- **Negation invariance** (SSBD §26.1, the `σ ≍ −σ` symmetry):
`R(−A) = R(A)` — negating every vector is absorbed by the sign average. Used
for the two-sided (±family) union step of SSBD §28.1. -/
theorem radComplexity_neg (A : Set (Fin n → ℝ)) :
    radComplexity ((fun a => -a) '' A) = radComplexity A := by
  sorry

/-- **SSBD Lemma A.6**: `(e^a + e^{−a})/2 ≤ e^{a²/2}` — the MGF of a
Rademacher sign is sub-Gaussian with variance proxy `1`. -/
theorem add_exp_neg_div_two_le_exp_sq (a : ℝ) :
    (Real.exp a + Real.exp (-a)) / 2 ≤ Real.exp (a ^ 2 / 2) := by
  sorry

/-- **Massart's lemma, center form** (SSBD Lemma 26.8 as consumed by §28.1):
if every `a ∈ A` lies in the Euclidean ball of radius `r` around a fixed
center `c`, then `R(A) ≤ r √(2 log |A|)/n`. -/
theorem radComplexity_le_of_dist_center_le (A : Finset (Fin n → ℝ))
    (c : Fin n → ℝ) {r : ℝ}
    -- USER-INPUT: nonempty finite class; SSBD Lemma 26.8
    (hne : A.Nonempty)
    -- USER-INPUT: Euclidean radius bound around the center; SSBD Lemma 26.8
    -- (with `c = ā` this is `max_{a} ‖a − ā‖ ≤ r`)
    (hr : ∀ a ∈ A, Real.sqrt (∑ i, (a i - c i) ^ 2) ≤ r) :
    radComplexity (↑A : Set (Fin n → ℝ)) ≤
      r * Real.sqrt (2 * Real.log A.card) / n := by
  sorry

/-- **Massart's lemma** (SSBD Lemma 26.8, book form): for finite
`A = {a₁,…,a_N}` with mean `ā = N⁻¹ ∑ a`,
`R(A) ≤ max_{a∈A} ‖a − ā‖₂ · √(2 log N)/n`. -/
theorem massart (A : Finset (Fin n → ℝ))
    -- USER-INPUT: nonempty finite class; SSBD Lemma 26.8
    (hne : A.Nonempty) :
    radComplexity (↑A : Set (Fin n → ℝ)) ≤
      (A.sup' hne fun a =>
          Real.sqrt (∑ i, (a i - (A.card : ℝ)⁻¹ * ∑ b ∈ A, b i) ^ 2)) *
        Real.sqrt (2 * Real.log A.card) / n := by
  sorry

end StatLean.StatisticalLearning
