import StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition

/-!
# McDiarmid's bounded-differences inequality — Lu-BDA §3.1 (`McDiarmid`)

We formalize Lu, *Big Data Analysis* §3.1 **McDiarmid's inequality**: for `n` independent
random variables `X = (X₀,…,Xₙ₋₁)` and a function `f` satisfying the bounded-differences
condition with constants `c : Fin n → ℝ` (`|f x − f (update x k y)| ≤ cₖ`), the centered
evaluation `f(X) − E[f(X)]` has the Gaussian-style upper tail

  `μ {ω | t < f(X ω) − E[f(X)]} ≤ exp(−2 t² / (∑ₖ cₖ²))`   for `0 ≤ t`,

and the two-sided form

  `μ {ω | t < |f(X ω) − E[f(X)]|} ≤ 2 · exp(−2 t² / (∑ₖ cₖ²))`.

The proof is a pure Chernoff bound on the sub-Gaussian MGF already established in
`McDiarmid/DoobDecomposition.lean`:
`mgf_sub_expectation_le` gives `HasSubgaussianMGF (f(X) − E[f(X)]) σ² μ` with proxy
`σ² = ∑ₖ (‖cₖ‖₊/2)² = (∑ₖ cₖ²)/4`. Mathlib's
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` then yields the right-tail bound
`μ.real {t ≤ ·} ≤ exp(−t²/(2σ²))`, and `−t²/(2σ²) = −t²/(2·(∑cₖ²)/4) = −2t²/(∑cₖ²)`.
The `μ.real → ENNReal` bridge mirrors `SubGaussian/TailBounds.lean`.

Deviation from the book: Lu states the bound for `t > 0`; we use the weaker `0 ≤ t` to
match Mathlib's brick, giving a strictly stronger statement (the `t = 0` case is trivial).
The strict inequality `<` on the event is faithful to the book; the brick gives `≤`, and
the slack is absorbed via the inclusion `{t < y} ⊆ {t ≤ y}`.

This file rests transitively on `DoobDecomposition`'s single open named debt
`increment_bounded_of_bounded_differences`; it introduces no new `sorry`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

section McDiarmid

variable {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {β : Fin n → Type*} [(i : Fin n) → MeasurableSpace (β i)]

/-- The Doob sub-Gaussian proxy `∑ₖ (‖cₖ‖₊/2)²` (an `ℝ≥0`) coerces to `(∑ₖ cₖ²)/4` as a real,
using `‖cₖ‖ = |cₖ| = cₖ` for the nonnegative constants `cₖ`. -/
private lemma coe_doob_proxy (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ((∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (∑ k : Fin n, c k ^ 2) / 4 := by
  rw [NNReal.coe_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [Real.norm_eq_abs, abs_of_nonneg (hc k)]
  ring

/-- The McDiarmid right-tail exponent rewrite: with proxy `σ² = ∑ₖ (‖cₖ‖₊/2)²`,
`−t²/(2σ²) = −2t²/(∑ₖ cₖ²)`. Holds unconditionally — both sides degenerate to `0`
when `∑ₖ cₖ² = 0` (Lean's `x/0 = 0`). -/
private lemma doob_exp_eq (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (t : ℝ) :
    Real.exp (-t ^ 2 / (2 * ((∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))
      = Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)) := by
  congr 1
  rw [coe_doob_proxy c hc]
  ring

/-- **McDiarmid's bounded-differences inequality** (Lu-BDA §3.1, `McDiarmid`), one-sided
upper tail.

For `n` independent random variables `X = (X₀,…,Xₙ₋₁)` and `f` satisfying the
bounded-differences condition with constants `c : Fin n → ℝ`, the centered evaluation has
the upper tail bound, for `0 ≤ t`,

  `μ {ω | t < f(X ω) − ∫ f(X) dμ} ≤ exp(−2 t² / (∑ₖ cₖ²))`.

Proof: Chernoff on the sub-Gaussian MGF `mgf_sub_expectation_le` (proxy `(∑cₖ²)/4`) via
`HasSubgaussianMGF.measure_ge_le`, then `−t²/(2σ²) = −2t²/(∑cₖ²)`. -/
theorem McDiarmid
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §3.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §3.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §3.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §3.1.
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
  have hsg : HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ :=
    mgf_sub_expectation_le X hX f hf c hc hbd hX_indep hf_int
  -- Mathlib Chernoff brick, then rewrite the exponent to the book form.
  have hbrick := hsg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrick
  -- {t < ·} ⊆ {t ≤ ·}; bridge μ.real → ENNReal exactly as in TailBounds.
  have hsub : {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ⊆ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ} := by
    intro ω hω
    have hω' : t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ := hω
    exact hω'.le
  calc μ {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hbrick

/-- **McDiarmid's bounded-differences inequality** (Lu-BDA §3.1, `McDiarmid`), two-sided
form.

For `0 ≤ t`,

  `μ {ω | t < |f(X ω) − ∫ f(X) dμ|} ≤ 2 · exp(−2 t² / (∑ₖ cₖ²))`.

Proof: `t < |Y|` splits as `t < Y ∨ t < −Y` (`lt_abs`); apply the one-sided Chernoff bound
to `Y := f(X) − E[f(X)]` (right tail) and to `−Y` via `HasSubgaussianMGF.neg` (left tail),
then combine with `measure_union_le`. -/
theorem McDiarmid_abs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §3.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §3.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §3.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §3.1.
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
  have hsg : HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ :=
    mgf_sub_expectation_le X hX f hf c hc hbd hX_indep hf_int
  -- Right tail.
  have hbrickR := hsg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrickR
  -- Left tail via negation.
  have hbrickL := hsg.neg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrickL
  simp only [Pi.neg_apply] at hbrickL
  -- Bridge each tail μ.real → ENNReal.
  have hR : μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickR
  have hL : μ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickL
  have hexp_nn : 0 ≤ Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)) := (Real.exp_pos _).le
  have hsub : {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ⊆ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
        ∪ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)} := by
    intro ω hω
    have hω' : t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ| := hω
    rcases lt_abs.mp hω' with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc μ {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ≤ μ ({ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
            ∪ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
          + μ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)))
          + ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := add_le_add hR hL
    _ = ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
        rw [← ENNReal.ofReal_add hexp_nn hexp_nn]
        ring_nf

end McDiarmid

end StatLean.ConcentrationInequalities
