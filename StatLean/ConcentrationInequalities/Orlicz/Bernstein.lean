import StatLean.ConcentrationInequalities.Orlicz.SubExponentialMGF

/-!
# Bernstein's inequality for sub-exponential sums (ψ₁-norm form)

For independent, mean-zero, sub-exponential $X_1, \dots, X_n$,
$$ \mathbb{P}\Bigl\{ \Bigl|\sum_{i=1}^{n} X_i\Bigr| \ge t \Bigr\}
   \;\le\; 2 \exp\Bigl[ -c \cdot \min\Bigl(
     \frac{t^2}{\sum_i \|X_i\|_{\psi_1}^2},
     \frac{t}{\max_i \|X_i\|_{\psi_1}} \Bigr) \Bigr], \qquad t \ge 0. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.9, Theorem 2.9.1 (and Corollary 2.9.2 for the
weighted form).

**Proof formalization notes.** Constants are explicit (formula + frozen
numeral): the exponent is $\min\bigl(t^2/(16\sum K_i^2),\, t/(4\max K_i)\bigr)$
— i.e. the book's absolute constant $c$ is realized as $c = 1/16$ in the
quadratic regime and $1/4$ in the linear regime, coming from the restricted
MGF bound `mgf_le_of_lintegral_exp_abs_le_two` ($E e^{\lambda X}
\le e^{4\lambda^2 K^2}$ for $|\lambda| \le 1/(2K)$, HDP Prop 2.8.1(iv) with
$K_4 = 2K$) via Chernoff and the optimization
$\lambda^\* = \min\bigl(t/(8\sum K_i^2),\, 1/(2\max K_i)\bigr)$. One-sided
engine first (`measure_sum_ge_le_of_subExponentialNorm_le`), two-sided by the
`X ↦ −X` symmetry of the ψ₁ norm and a union bound. `hK : ∀ i, 0 < K i` is a
mild strengthening over the book (a zero bound forces the degenerate
`X_i = 0` a.e., removable by reindexing); documented, not laundered. The
work item's single named-sorry fallback is the **bonus** weighted Corollary
2.9.2 (`bernstein_subexponential_weighted`); Theorem 2.9.1 itself must close.

**Bibliographic comments.** Bernstein-type inequalities for unbounded
variables under exponential-moment conditions go back to S. N. Bernstein
(1920s–1930s); the ψ₁-norm formulation is the modern synthesis of
Vershynin (HDP §2.9, and the Notes to Chapter 2). The moment-condition
variant is formalized separately in `Bernstein/Bernstein.lean` (Lu-BDA); the
two are deliberately distinct results.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- One-sided ψ₁-Bernstein engine (HDP Theorem 2.9.1, upper tail):
Chernoff + `iIndepFun.mgf_sum` + the per-`i` restricted MGF bound of
Prop 2.8.1(iv), optimized at
`λ* = min (t / (8 ∑ Kᵢ²)) (1 / (2 max Kᵢ))`. Exponent frozen:
`min (t²/(16 ∑ Kᵢ²)) (t/(4 max Kᵢ))`. -/
theorem measure_sum_ge_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; Chernoff/MGF machinery requires it
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: nonempty sum so max Kᵢ is well-defined; n = 0 is vacuous
    (hn : 0 < n)
    -- LEAN-ONLY: measurability of each summand; MGF regularity
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the Xᵢ; HDP Thm 2.9.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero summands; HDP Thm 2.9.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (zero forces Xᵢ = 0 a.e.; removable
    -- by reindexing — documented mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: sub-exponential norm bounds ‖Xᵢ‖_{ψ₁} ≤ Kᵢ; HDP Thm 2.9.1
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K i)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Thm 2.9.1
    (ht : 0 ≤ t) :
    μ {ω | t ≤ ∑ i, X i ω} ≤
      ENNReal.ofReal (Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
        (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ))))))  := by sorry

/-- **Bernstein's inequality, ψ₁-norm form** (HDP §2.9, Theorem 2.9.1; the
book's absolute constant realized as `c = 1/16` quadratic / `1/4` linear):
two-sided tail for sums of independent mean-zero sub-exponential variables.
Name avoids the taken `bernstein_inequality` (moment-condition version in
`Bernstein/Bernstein.lean`). -/
theorem bernstein_subexponential
    -- LEAN-ONLY: probability measure; Chernoff/MGF machinery requires it
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: nonempty sum so max Kᵢ is well-defined
    (hn : 0 < n)
    -- LEAN-ONLY: measurability of each summand
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Thm 2.9.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero; HDP Thm 2.9.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening, see module notes)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₁} ≤ Kᵢ; HDP Thm 2.9.1
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K i)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Thm 2.9.1
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
        (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ))))))  := by sorry

/-- **Weighted Bernstein** (HDP Corollary 2.9.2; BONUS — this file's allowed
named-sorry debt): tail for `∑ aᵢ Xᵢ` with uniform ψ₁ bound `K`, exponent
`min (t²/(16 K² ‖a‖₂²)) (t/(4 K ‖a‖_∞))`. -/
theorem bernstein_subexponential_weighted
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ≥0}
    (a : Fin n → ℝ)
    -- LEAN-ONLY: nonempty sum
    (hn : 0 < n)
    -- LEAN-ONLY: nonzero weights (zero weights removable by reindexing)
    (ha : ∀ i, a i ≠ 0)
    -- LEAN-ONLY: measurability of each summand
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Cor 2.9.2
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero; HDP Cor 2.9.2
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive uniform norm bound
    (hKpos : 0 < K)
    -- USER-INPUT: uniform ψ₁ bound ‖Xᵢ‖_{ψ₁} ≤ K; HDP Cor 2.9.2
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Cor 2.9.2
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, a i * X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-(min (t ^ 2 / (16 * (K : ℝ) ^ 2 * ∑ i, (a i) ^ 2))
          (t / (4 * (K : ℝ) *
            ((Finset.univ.sup fun i => ‖a i‖₊ : ℝ≥0) : ℝ)))))) := by
  sorry

end StatLean.ConcentrationInequalities
