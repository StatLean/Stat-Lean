import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbersCountable
import StatLean.ConcentrationInequalities.ForMathlib.SupRatApprox
import Mathlib.Probability.CDF

/-!
# Glivenko–Cantelli theorem (in expectation)

For i.i.d. real data with common law $\mu$ and empirical CDF $F_n$,
$$ \mathbb{E}\, \|F_n - F\|_\infty
   \;=\; \mathbb{E} \sup_{t \in \mathbb{R}} |F_n(t) - F(t)|
   \;\le\; \frac{5400}{\sqrt{n}}. $$
The class is $\{\mathbf{1}_{(-\infty,\,t]} : t \in \mathbb{R}\}$; its VC
dimension is computed exactly ($= 1$), and the *full uncountable* supremum
over $\mathbb{R}$ is recovered deterministically from the rational
subclass by right-continuity — no countability hypothesis in the headline.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.17.

**Proof formalization notes.** Deviations: (1) the book bounds
$\mathrm{vc} \le 2$ via Example 8.3.2; we compute the exact value
`vcDim iicClass = 1` (half-lines cannot realize the labeling
$g(p) = 0, g(q) = 1$ for $p < q$) — documented deviation, giving
`√d = 1`. (2) Frozen numeral `5400/√n` inherited from `vc_lln_countable`
(formula `2 × 40 × √6 × 27`, see `VC/LawOfLargeNumbers.lean`). Sup policy:
`vc_lln_countable` is applied to the countable rational subclass
`iicRatClass`; the ℝ-sup equals the ℚ-sup pointwise by right-continuity of
both the empirical CDF (`empFrac_iic_rightContinuous`, finitely many jumps)
and the population CDF (`real_iic_rightContinuous`, R6 split helper —
`StieltjesFunction` fields of `ProbabilityTheory.cdf`), through the generic
bridge `iSup_eq_iSup_rat_of_right_approx` (`ForMathlib/SupRatApprox.lean`).
Work-item single named-sorry fallback: `iSup_iic_diff_eq_iSup_rat` (the
deterministic ℝ→ℚ sup bridge); `vcDim_iicClass` and the LLN instantiation
must close.

**Bibliographic comments.** V. Glivenko and F. P. Cantelli (1933),
*Giornale dell'Istituto Italiano degli Attuari* 4; the in-expectation
$n^{-1/2}$ form with the VC route is HDP §8.3.6; the sharp constant is the
DKW inequality (Dvoretzky–Kiefer–Wolfowitz 1956, Massart 1990), out of
scope here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

/-- The half-line class `{(-∞, t] : t ∈ ℝ}` (HDP Theorem 8.3.17). -/
def iicClass : Set (Set ℝ) := Set.range Set.Iic

/-- Countable rational subclass (LEAN-ONLY: sup-policy device). -/
def iicRatClass : Set (Set ℝ) := ⋃ q : ℚ, {Set.Iic (q : ℝ)}

/-- The half-line class has VC dimension exactly `1` (HDP §8.3.6; the book
uses the bound `≤ 2` via Example 8.3.2 — we compute the exact value:
one point is shattered; for `p < q` no member realizes `p ∉ S, q ∈ S`).
Documented deviation (sharper than the book). -/
theorem vcDim_iicClass : vcDim iicClass = 1 := by sorry

/-- The empirical CDF is right-continuous in the threshold (LEAN-ONLY:
finitely many jumps; `Set.Iic`-membership is right-stable). -/
lemma empFrac_iic_rightContinuous {n : ℕ} (x : Fin n → ℝ) :
    ∀ t : ℝ, ContinuousWithinAt (fun s => empFrac x (Set.Iic s))
      (Set.Ici t) t := by sorry

/-- The population CDF `t ↦ μ.real (Iic t)` is right-continuous (LEAN-ONLY,
batch reconciliation R6 split helper: `StieltjesFunction` fields of
`ProbabilityTheory.cdf` transported to `μ.real ∘ Set.Iic`). Kept separate
from `iSup_iic_diff_eq_iSup_rat` so debts stay atomic. -/
lemma real_iic_rightContinuous (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ t : ℝ, ContinuousWithinAt (fun s => μ.real (Set.Iic s))
      (Set.Ici t) t := by sorry

/-- Deterministic ℝ→ℚ sup recovery for the CDF deviation (HDP §8.3.6 proof;
via `iSup_eq_iSup_rat_of_right_approx` + the two right-continuity lemmas).
This work item's single named-sorry fallback. -/
lemma iSup_iic_diff_eq_iSup_rat {n : ℕ} (x : Fin n → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (⨆ t : ℝ, |empFrac x (Set.Iic t) - μ.real (Set.Iic t)|) =
      ⨆ q : ℚ, |empFrac x (Set.Iic (q : ℝ)) - μ.real (Set.Iic (q : ℝ))| := by
  sorry

/-- **Theorem 8.3.17 (Glivenko–Cantelli, in expectation)** (HDP §8.3.6;
frozen numeral `5400/√n`, formula `2 × 40 × √6 × 27` at `d = 1` — see
module notes): the expected sup-distance between the empirical and
population CDFs, with the genuine full supremum over `ℝ`. -/
theorem glivenko_cantelli {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → ℝ}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.3.17
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.3.17 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit)
    (hn : 1 ≤ n) :
    ∫ ξ, ⨆ t : ℝ, |empFrac (fun i : Fin n => X i ξ) (Set.Iic t) -
        μ.real (Set.Iic t)| ∂P ≤ 5400 / Real.sqrt n := by sorry

end StatLean.ConcentrationInequalities
