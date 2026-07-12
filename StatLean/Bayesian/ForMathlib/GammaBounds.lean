import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Probability.Distributions.Gamma

/-!
# Elementary two-sided bounds on the Gamma function

The handful of numeric Gamma-function estimates the Dirichlet–Laplace marginal-density analysis
needs: the range of `Γ(1 + a)` for `a ∈ [0, 1]`, the derived bounds on `Γ(a)`, `Γ(1 − a)`, and the
half-integer factorial bound `Γ(q/2 + 1) ≤ (q + 1)^{q+1}`. Plus the (measure-theoretic) fact that
the Gamma law puts no mass on the nonpositive half-line.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*
(arXiv:1401.5398), Lemma 3.3 and §6 ball-volume bookkeeping, which invoke these **elementary Gamma
bounds** (there stated without proof, and — see below — with one erroneous constant). All estimates
here are classical facts about `Γ` on `(0, 2]`.

**Proof formalization notes (deviation D6).** We prove everything from the single range
`Γ(1 + a) ∈ [e⁻¹, 2]` for `a ∈ [0, 1]` (`exp_neg_one_le_Gamma_one_add`, `Gamma_one_add_le_two`),
obtained by convexity/monotonicity of `Γ` on `[1, 2]` together with `Γ(1) = Γ(2) = 1` — **avoiding
Alzer's inequality** (which the paper's sketch leans on and which is not in Mathlib). The
recurrence `Γ(a) = Γ(1 + a)/a` then gives `Γ(a) ≤ 2/a` and `Γ(a) ≥ 1/(e·a)` on `(0, 1]`; note the
paper's "`Γ(x) ≥ 1/x`" is **false as stated** (e.g. `Γ(1) = 1 = 1/1` is not a strict lower bound and
`Γ` dips below `1/x` for small `x` only up to the `e` factor), so we carry the correct
`Γ(a) ≥ 1/(e·a)`. `Gamma_one_sub_le_four` uses `1 − a ∈ [1/2, 1]` with `Γ(1/2) = √π < 4`;
`Gamma_half_add_one_le` chains `Γ(q/2 + 1) ≤ Γ(q + 1) = q!` (monotonicity on `[2, ∞)`,
`Real.Gamma_nat_eq_factorial`) with `q! ≤ (q + 1)^{q+1}`. `gammaMeasure_Iic_eq_zero` holds because
`gammaPDFReal` is `0` on `x < 0` and `{0}` is Lebesgue-null.

**Bibliographic comments.** The convexity/log-convexity of `Γ` and its characterization on `[1, 2]`
are the Bohr–Mollerup theorem (H. Bohr, J. Mollerup, 1922); the factorial identity `Γ(n + 1) = n!`
is Euler's (1729).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- `Γ(1 + a) ≤ 2` for `a ∈ [0, 1]` (in fact `Γ(1 + a) ≤ 1` there, by convexity with
`Γ(1) = Γ(2) = 1`; the looser bound `2` is all downstream needs). Deviation D6. -/
theorem Gamma_one_add_le_two {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 + a ∈ [1, 2] where Γ ≤ 1 (convexity on [1,2])
    (ha0 : 0 ≤ a)
    -- LEAN-ONLY: a ≤ 1, upper end of the [1,2] window
    (ha1 : a ≤ 1) :
    Real.Gamma (1 + a) ≤ 2 := by
  sorry

/-- `e⁻¹ ≤ Γ(1 + a)` for `a ∈ [0, 1]` (the minimum of `Γ` on `[1, 2]` is `≈ 0.886 > e⁻¹`).
Deviation D6. -/
theorem exp_neg_one_le_Gamma_one_add {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 + a ∈ [1, 2] where Γ ≥ e⁻¹
    (ha0 : 0 ≤ a)
    -- LEAN-ONLY: a ≤ 1, upper end of the [1,2] window
    (ha1 : a ≤ 1) :
    Real.exp (-1) ≤ Real.Gamma (1 + a) := by
  sorry

/-- `Γ(a) ≤ 2/a` on `(0, 1]`, from `Γ(a) = Γ(1 + a)/a` and `Γ(1 + a) ≤ 2`. -/
theorem Gamma_le_two_div {a : ℝ}
    -- LEAN-ONLY: a > 0, so the recurrence Γ(a) = Γ(1+a)/a is valid and a⁻¹ > 0
    (ha0 : 0 < a)
    -- LEAN-ONLY: a ≤ 1, the range on which Γ(1+a) ≤ 2 holds
    (ha1 : a ≤ 1) :
    Real.Gamma a ≤ 2 / a := by
  sorry

/-- `1/(e·a) ≤ Γ(a)` on `(0, 1]`, from `Γ(a) = Γ(1 + a)/a` and `Γ(1 + a) ≥ e⁻¹`. This is the
correct form of the paper's (erroneous) `Γ(x) ≥ 1/x`; deviation D6. -/
theorem inv_e_mul_le_Gamma {a : ℝ}
    -- LEAN-ONLY: a > 0, so the recurrence Γ(a) = Γ(1+a)/a is valid
    (ha0 : 0 < a)
    -- LEAN-ONLY: a ≤ 1, the range on which Γ(1+a) ≥ e⁻¹ holds
    (ha1 : a ≤ 1) :
    1 / (Real.exp 1 * a) ≤ Real.Gamma a := by
  sorry

/-- `e⁻¹ ≤ Γ(x)` for `x ≥ 1` (uniform lower bound on `[1, ∞)`): on `[1, 2]` this is
`exp_neg_one_le_Gamma_one_add`; on `[2, ∞)` monotonicity of `Γ` gives `Γ(x) ≥ Γ(2) = 1 ≥ e⁻¹`. -/
theorem exp_neg_one_le_Gamma {x : ℝ}
    -- LEAN-ONLY: x ≥ 1; below 1 the Γ pole makes Γ arbitrarily large but the bound is not needed
    (hx : 1 ≤ x) :
    Real.exp (-1) ≤ Real.Gamma x := by
  sorry

/-- `Γ(1 − a) ≤ 4` for `a ∈ [0, 1/2]` (`1 − a ∈ [1/2, 1]`, where `Γ ≤ Γ(1/2) = √π < 4`). The
`a ≤ 1/2` ceiling is deviation D8 (the density upper bound genuinely needs it: `Γ(1 − a)` blows up as
`a → 1`). -/
theorem Gamma_one_sub_le_four {a : ℝ}
    -- LEAN-ONLY: a ≥ 0, so 1 − a ≤ 1 stays in the bounded window
    (ha0 : 0 ≤ a)
    -- USER-INPUT: a ≤ 1/2 keeps Γ(1−a) finite (Γ(1−a)→∞ as a→1); BPPD Lemma 3.2 (D8)
    (ha1 : a ≤ 1 / 2) :
    Real.Gamma (1 - a) ≤ 4 := by
  sorry

/-- `Γ(q/2 + 1) ≤ (q + 1)^{q+1}` for natural `q` (a crude factorial bound for the ball-volume
denominators): `Γ(q/2 + 1) ≤ Γ(q + 1) = q! ≤ (q + 1)^{q+1}`. -/
theorem Gamma_half_add_one_le (q : ℕ) :
    Real.Gamma ((q : ℝ) / 2 + 1) ≤ ((q : ℝ) + 1) ^ (q + 1) := by
  sorry

/-- The Gamma law puts no mass on the nonpositive half-line: `gammaMeasure a r (Iic 0) = 0`.
(`gammaPDFReal` is `0` on `x < 0`, and `{0}` is Lebesgue-null.) Needed for the probability-measure
instance on the Dirichlet–Laplace mixture. -/
theorem gammaMeasure_Iic_eq_zero {a r : ℝ}
    -- LEAN-ONLY: a > 0, shape of a genuine Gamma law
    (ha : 0 < a)
    -- LEAN-ONLY: r > 0, rate of a genuine Gamma law
    (hr : 0 < r) :
    gammaMeasure a r (Set.Iic 0) = 0 := by
  sorry

end StatLean.Bayesian
