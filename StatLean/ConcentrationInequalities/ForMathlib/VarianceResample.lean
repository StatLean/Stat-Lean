import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Variance as a half-averaged squared difference of two independent copies

For a probability measure $\nu$ and a square-integrable $g$,
$$ \operatorname{Var}(g) \;=\; \tfrac12 \int\!\!\int \bigl(g(a) - g(b)\bigr)^2
   \, d\nu(a)\, d\nu(b), $$
the elementary identity $\operatorname{Var}(X) = \tfrac12 \mathbb{E}\,(X - Y)^2$ for
independent identically distributed $X, Y$, written directly as an iterated integral so
that no auxiliary product space is needed. Absent from Mathlib at our pin (verified by
search for `variance_eq_half`, `integrable_sq` and the `IdentDistrib` API in
`Mathlib/Probability/Moments/Variance.lean`); Mathlib-only imports — candidate upstream.

This is the brick that converts the leave-one-out conditional variance
$\operatorname{Var}^{(i)}(Z)$ of the Efron–Stein bound into its resampled form
$\tfrac12\,\mathbb{E}\,(Z - Z_i')^2$. It supplies the iid-copy variance identity; the
product-law interpretation of the replacement coordinate is supplied by `PiUpdate`.

**Reference.** Stéphane Boucheron, Gábor Lugosi and Pascal Massart, *Concentration
Inequalities: A Nonasymptotic Theory of Independence*, Oxford University Press, 2013
(ISBN 978-0-19-953525-5), §3.1, inside the proof of Theorem 3.1: "one may simply use
(conditionally) the elementary fact that if $X$ and $Y$ are independent and identically
distributed real-valued random variables, then $\operatorname{Var}(X) = (1/2)
\mathbb{E}[(X-Y)^2]$."

**Proof formalization notes.** Pure expansion: center by $m = \nu[g]$, write
$(g(a) - g(b))^2 = (g(a) - m)^2 - 2 (g(a) - m)(g(b) - m) + (g(b) - m)^2$, and integrate in
$b$ first — the cross term vanishes because $\int (g - m)\, d\nu = 0$. Integrability of
every piece comes from `MemLp.integrable one_le_two` and `MemLp.integrable_sq` against the
finite measure. `variance_eq_integral` supplies the centered form of the variance.

**Bibliographic comments.** The identity is folklore: it is the $U$-statistic
representation of the variance. Boucheron–Lugosi–Massart state it without attribution as
an "elementary fact", and no attribution is asserted here beyond that.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {g : α → ℝ}

/-- **The centered integrand integrates to zero.** -/
private lemma integral_sub_integral_eq_zero (hg : Integrable g ν) :
    ∫ b, (g b - ν[g]) ∂ν = 0 := by
  rw [integral_sub hg (integrable_const _)]
  simp

/-- **Jensen for a probability measure**: the square of the mean is at most the mean of
the square. Immediate from `variance_nonneg` and `variance_eq_sub`. -/
theorem sq_integral_le_integral_sq (hg : MemLp g 2 ν) :
    (∫ a, g a ∂ν) ^ 2 ≤ ∫ a, g a ^ 2 ∂ν := by
  have h : (0 : ℝ) ≤ Var[g; ν] := variance_nonneg g ν
  rw [variance_eq_sub hg] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- **Inner integral.** For each fixed `a`, averaging `(g a - g b) ^ 2` over `b` gives the
squared centered value at `a` plus the variance. -/
theorem integral_sub_sq_right (hg : MemLp g 2 ν) (a : α) :
    ∫ b, (g a - g b) ^ 2 ∂ν = (g a - ν[g]) ^ 2 + Var[g; ν] := by
  have hg1 : Integrable g ν := hg.integrable one_le_two
  have hcent : MemLp (fun b => g b - ν[g]) 2 ν := hg.sub (memLp_const _)
  have hcent1 : Integrable (fun b => g b - ν[g]) ν := hcent.integrable one_le_two
  have hcent2 : Integrable (fun b => (g b - ν[g]) ^ 2) ν := hcent.integrable_sq
  have hexp : ∀ b, (g a - g b) ^ 2
      = ((g a - ν[g]) ^ 2 - 2 * (g a - ν[g]) * (g b - ν[g])) + (g b - ν[g]) ^ 2 := by
    intro b; ring
  have hf1 : Integrable (fun b => (g a - ν[g]) ^ 2 - 2 * (g a - ν[g]) * (g b - ν[g])) ν :=
    (integrable_const _).sub (hcent1.const_mul (2 * (g a - ν[g])))
  simp_rw [hexp]
  rw [integral_add hf1 hcent2,
    integral_sub (integrable_const _) (hcent1.const_mul (2 * (g a - ν[g]))),
    integral_const_mul, integral_sub_integral_eq_zero hg1, mul_zero, sub_zero,
    ← variance_eq_integral hg1.aemeasurable]
  simp

/-- **Variance as a half-averaged squared difference of two independent copies**
(Boucheron–Lugosi–Massart 2013, §3.1, inside the proof of Theorem 3.1). For a probability
measure `ν` and `g ∈ L²(ν)`,
$$\int\!\!\int (g(a) - g(b))^2 \, d\nu \, d\nu = 2 \operatorname{Var}(g).$$ -/
theorem integral_integral_sub_sq_eq_two_mul_variance (hg : MemLp g 2 ν) :
    ∫ a, ∫ b, (g a - g b) ^ 2 ∂ν ∂ν = 2 * Var[g; ν] := by
  have hg1 : Integrable g ν := hg.integrable one_le_two
  have hcent : MemLp (fun a => g a - ν[g]) 2 ν := hg.sub (memLp_const _)
  have hcent2 : Integrable (fun a => (g a - ν[g]) ^ 2) ν := hcent.integrable_sq
  calc ∫ a, ∫ b, (g a - g b) ^ 2 ∂ν ∂ν
      = ∫ a, ((g a - ν[g]) ^ 2 + Var[g; ν]) ∂ν := by
        exact integral_congr_ae (by filter_upwards with a using integral_sub_sq_right hg a)
    _ = (∫ a, (g a - ν[g]) ^ 2 ∂ν) + Var[g; ν] := by
        rw [integral_add hcent2 (integrable_const _)]
        simp
    _ = 2 * Var[g; ν] := by
        rw [← variance_eq_integral hg1.aemeasurable]; ring

/-- The same identity in the form used by the Efron–Stein development: the conditional
variance is **half** the averaged squared difference. -/
theorem variance_eq_half_integral_integral_sub_sq (hg : MemLp g 2 ν) :
    Var[g; ν] = (1 / 2) * ∫ a, ∫ b, (g a - g b) ^ 2 ∂ν ∂ν := by
  rw [integral_integral_sub_sq_eq_two_mul_variance hg]; ring

end StatLean.ConcentrationInequalities
