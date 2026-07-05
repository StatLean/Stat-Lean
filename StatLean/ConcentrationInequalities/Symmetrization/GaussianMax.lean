import StatLean.ConcentrationInequalities.Symmetrization.GaussianVector
import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Expected maximum of independent standard Gaussians

For $g_1, \dots, g_N$ i.i.d. standard Gaussians ($N \ge 1$),
$$ \mathbb{E}\,\max_{i \le N} |g_i| \;\le\; \sqrt{2 \log (2N)}, $$
equivalently $\mathbb{E}\,\|g\|_\infty \le \sqrt{2\log(2N)}$ for the Pi
sup-norm on $\mathrm{Fin}\,N \to \mathbb{R}$. This is the explicit-constant
replacement for the book's "$\mathbb{E}\|g\|_\infty \le C\sqrt{\log N}$"
(cited from Exercise 2.38(a)) in the lower bound of Lemma 6.6.2.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, p. 186 (in the proof of Lemma 6.6.2);
the underlying maximal inequality is §2.5, Exercise 2.38(a).

**Proof formalization notes.** We reuse our
`Maximal/FiniteMaximal.expectation_max_le` **verbatim** on the `2N`-fold
one-sided family `(gᵢ, −gᵢ)` reindexed along `finSumFinEquiv` (each member
centered sub-Gaussian with `σ² = 1` by
`isSubGaussian_eval_gaussVec`/`isSubGaussian_neg_eval_gaussVec`), giving
`√1·√(2 log(2N))`. **Documented deviation:** the `2N` inside the logarithm
(vs. the book's unnamed `C√(log N)`) is the standard union-bound cost of the
two-sided maximum; the `N ≥ 2` corollary consumed by
`gaussian_symmetrization_lower_log` absorbs it via `log(2N) ≤ 2 log N`.
The Pi-norm ↔ `ciSup`-of-abs bridge `pi_norm_eq_ciSup_abs` is `LEAN-ONLY`
glue (`pi_norm_le_iff_of_nonneg` + `norm_le_pi_norm`). Named-sorry fallback
of this work item: `integral_ciSup_abs_gaussVec_le` (the bridge lemma
proven); `expectation_max_le` is reused, never re-derived.

**Bibliographic comments.** The $\sqrt{2\log N}$ growth of Gaussian maxima is
classical extreme-value theory (Cramér, 1946); the sub-Gaussian
maximal-inequality route used here is the textbook argument of HDP §2.5 and
Boucheron–Lugosi–Massart, *Concentration Inequalities* (2013), §2.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The `Fintype` Pi norm on `ι → ℝ` is the supremum of the coordinate
absolute values. -/
-- LEAN-ONLY: norm/ciSup bridge; via pi_norm_le_iff_of_nonneg + norm_le_pi_norm.
theorem pi_norm_eq_ciSup_abs {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ‖v‖ = ⨆ i, |v i| := by
  sorry

/-- **Expected two-sided Gaussian maximum** (HDP §6.6, p. 186, explicit
constant): `E max_i |gᵢ| ≤ √(2 log(2N))`. The `2N` is the union-bound cost of
two-sidedness (documented deviation from the book's `C√(log N)`). Named-sorry
debt candidate of this work item; reuses `expectation_max_le` on the
`2N`-family `(gᵢ, −gᵢ)`. -/
theorem integral_ciSup_abs_gaussVec_le (N : ℕ) [NeZero N] :
    ∫ g, ⨆ i, |g i| ∂(gaussVec N) ≤ Real.sqrt (2 * Real.log (2 * N)) := by
  sorry

/-- **Expected sup-norm of the Gaussian vector** (HDP §6.6, p. 186):
`E‖g‖_∞ ≤ √(2 log(2N))`; the Pi-norm phrasing of
`integral_ciSup_abs_gaussVec_le`. -/
theorem integral_pi_norm_gaussVec_le (N : ℕ) [NeZero N] :
    ∫ g, ‖g‖ ∂(gaussVec N) ≤ Real.sqrt (2 * Real.log (2 * N)) := by
  sorry

end StatLean.ConcentrationInequalities
