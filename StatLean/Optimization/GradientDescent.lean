import StatLean.Optimization.Smoothness.CoCoercive
import StatLean.Optimization.ForMathlib.FirstOrderConvex
import StatLean.Optimization.ForMathlib.GradientCalc

/-!
# Convergence of gradient descent (Theorem 11.1)

Lu, *Big Data Analysis* §11.1, Theorem `thm:gd`: for a convex `L`-smooth `f`,
the gradient-descent iterates `x_{t+1} = x_t - (1/L) ∇f(x_t)` satisfy an
`O(1/t)` rate `f(x_t) - f(x*) ≤ C · ‖x_0 - x*‖² / t`.

The iteration is supplied abstractly: `x : ℕ → E` with the recurrence `hrec`,
and `x*` is a global minimizer (`hmin`), from which `∇f(x*) = 0` is derived
(`gradient_eq_zero_of_forall_le`). The proof goes through co-coercivity
(`cocoercive`, Lemma 11.1): the distance `‖x_t - x*‖` is non-increasing, and a
telescoping/recursive bound on `δ_t = f(x_t) - f(x*)` yields the rate.

**Constant.** The book writes `2L‖x_0 - x*‖²/t`; the constant stated here is to
be set to the value actually provable from the telescoping during proof closure
(expected `L/2`, i.e. the proximal-gradient bound with `h = 0`). Any deviation
from the book is documented at proof time.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Thm 11.1 (gradient-descent convergence rate). Convex `L`-smooth `f`,
step `1/L`, global minimizer `x*`: `f(x_t) - f(x*) ≤ 2L‖x_0 - x*‖²/t`
(constant subject to adjustment to the provable value; see module docstring). -/
theorem gradientDescent_rate
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    (x : ℕ → E) (hrec : ∀ t, x (t + 1) = x t - (1 / L) • gradient f (x t))
    {xstar : E} (hmin : ∀ y, f xstar ≤ f y)
    {t : ℕ} (ht : 0 < t) :
    f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / (t : ℝ) := by
  sorry

end StatLean.Optimization
