import StatLean.Optimization.AcceleratedProximal

/-!
# Convergence of accelerated gradient descent (Theorem 11.3)

Lu, *Big Data Analysis* §11.3, Theorem `thm:cvg-agd`: Nesterov's accelerated
gradient descent (AGD) achieves the `O(1/t²)` rate.

AGD (`x_0 = y_0`, `λ_0 = 1`, `λ_{t+1} = (1 + √(1 + 4λ_t²))/2`):
* `x_{t+1} = y_t - (1/L) ∇f(y_t)`   (a plain gradient step);
* `y_{t+1} = x_{t+1} + ((λ_t - 1)/λ_{t+1}) (x_{t+1} - x_t)`.

This is the `h = 0` special case of accelerated proximal gradient descent
(Theorem 12.2, `acceleratedProximalGradient_rate`): the proximal operator of the
zero function is the identity, so the prox step `prox_{(1/L)·0}(y_t - (1/L)∇f(y_t))`
is exactly the gradient step `y_t - (1/L)∇f(y_t)`. We obtain the theorem as a
direct corollary, per the book's remark following Theorem 12.2.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Thm 11.3 (`thm:cvg-agd`, convergence of AGD). For convex `L`-smooth `f`
(`0 < L`) with step `1/L`, Nesterov's accelerated gradient descent satisfies
`f(x_t) - f(x*) ≤ 2L‖x_0 - x*‖²/(t+1)²`. Stated for `t ≥ 1` (inherited from
Theorem 12.2). Proved as the `h = 0` specialization of
`acceleratedProximalGradient_rate`. -/
theorem acceleratedGradientDescent_rate
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L)
    (x y : ℕ → E) (lam : ℕ → ℝ)
    (hxy0 : y 0 = x 0) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (hxrec : ∀ t, x (t + 1) = y t - (1 / L) • gradient f (y t))
    (hyrec : ∀ t, y (t + 1) = x (t + 1) + ((lam t - 1) / lam (t + 1)) • (x (t + 1) - x t))
    {xstar : E} (hmin : ∀ z, f xstar ≤ f z)
    (t : ℕ) (ht : 1 ≤ t) :
    f (x t) - f xstar ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2 := by
  -- the zero penalty is convex, and its prox step is the gradient step
  have hh0 : ConvexOn ℝ Set.univ (fun _ : E => (0 : ℝ)) := convexOn_const 0 convex_univ
  have hprox : ∀ t, IsProxMinimizer ((1 / L) • (fun _ : E => (0 : ℝ)))
      (y t - (1 / L) • gradient f (y t)) (x (t + 1)) := by
    intro t w
    rw [hxrec t]
    simp only [proxObj, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖w - (y t - (1 / L) • gradient f (y t))‖]
  have hmin0 : ∀ z, f xstar + (fun _ : E => (0 : ℝ)) xstar ≤ f z + (fun _ : E => (0 : ℝ)) z :=
    fun z => by simpa using hmin z
  have key := acceleratedProximalGradient_rate hf hdiff hL hsmooth hh0 x y lam hxy0 hlam0
    hlamrec hprox hyrec hmin0 t ht
  simpa using key

end StatLean.Optimization
