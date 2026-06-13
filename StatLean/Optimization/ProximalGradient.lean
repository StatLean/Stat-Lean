import StatLean.Optimization.Prox.Pillar

/-!
# Convergence of proximal gradient descent (Theorem 12.1)

Lu, *Big Data Analysis* §12.1, Theorem `thm:cvg-prox`: for `F = f + h` with `f`
convex `L`-smooth and `h` convex, the proximal-gradient iterates
`x_{t+1} = prox_{(1/L)h}(x_t - (1/L)∇f(x_t))` satisfy
`F(x_t) - F(x*) ≤ L‖x_0 - x*‖² / (2t)`.

Each step is given as a prox minimizer (`hrec`). The proof applies the pillar
inequality (Lemma 12.1) twice: once with `x = y = x_t` to get monotone descent,
once with `x = x*`, `y = x_t` to get a telescoping bound whose sum yields the
`O(1/t)` rate.
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lu-BDA Thm 12.1 (proximal-gradient convergence rate). `f` convex `L`-smooth
(`0 < L`), `h` convex, `F = f + h`, step `1/L`:
`F(x_t) - F(x*) ≤ L‖x_0 - x*‖² / (2t)`. -/
theorem proximalGradient_rate
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    (x : ℕ → E)
    (hrec : ∀ t, IsProxMinimizer ((1 / L) • h)
        (x t - (1 / L) • gradient f (x t)) (x (t + 1)))
    {xstar : E} (hmin : ∀ y, f xstar + h xstar ≤ f y + h y)
    {t : ℕ} (ht : 0 < t) :
    (f (x t) + h (x t)) - (f xstar + h xstar) ≤ L * ‖x 0 - xstar‖ ^ 2 / (2 * (t : ℝ)) := by
  sorry

end StatLean.Optimization
