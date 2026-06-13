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
  -- Monotone descent (pillar with `x = y = x_s`).
  have hdesc : ∀ s, f (x (s + 1)) + h (x (s + 1)) ≤ f (x s) + h (x s) := by
    intro s
    have hp := pillar hf hdiff hL hsmooth hh (x := x s) (hrec s)
    have h0 : ‖x s - x s‖ ^ 2 = 0 := by rw [sub_self, norm_zero]; ring
    rw [h0] at hp
    nlinarith [hp, sq_nonneg ‖x s - x (s + 1)‖, hL]
  have hanti : Antitone (fun s => f (x s) + h (x s) - (f xstar + h xstar)) :=
    antitone_nat_of_succ_le (fun s => by linarith [hdesc s])
  -- Telescoping step (pillar with `x = x*`, `y = x_s`).
  have hstep : ∀ s, f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)
      ≤ L / 2 * ‖xstar - x s‖ ^ 2 - L / 2 * ‖xstar - x (s + 1)‖ ^ 2 :=
    fun s => pillar hf hdiff hL hsmooth hh (x := xstar) (hrec s)
  -- Sum the telescoping bound.
  have hsum : ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar))
      ≤ L / 2 * ‖x 0 - xstar‖ ^ 2 := by
    calc ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar))
        ≤ ∑ s ∈ Finset.range t,
            (L / 2 * ‖xstar - x s‖ ^ 2 - L / 2 * ‖xstar - x (s + 1)‖ ^ 2) :=
          Finset.sum_le_sum (fun s _ => hstep s)
      _ = L / 2 * ‖xstar - x 0‖ ^ 2 - L / 2 * ‖xstar - x t‖ ^ 2 :=
          Finset.sum_range_sub' (fun s => L / 2 * ‖xstar - x s‖ ^ 2) t
      _ ≤ L / 2 * ‖xstar - x 0‖ ^ 2 := by nlinarith [sq_nonneg ‖xstar - x t‖, hL]
      _ = L / 2 * ‖x 0 - xstar‖ ^ 2 := by rw [norm_sub_rev]
  -- `t · δ_t ≤ ∑ δ_{s+1}` by antitonicity.
  have hlb : (t : ℝ) * (f (x t) + h (x t) - (f xstar + h xstar))
      ≤ ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) := by
    calc (t : ℝ) * (f (x t) + h (x t) - (f xstar + h xstar))
        = ∑ _s ∈ Finset.range t, (f (x t) + h (x t) - (f xstar + h xstar)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ s ∈ Finset.range t, (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) :=
          Finset.sum_le_sum fun s hs =>
            hanti (Nat.succ_le_of_lt (Finset.mem_range.mp hs))
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (t : ℝ))]
  nlinarith [hlb, hsum]

end StatLean.Optimization
