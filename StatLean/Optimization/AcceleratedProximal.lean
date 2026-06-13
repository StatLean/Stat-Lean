import StatLean.Optimization.Prox.Pillar
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Convergence of accelerated proximal gradient descent (Theorem 12.2)

Lu, *Big Data Analysis* §12.2, Theorem `thm:cvg-aprox`: with Nesterov momentum,
the accelerated proximal-gradient iterates achieve the faster `O(1/t²)` rate
`F(x_t) - F(x*) ≤ 2L‖x_0 - x*‖² / (t+1)²`.

Algorithm (with `x_0 = y_0`, `λ_0 = 1`, `λ_{t+1} = (1 + √(1 + 4λ_t²))/2`):
* `x_{t+1} = prox_{(1/L)h}(y_t - (1/L)∇f(y_t))`;
* `y_{t+1} = x_{t+1} + ((λ_t - 1)/λ_{t+1})(x_{t+1} - x_t)`.

The proof is not monotone in `F`; it uses the pillar inequality (Lemma 12.1)
together with a Lyapunov energy `L_t = ‖u_t‖² + (2/L)λ_{t-1}²(F(x_t) - F(x*))`
(Lemma 12.2 below) shown to be non-increasing, plus the Nesterov-sequence bound
`λ_t ≥ (t+2)/2` (`nesterov_lambda_lower`).
-/

namespace StatLean.Optimization

open scoped InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Nesterov extrapolation sequence `λ_0 = 1`,
`λ_{t+1} = (1 + √(1 + 4λ_t²))/2` satisfies `λ_t ≥ (t+2)/2` (Lu-BDA §12.2). -/
theorem nesterov_lambda_lower
    (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (t : ℕ) :
    ((t : ℝ) + 2) / 2 ≤ lam t := by
  induction t with
  | zero => rw [hlam0]; norm_num
  | succ k ih =>
    have hk_nonneg : (0 : ℝ) ≤ lam k := le_trans (by positivity) ih
    rw [hlamrec k]
    have hsqrt : ((k : ℝ) + 2) ≤ Real.sqrt (1 + 4 * lam k ^ 2) := by
      rw [show ((k : ℝ) + 2) = Real.sqrt (((k : ℝ) + 2) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h2 : (k : ℝ) + 2 ≤ 2 * lam k := by linarith [ih]
      have hsq : ((k : ℝ) + 2) ^ 2 ≤ (2 * lam k) ^ 2 :=
        sq_le_sq' (by linarith [hk_nonneg, hk0]) h2
      nlinarith [hsq]
    push_cast
    linarith [hsqrt]

/-- The Nesterov sequence is strictly positive. -/
private theorem lam_pos (lam : ℕ → ℝ) (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2) (s : ℕ) :
    0 < lam s := by
  have h := nesterov_lambda_lower lam hlam0 hlamrec s
  have : (0 : ℝ) < ((s : ℝ) + 2) / 2 := by positivity
  linarith

/-- The Nesterov-sequence identity `λ_{s+1}² - λ_{s+1} = λ_s²` (Lu-BDA §12.2,
from `(2λ_{s+1} - 1)² = 1 + 4λ_s²`). -/
private theorem lam_sq_sub (lam : ℕ → ℝ)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2) (s : ℕ) :
    lam (s + 1) ^ 2 - lam (s + 1) = lam s ^ 2 := by
  have hsq : Real.sqrt (1 + 4 * lam s ^ 2) ^ 2 = 1 + 4 * lam s ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hlamrec s]
  linear_combination (1 / 4 : ℝ) * hsq

/-- Lu-BDA Thm 12.2 (accelerated proximal-gradient convergence rate). `f` convex
`L`-smooth (`0 < L`), `h` convex, `F = f + h`, step `1/L`, Nesterov momentum:
`F(x_t) - F(x*) ≤ 2L‖x_0 - x*‖² / (t+1)²`. Stated for `t ≥ 1` (the `t = 0` case
is the trivial initial gap), per CLAUDE.md §1 documented deviation. -/
theorem acceleratedProximalGradient_rate
    {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
    (x y : ℕ → E) (lam : ℕ → ℝ)
    (hxy0 : y 0 = x 0)
    (hlam0 : lam 0 = 1)
    (hlamrec : ∀ t, lam (t + 1) = (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2)
    (hxrec : ∀ t, IsProxMinimizer ((1 / L) • h)
        (y t - (1 / L) • gradient f (y t)) (x (t + 1)))
    (hyrec : ∀ t, y (t + 1) = x (t + 1) + ((lam t - 1) / lam (t + 1)) • (x (t + 1) - x t))
    {xstar : E} (hmin : ∀ z, f xstar + h xstar ≤ f z + h z)
    (t : ℕ) (ht : 1 ≤ t) :
    (f (x t) + h (x t)) - (f xstar + h xstar)
      ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((t : ℝ) + 1) ^ 2 := by
  have hLpos : (0 : ℝ) < L := hL
  have hFconv : ConvexOn ℝ Set.univ (fun z => f z + h z) := hf.add hh
  have hlampos : ∀ s, (0 : ℝ) < lam s := fun s => lam_pos lam hlam0 hlamrec s
  -- `u s` = book `u_{s+1}`; `Φ s` = book Lyapunov `L_{s+1}`.
  set u : ℕ → E := fun s => lam s • x (s + 1) - (xstar + (lam s - 1) • x s) with hu
  set Φ : ℕ → ℝ := fun s =>
      ‖u s‖ ^ 2 + 2 / L * lam s ^ 2 *
        (f (x (s + 1)) + h (x (s + 1)) - (f xstar + h xstar)) with hΦ
  -- Lyapunov monotonicity (Lemma 12.2).
  have hΦdec : ∀ s, Φ (s + 1) ≤ Φ s := by
    intro s
    have hλ1 : (0 : ℝ) < lam (s + 1) := hlampos (s + 1)
    have hλ1ne : lam (s + 1) ≠ 0 := ne_of_gt hλ1
    have hλ2pos : (0 : ℝ) < lam (s + 1) ^ 2 := by positivity
    have hλ1ge1 : (1 : ℝ) ≤ lam (s + 1) := by
      have := nesterov_lambda_lower lam hlam0 hlamrec (s + 1); push_cast at this ⊢; linarith
    set xc : E := lam (s + 1)⁻¹ • xstar + (1 - lam (s + 1)⁻¹) • x (s + 1) with hxc
    -- momentum identity: λ_{s+1}•y_{s+1} - (x* + (λ_{s+1}-1)•x_{s+1}) = u s
    have hmom : lam (s + 1) • y (s + 1) - (xstar + (lam (s + 1) - 1) • x (s + 1)) = u s := by
      rw [hyrec s, hu, smul_add, smul_smul, mul_div_cancel₀ _ hλ1ne]; module
    -- λ_{s+1} • xc = x* + (λ_{s+1}-1)•x_{s+1}
    have hλxc : lam (s + 1) • xc = xstar + (lam (s + 1) - 1) • x (s + 1) := by
      rw [hxc, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hλ1ne, one_smul]; module
    -- scaled distances to `u`
    have hsc_y : lam (s + 1) • (xc - y (s + 1)) = -u s := by
      rw [smul_sub, hλxc, ← hmom]; abel
    have hsc_x : lam (s + 1) • (xc - x (s + 2)) = -u (s + 1) := by
      rw [smul_sub, hλxc, hu]; abel
    have hnorm_y : lam (s + 1) ^ 2 * ‖xc - y (s + 1)‖ ^ 2 = ‖u s‖ ^ 2 := by
      have h := congrArg (fun z => ‖z‖ ^ 2) hsc_y
      simpa [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_neg] using h
    have hnorm_x : lam (s + 1) ^ 2 * ‖xc - x (s + 2)‖ ^ 2 = ‖u (s + 1)‖ ^ 2 := by
      have h := congrArg (fun z => ‖z‖ ^ 2) hsc_x
      simpa [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_neg] using h
    -- convexity of F = f+h at the combination
    have hconv : f xc + h xc
        ≤ lam (s + 1)⁻¹ * (f xstar + h xstar)
          + (1 - lam (s + 1)⁻¹) * (f (x (s + 1)) + h (x (s + 1))) := by
      have hw1 : (0 : ℝ) ≤ 1 - lam (s + 1)⁻¹ := by
        have : lam (s + 1)⁻¹ ≤ 1 := (inv_le_one₀ hλ1).mpr hλ1ge1
        linarith
      have hcv := hFconv.2 (Set.mem_univ xstar) (Set.mem_univ (x (s + 1)))
        (by positivity) hw1 (by ring)
      simpa [hxc] using hcv
    -- pillar at the combination
    have hp := pillar hf hdiff hL hsmooth hh (x := xc) (hxrec (s + 1))
    have hλsq := lam_sq_sub lam hlamrec s
    have hp' := mul_le_mul_of_nonneg_left hp hλ2pos.le
    have hconv' := mul_le_mul_of_nonneg_left hconv hλ2pos.le
    rw [hΦ]
    nlinarith [hp', hconv', hnorm_y, hnorm_x, hλsq, hλ1, hλ2pos, mul_pos hLpos hλ2pos]
  -- assembly
  have hΦanti : Antitone Φ := antitone_nat_of_succ_le hΦdec
  have hΦ0 : Φ 0 ≤ ‖x 0 - xstar‖ ^ 2 := by
    have hp0 := pillar hf hdiff hL hsmooth hh (x := xstar) (hxrec 0)
    have hu0 : u 0 = x 1 - xstar := by rw [hu, hlam0]; module
    rw [hΦ, hu0, hlam0, hxy0]
    have e2 : ‖xstar - x 1‖ ^ 2 = ‖x 1 - xstar‖ ^ 2 := by rw [norm_sub_rev]
    have e1 : ‖xstar - x 0‖ ^ 2 = ‖x 0 - xstar‖ ^ 2 := by rw [norm_sub_rev]
    rw [hxy0] at hp0
    nlinarith [hp0, e1, e2, hLpos]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hΦm := le_trans (hΦanti (Nat.zero_le m)) hΦ0
  rw [hΦ] at hΦm
  have hλm : ((m : ℝ) + 2) / 2 ≤ lam m := nesterov_lambda_lower lam hlam0 hlamrec m
  have hλmpos : (0 : ℝ) < lam m := hlampos m
  have hgap : (0 : ℝ) ≤ f (x (m + 1)) + h (x (m + 1)) - (f xstar + h xstar) := by
    linarith [hmin (x (m + 1))]
  have hbound : 2 / L * lam m ^ 2 * (f (x (m + 1)) + h (x (m + 1)) - (f xstar + h xstar))
      ≤ ‖x 0 - xstar‖ ^ 2 := by nlinarith [hΦm, sq_nonneg ‖u m‖]
  have hλmsq : ((m : ℝ) + 2) ^ 2 / 4 ≤ lam m ^ 2 := by nlinarith [hλm, hλmpos]
  push_cast
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1 + 1) ^ 2)]
  nlinarith [hbound, hλmsq, hgap, hLpos, hλmpos, mul_pos hλmpos hλmpos,
    mul_nonneg hgap (sq_nonneg ((m : ℝ) + 2))]

end StatLean.Optimization
