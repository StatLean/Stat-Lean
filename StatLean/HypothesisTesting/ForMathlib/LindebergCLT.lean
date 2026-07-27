import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Lindeberg central limit theorem for triangular arrays

Mathlib's central limit theorem
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) covers a *single* i.i.d.
sequence. The asymptotics of permutation, randomization and bootstrap distributions all
need the strictly more general **triangular-array** form: for each `n` a finite row
`X n 0, …, X n (m n − 1)` of independent, centered, square-integrable variables whose
variances add up to `1` in the limit and which satisfy the **Lindeberg condition**
$$\sum_i \mathbb E\bigl[X_{n,i}^2\,\mathbf 1\{|X_{n,i}| > \varepsilon\}\bigr] \to 0
  \qquad (\forall\,\varepsilon > 0),$$
the row sums `∑ᵢ Xₙ,ᵢ` converge in distribution to the standard normal law. Rows are
unrelated to each other (no nesting, no common marginal), which is exactly what the
downstream applications need: after conditioning on the data, a permutation statistic is a
row of independent summands whose law changes with `n`.

## Main results

* `lindeberg_clt` — the triangular-array CLT under the Lindeberg condition.
* `lindeberg_clt_of_bounded` — the uniformly-bounded corollary (`|Xₙ,ᵢ| ≤ cₙ`, `cₙ → 0`),
  which is the form most often applied.
* `weighted_iid_clt` — weighted sums `∑ᵢ wₙ,ᵢ Yᵢ` of an i.i.d. sequence, under the
  negligibility condition `maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`.
* `triangular_wlln_of_L1` — the companion weak law: row-i.i.d. arrays whose row laws
  converge weakly *and* whose first absolute moments converge have row averages converging
  in probability to the limiting mean.

Convergence in distribution is stated with Mathlib's `MeasureTheory.TendstoInDistribution`
(random-variable form, constant family of underlying spaces `fun _ => P`), which is the
convention already used by the multivariate CLT elsewhere in the project; convergence in
probability with `MeasureTheory.TendstoInMeasure`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 11 (Basic Large-Sample
Theory), §11.2 (Weak Convergence and Central Limit Theorems), the Lindeberg–Feller central
limit theorem for triangular arrays. (`TSH4 §11.2`.)

**Proof formalization notes.**
* Route: characteristic functions. Lindeberg's swapping/telescoping argument bounds
  `|∏ᵢ φₙ,ᵢ(t) − exp(−t²/2)|` by a sum of third-order remainders split at the level `ε`;
  Lévy continuity (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) then
  converts pointwise `charFun` convergence into weak convergence, exactly as in the
  project's multivariate CLT.
* The variance normalisation is stated as `∑ᵢ Var[Xₙ,ᵢ] → 1` rather than the textbook's
  exact `= 1`; this is strictly more general (rescaling a row by `sₙ` is not always
  available downstream) and is what the swapping argument actually consumes.
* The Lindeberg sums are stated with the *open* truncation set `{ε < |Xₙ,ᵢ|}`. Quantified
  over all `ε > 0` this is equivalent to the closed-set version, and it is the weaker
  hypothesis at each fixed `ε`.
* `lindeberg_clt_of_bounded` does not carry an `MemLp _ 2` hypothesis: a bounded
  measurable function on a probability space is automatically square-integrable, so
  demanding it would be laundering.
* In `weighted_iid_clt` the negligibility condition is written in `∀ ε > 0, ∀ᶠ n` form
  rather than as `Tendsto (fun n => ⨆ i, …) atTop (𝓝 0)`: for an empty row `Fin 0` a real
  `⨆` collapses to the junk value `0`, so the `iSup` spelling would silently weaken the
  hypothesis; the two agree on nonempty rows.

**Bibliographic comments.** The condition and the theorem are due to J. W. Lindeberg
("Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung,"
*Math. Z.* **15** (1922), 211–225); the triangular-array formulation and the converse
(necessity of the condition under uniform asymptotic negligibility) are due to W. Feller
("Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung," *Math. Z.* **40**
(1935), 521–559). The characteristic-function continuity theorem that closes the argument
is P. Lévy, *Calcul des probabilités*, Gauthier-Villars, 1925.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped Topology ENNReal NNReal

namespace StatLean.HypothesisTesting

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both bounds are elementary: the cubic half comes from integrating the exponential's remainder
three times, the quadratic half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality. Mathlib only provides the non-uniform `taylor_charFun_two`, so this is proved from
scratch here. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  -- `|exp (I u)| = 1`.
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  -- Derivative of `u ↦ I u`.
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  -- Continuity of the three integrands.
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  -- Derivative of `A₁ w = exp (I w) − 1 − I w`.
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  -- Derivative of `w ↦ w²/2` (written `w * w / 2`).
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  -- Derivative of `A₂ w = exp (I w) − 1 − I w + w²/2`.
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  -- `A₂ z` as an integral of `A₁ · I`.
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal (with `|y| = y`).
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  -- Reduce the goal to `A₂`.
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

-- H1: telescoping product bound.
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

-- H2: real quadratic remainder for `exp (-u)`.
private lemma abs_exp_neg_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp (-u) - (1 - u)| ≤ (3 / 4) * u ^ 2 := by
  have h := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, (-u) ^ m / (m.factorial : ℝ) = 1 - u := by
    simp [Finset.sum_range_succ]; ring
  rw [hs, abs_neg, sq_abs] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

-- H3: diagonal tendsto-to-zero.
private lemma tendsto_zero_of_eventually_le {F : ℕ → ℝ}
    (hF : ∀ᶠ n in atTop, 0 ≤ F n) (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, F n ≤ δ) :
    Tendsto F atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hF] with n hn using lt_of_lt_of_le hb hn
  · filter_upwards [h (b / 2) (by linarith)] with n hn using lt_of_le_of_lt hn (by linarith)

open Complex in
/-- **The analytic core of the Lindeberg CLT.** Under the Lindeberg hypotheses the product
of the row characteristic functions converges pointwise to the standard-normal
characteristic function `t ↦ exp(−t²/2)`. This is the content of Lindeberg's
swapping/telescoping estimate; `lindeberg_clt` merely feeds this pointwise statement through
Lévy's continuity theorem.

Lindeberg's swapping/telescoping estimate, assembled on top of the uniform remainder
bound `norm_cexp_sub_taylor_le`: telescope the two products, bound each factor's
difference by `E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]`, split at the level `ε` (the large part is
the Lindeberg sum killed by `hlin`), and match `∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²/2)`. -/
private lemma tendsto_prod_charFun_lindeberg
    {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) P)
    (hL2 : ∀ n i, MemLp (X n i) 2 P)
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => ∏ i, charFun (P.map (X n i)) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t)) := by
  -- The `t = 0` case is `∏ 1 → 1`; handle it first, then assume `t ≠ 0`.
  rcases eq_or_ne t 0 with rfl | ht
  · have hone : ∀ n i, charFun (P.map (X n i)) 0 = 1 := by
      intro n i
      haveI : IsProbabilityMeasure (P.map (X n i)) :=
        Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    have hR : charFun (gaussianReal 0 1) 0 = 1 := by
      rw [charFun_zero, probReal_univ, Complex.ofReal_one]
    simp only [hone, Finset.prod_const_one, hR]
    exact tendsto_const_nhds
  -- Basic facts about the row entries.
  have hvnn : ∀ n i, (0:ℝ) ≤ Var[X n i; P] := fun n i => variance_nonneg _ _
  have hunn : ∀ n i, (0:ℝ) ≤ t ^ 2 * Var[X n i; P] / 2 :=
    fun n i => div_nonneg (mul_nonneg (sq_nonneg t) (hvnn n i)) (by norm_num)
  have hI2 : ∀ n i, Integrable (fun ω => (X n i ω) ^ 2) P := fun n i => (hL2 n i).integrable_sq
  have hI1 : ∀ n i, Integrable (X n i) P := fun n i => (hL2 n i).integrable one_le_two
  have hVeq : ∀ n i, Var[X n i; P] = ∫ ω, (X n i ω) ^ 2 ∂P :=
    fun n i => variance_of_integral_eq_zero (hmeas n i).aemeasurable (hmean n i)
  -- The RHS constant as a genuine exponential.
  have hc : charFun (gaussianReal 0 1) t = Complex.exp (-(↑t ^ 2 / 2)) := by
    rw [charFun_gaussianReal]; push_cast; ring_nf
  -- Measurability of the truncation sets.
  have hset : ∀ ε n i, MeasurableSet {ω | ε < |X n i ω|} := fun ε n i =>
    measurableSet_lt measurable_const (hmeas n i).abs
  -- Nonnegativity of the Lindeberg terms.
  have hLnn : ∀ ε n i, 0 ≤ ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P :=
    fun ε n i => setIntegral_nonneg (hset ε n i) fun ω _ => sq_nonneg _
  -- CENTRAL per-term estimate (crux of the swapping argument).
  have hterm : ∀ ε : ℝ, 0 < ε → ∀ n i,
      ‖charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * Var[X n i; P]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
    intro ε hε n i
    have hsm := hset ε n i
    -- Integrability of the integrand pieces.
    have hIsecond : Integrable (fun ω => Complex.I * (↑(t * X n i ω) : ℂ)) P :=
      (((hI1 n i).const_mul t).ofReal).const_mul Complex.I
    have hIrp : Integrable (fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)) P :=
      ((integrable_const (1 : ℝ)).sub (((hI2 n i).const_mul (t ^ 2)).div_const 2)).ofReal
    have hItX2 : Integrable (fun ω => (t * X n i ω) ^ 2) P := by
      simpa [mul_pow] using (hI2 n i).const_mul (t ^ 2)
    have hIthird : Integrable (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) P := by
      have he : (fun ω => ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => (↑((t * X n i ω) ^ 2) : ℂ) / 2 := by ext ω; rw [← Complex.ofReal_pow]
      rw [he]; exact (hItX2.ofReal).div_const (2 : ℂ)
    have hFmeas : Measurable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp ((hmeas n i).const_mul t)).const_mul Complex.I)
    have hIF : Integrable (fun ω => Complex.exp (Complex.I * ↑(t * X n i ω))) P :=
      (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (by rw [Complex.norm_exp]; simp))
    have hIG : Integrable (fun ω => 1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) P :=
      ((integrable_const (1 : ℂ)).add hIsecond).sub hIthird
    -- `charFun = ∫ exp`.
    have hFcf : charFun (P.map (X n i)) t
        = ∫ ω, Complex.exp (Complex.I * ↑(t * X n i ω)) ∂P := by
      rw [charFun_apply_real, integral_map (hmeas n i).aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      congr 1; push_cast; ring
    -- The real (variance) part and the vanishing imaginary part.
    have hRp : ∫ ω, (1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) ∂P = 1 - t ^ 2 * Var[X n i; P] / 2 := by
      rw [integral_sub (integrable_const 1) (((hI2 n i).const_mul (t ^ 2)).div_const 2),
        integral_const, probReal_univ, smul_eq_mul, mul_one, integral_div]
      simp only [integral_const_mul]
      rw [← hVeq n i]
    have hTX : ∫ ω, t * X n i ω ∂P = 0 := by
      rw [integral_const_mul t (X n i), hmean n i, mul_zero]
    have hImC : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂P = 0 := by
      have key : ∫ ω, Complex.I * ((t * X n i ω : ℝ) : ℂ) ∂P
          = Complex.I * ∫ ω, ((t * X n i ω : ℝ) : ℂ) ∂P := integral_const_mul _ _
      rw [key, integral_complex_ofReal, hTX, Complex.ofReal_zero, mul_zero]
    -- `∫ G = 1 - t²σ²/2`.
    have hGint : ∫ ω, (1 + Complex.I * ↑(t * X n i ω)
        - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2) ∂P = ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ) := by
      have hEq : (fun ω => 1 + Complex.I * (↑(t * X n i ω) : ℂ) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)
          = fun ω => ((1 - t ^ 2 * (X n i ω) ^ 2 / 2 : ℝ) : ℂ)
              + Complex.I * ((t * X n i ω : ℝ) : ℂ) := by
        ext ω; push_cast; ring
      rw [hEq, integral_add hIrp hIsecond, integral_complex_ofReal, hRp, hImC, add_zero]
    -- Assemble the difference as one integral.
    have hab : charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)
        = ∫ ω, (Complex.exp (Complex.I * ↑(t * X n i ω))
            - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)) ∂P := by
      rw [integral_sub hIF hIG, ← hFcf, hGint]
    -- Pointwise remainder bound.
    set g : Ω → ℝ := fun ω => |t| ^ 3 * ε / 6 * (X n i ω) ^ 2
        + t ^ 2 * Set.indicator {ω | ε < |X n i ω|} (fun ω => (X n i ω) ^ 2) ω with hgdef
    have hbound : ∀ ω, ‖Complex.exp (Complex.I * ↑(t * X n i ω))
        - (1 + Complex.I * ↑(t * X n i ω) - ((↑(t * X n i ω) : ℂ)) ^ 2 / 2)‖ ≤ g ω := by
      intro ω
      refine (norm_cexp_sub_taylor_le (t * X n i ω)).trans ?_
      have hnn0 : (0:ℝ) ≤ |t| ^ 3 * ε / 6 * (X n i ω) ^ 2 :=
        mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) 3) hε.le) (by norm_num))
          (sq_nonneg _)
      by_cases hω : ε < |X n i ω|
      · have hωm : ω ∈ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_mem hωm]
        refine (min_le_right _ _).trans ?_
        have h2 : (t * X n i ω) ^ 2 = t ^ 2 * (X n i ω) ^ 2 := by ring
        rw [h2]; linarith [hnn0]
      · have hωm : ω ∉ {ω | ε < |X n i ω|} := hω
        simp only [hgdef, Set.indicator_of_notMem hωm, mul_zero, add_zero]
        refine (min_le_left _ _).trans ?_
        have habs : |t * X n i ω| ^ 3 = |t| ^ 3 * |X n i ω| ^ 3 := by rw [abs_mul, mul_pow]
        have hcube : |X n i ω| ^ 3 ≤ ε * (X n i ω) ^ 2 := by
          have he : |X n i ω| ^ 3 = |X n i ω| * (X n i ω) ^ 2 := by rw [← sq_abs]; ring
          rw [he]; exact mul_le_mul_of_nonneg_right (not_lt.1 hω) (sq_nonneg _)
        rw [habs]; nlinarith [hcube, pow_nonneg (abs_nonneg t) 3]
    have hbint : Integrable g P := by
      rw [hgdef]
      exact ((hI2 n i).const_mul _).add (((hI2 n i).indicator hsm).const_mul _)
    have hg_int : ∫ ω, g ω ∂P
        = |t| ^ 3 * ε / 6 * Var[X n i; P]
          + t ^ 2 * ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
      rw [hgdef, integral_add ((hI2 n i).const_mul _) (((hI2 n i).indicator hsm).const_mul _)]
      simp only [integral_const_mul, integral_indicator hsm]
      rw [← hVeq n i]
    rw [hab]
    exact (norm_integral_le_of_norm_le hbint (ae_of_all _ hbound)).trans (le_of_eq hg_int)
  -- Uniform asymptotic negligibility of the row variances.
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, Var[X n i; P] ≤ c := by
    intro c hc
    have hεpos : (0:ℝ) < Real.sqrt (c / 2) := Real.sqrt_pos.2 (by linarith)
    have hε2 : Real.sqrt (c / 2) ^ 2 = c / 2 := Real.sq_sqrt (by linarith)
    set ε := Real.sqrt (c / 2) with hεdef
    have hSlt : ∀ᶠ n in atTop,
        ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P ≤ c / 2 :=
      (hlin ε hεpos).eventually_le_const (show (0:ℝ) < c / 2 by linarith)
    filter_upwards [hSlt] with n hn i
    have hsm := hset ε n i
    have hdecomp : Var[X n i; P]
        = ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          + ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P := by
      rw [hVeq n i]; exact (integral_add_compl hsm (hI2 n i)).symm
    have hpart1 : ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P ≤ c / 2 :=
      le_trans (Finset.single_le_sum (fun j _ => hLnn ε n j) (Finset.mem_univ i)) hn
    have hpart2 : ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P ≤ c / 2 := by
      rw [← hε2]
      calc ∫ ω in {ω | ε < |X n i ω|}ᶜ, (X n i ω) ^ 2 ∂P
          ≤ ∫ ω in {ω | ε < |X n i ω|}ᶜ, ε ^ 2 ∂P := by
            refine setIntegral_mono_on ((hI2 n i).integrableOn) integrableOn_const hsm.compl
              (fun ω hω => ?_)
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
            rw [← sq_abs (X n i ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        _ ≤ ∫ _ω, ε ^ 2 ∂P :=
            setIntegral_le_integral (integrable_const _) (ae_of_all _ fun _ => by positivity)
        _ = ε ^ 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hdecomp]; linarith
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  -- Eventually every row term satisfies `uᵢ = t²σᵢ²/2 ≤ 1`.
  have hev1 : ∀ᶠ n in atTop, ∀ i, t ^ 2 * Var[X n i; P] / 2 ≤ 1 := by
    filter_upwards [hsmall (2 / t ^ 2) (by positivity)] with n hn i
    have hb := (le_div_iff₀ ht2).1 (hn i)
    have hcomm : t ^ 2 * Var[X n i; P] = Var[X n i; P] * t ^ 2 := mul_comm _ _
    linarith
  -- Abbreviations for the two products (`A` characteristic, `B` its quadratic surrogate).
  set A : ℕ → ℂ := fun n => ∏ i, charFun (P.map (X n i)) t with hA
  set B : ℕ → ℂ := fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ) with hB
  -- `∑ᵢ uᵢ → t²/2`.
  have hsum : Tendsto (fun n => ∑ i, t ^ 2 * Var[X n i; P] / 2) atTop (𝓝 (t ^ 2 / 2)) := by
    have h := hvar.const_mul (t ^ 2 / 2)
    have he : ∀ n, ∑ i, t ^ 2 * Var[X n i; P] / 2 = t ^ 2 / 2 * ∑ i, Var[X n i; P] := by
      intro n; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    simpa [he, mul_one] using h
  ------------------------------------------------------------------
  -- Claim G : `∑ᵢ uᵢ² → 0`.
  ------------------------------------------------------------------
  have hGsq : Tendsto (fun n => ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg _) (fun δ hδ => ?_)
    set M : ℝ := δ / (t ^ 2 / 2 + 2) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; exact div_pos hδ (by positivity)
    have hsmallM := hsmall (2 * M / t ^ 2) (div_pos (mul_pos (by norm_num) hMpos) ht2)
    have hsumlt : ∀ᶠ n in atTop, ∑ i, t ^ 2 * Var[X n i; P] / 2 < t ^ 2 / 2 + 1 :=
      hsum.eventually_lt_const (by linarith)
    filter_upwards [hsmallM, hsumlt] with n hnM hnsum
    have huM : ∀ i, t ^ 2 * Var[X n i; P] / 2 ≤ M := by
      intro i
      have hb := (le_div_iff₀ ht2).1 (hnM i)
      have hcomm : t ^ 2 * Var[X n i; P] = Var[X n i; P] * t ^ 2 := mul_comm _ _
      linarith
    calc ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2
        ≤ ∑ i, M * (t ^ 2 * Var[X n i; P] / 2) := by
          apply Finset.sum_le_sum; intro i _
          rw [sq]; exact mul_le_mul_of_nonneg_right (huM i) (hunn n i)
      _ = M * ∑ i, t ^ 2 * Var[X n i; P] / 2 := by rw [Finset.mul_sum]
      _ ≤ M * (t ^ 2 / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left hnsum.le hMpos.le
      _ ≤ δ := by
          rw [hMdef]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [hδ.le]
  ------------------------------------------------------------------
  -- T2 : `B n → charFun gaussian`.
  ------------------------------------------------------------------
  have T2 : Tendsto B atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
    rw [hc, hB]
    -- Reduce to a real product.
    have hLC : Complex.exp (-(↑t ^ 2 / 2)) = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have hBreal : (fun n => ∏ i, ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ))
        = fun n => ((∏ i, (1 - t ^ 2 * Var[X n i; P] / 2) : ℝ) : ℂ) := by
      ext n; rw [Complex.ofReal_prod]
    rw [hLC, hBreal]
    -- Now prove the real limit and lift by `ofReal`.
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    -- Real statement: `∏ (1 - uᵢ) → exp(-t²/2)`.
    have hprodexp : ∀ n, ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))
        = Real.exp (-(∑ i, t ^ 2 * Var[X n i; P] / 2)) := by
      intro n; rw [← Real.exp_sum]; rw [← Finset.sum_neg_distrib]
    have hEprod : Tendsto (fun n => ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      simp_rw [hprodexp]
      exact (Real.continuous_exp.tendsto _).comp hsum.neg
    have hdiff : Tendsto (fun n => (∏ i, (1 - t ^ 2 * Var[X n i; P] / 2))
        - ∏ i, Real.exp (-(t ^ 2 * Var[X n i; P] / 2))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
        (fun δ hδ => ?_)
      have hsqlt : ∀ᶠ n in atTop, (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2 < δ := by
        have hlim : Tendsto (fun n => (3 / 4) * ∑ i, (t ^ 2 * Var[X n i; P] / 2) ^ 2) atTop
            (𝓝 0) := by simpa using hGsq.const_mul (3 / 4)
        exact hlim.eventually_lt_const (by linarith)
      filter_upwards [hev1, hsqlt] with n hn1 hn2
      have htel := norm_prod_sub_prod_le (𝕜 := ℝ) Finset.univ
        (fun i => 1 - t ^ 2 * Var[X n i; P] / 2)
        (fun i => Real.exp (-(t ^ 2 * Var[X n i; P] / 2)))
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [hn1 i, hunn n i], by linarith [hunn n i]⟩)
        (fun i _ => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact (Real.exp_le_one_iff).2 (by linarith [hunn n i]))
      refine htel.trans (le_of_lt (lt_of_le_of_lt ?_ hn2))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h2 := abs_exp_neg_sub_one_sub_le (u := t ^ 2 * Var[X n i; P] / 2)
        (by rw [abs_le]; exact ⟨by linarith [hunn n i], hn1 i⟩)
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact h2
    have hRealP1 : Tendsto (fun n => ∏ i, (1 - t ^ 2 * Var[X n i; P] / 2)) atTop
        (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
      have := hdiff.add hEprod
      simpa using this
    exact hRealP1
  ------------------------------------------------------------------
  -- T1 : `A n - B n → 0`.
  ------------------------------------------------------------------
  have T1 : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (Eventually.of_forall fun n => norm_nonneg _)
      (fun δ hδ => ?_)
    set ε : ℝ := δ / (|t| ^ 3 + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by positivity)
    have hle : |t| ^ 3 * ε ≤ δ := by
      have h0 : (0:ℝ) < |t| ^ 3 + 1 := by positivity
      rw [hεdef, ← mul_div_assoc, div_le_iff₀ h0]; nlinarith [abs_nonneg t, hδ.le]
    have hVarlt : ∀ᶠ n in atTop, ∑ i, Var[X n i; P] ≤ 2 :=
      (hvar.eventually_lt_const (by norm_num : (1:ℝ) < 2)).mono fun n h => h.le
    have hLinlt : ∀ᶠ n in atTop,
        t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P < δ / 3 := by
      have hlim : Tendsto (fun n => t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P)
          atTop (𝓝 0) := by simpa using (hlin ε hεpos).const_mul (t ^ 2)
      exact hlim.eventually_lt_const (by linarith)
    filter_upwards [hev1, hVarlt, hLinlt] with n hn1 hn2 hn3
    -- telescoping
    have hpm : ∀ i, IsProbabilityMeasure (P.map (X n i)) := fun i =>
      Measure.isProbabilityMeasure_map (hmeas n i).aemeasurable
    have htel := norm_prod_sub_prod_le (𝕜 := ℂ) Finset.univ
      (fun i => charFun (P.map (X n i)) t)
      (fun i => ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ))
      (fun i _ => norm_charFun_le_one _)
      (fun i _ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hn1 i], by linarith [hunn n i]⟩)
    refine htel.trans ?_
    -- sum of per-term bounds
    have hsum2 : ∑ i, ‖charFun (P.map (X n i)) t - ((1 - t ^ 2 * Var[X n i; P] / 2 : ℝ) : ℂ)‖
        ≤ |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P]
          + t ^ 2 * ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hterm ε hεpos n i
    refine hsum2.trans ?_
    have hterm1 : |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P] ≤ δ / 3 := by
      have hnn : (0:ℝ) ≤ |t| ^ 3 * ε / 6 := by positivity
      calc |t| ^ 3 * ε / 6 * ∑ i, Var[X n i; P]
          ≤ |t| ^ 3 * ε / 6 * 2 := by apply mul_le_mul_of_nonneg_left hn2 hnn
        _ ≤ δ / 3 := by nlinarith [hle, hεpos.le, abs_nonneg t]
    linarith [hn3]
  ------------------------------------------------------------------
  -- Combine.
  ------------------------------------------------------------------
  have hcomb := T1.add T2
  simpa using hcomb

/-- **Lindeberg's central limit theorem for triangular arrays.**

For each `n` the row `(X n i)_{i < m n}` consists of independent, centered,
square-integrable random variables; the row variances converge to `1` and the Lindeberg
condition holds. Then the row sums converge in distribution to the standard normal law.

The row sizes `m n` are arbitrary (they need not tend to infinity, and rows are unrelated
across `n`). -/
theorem lindeberg_clt {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: entries inside a row are jointly independent (rows are unconstrained).
    (hindep : ∀ n, iIndepFun (X n) P)
    -- USER-INPUT: entries are square-integrable, so the row variances are finite.
    (hL2 : ∀ n i, MemLp (X n i) 2 P)
    -- USER-INPUT: entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    -- USER-INPUT: the row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    -- USER-INPUT: the Lindeberg condition.
    (hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0))
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z (fun _ => P) P' where
  forall_aemeasurable n :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hmeas n i).aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hZ.map_eq]
    have hcf : ∀ n, charFun (P.map (fun ω => ∑ i, X n i ω)) t
        = ∏ i, charFun (P.map (X n i)) t := fun n => by
      rw [iIndepFun.charFun_map_fun_sum_eq_prod (fun i => (hmeas n i).aemeasurable) (hindep n),
        Finset.prod_apply]
    simpa [hcf] using tendsto_prod_charFun_lindeberg hmeas hindep hL2 hmean hvar hlin t

/-- **Uniformly bounded rows.**

If the entries of the `n`-th row are bounded by a constant `c n` tending to `0`, the
Lindeberg condition is automatic (for `ε > 0` the truncation sets are eventually empty), so
the row sums are asymptotically standard normal as soon as the row variances converge
to `1`. This is the form used for randomization and permutation statistics, where the
summands are explicit bounded functions of the data.

No square-integrability hypothesis is needed: a bounded measurable function on a
probability space lies in `L²`. -/
theorem lindeberg_clt_of_bounded {m : ℕ → ℕ} {X : (n : ℕ) → Fin (m n) → Ω → ℝ}
    {c : ℕ → ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (X n i))
    -- USER-INPUT: entries inside a row are jointly independent.
    (hindep : ∀ n, iIndepFun (X n) P)
    -- USER-INPUT: entries are centered.
    (hmean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    -- USER-INPUT: the row variances add up to 1 in the limit (normalisation).
    (hvar : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1))
    -- USER-INPUT: the `n`-th row is bounded by `c n`.
    (hbdd : ∀ n i ω, |X n i ω| ≤ c n)
    -- USER-INPUT: the bounds are asymptotically negligible.
    (hc : Tendsto c atTop (𝓝 0))
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z (fun _ => P) P' := by
  -- Bounded measurable ⇒ `L²`.
  have hL2 : ∀ n i, MemLp (X n i) 2 P := fun n i =>
    MemLp.of_bound (hmeas n i).aestronglyMeasurable (c n)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbdd n i ω)
  -- Lindeberg condition: for `ε > 0` the truncation sets are eventually empty (`c n < ε`).
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro ε hε
    have key : ∀ᶠ n in atTop,
        (∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) = 0 := by
      filter_upwards [hc.eventually (eventually_lt_nhds hε)] with n hn
      refine Finset.sum_eq_zero fun i _ => ?_
      have hempty : {ω | ε < |X n i ω|} = (∅ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact le_trans (hbdd n i ω) hn.le
      rw [hempty]; simp
    exact tendsto_const_nhds.congr' (key.mono fun n hn => hn.symm)
  exact lindeberg_clt hmeas hindep hL2 hmean hvar hlin hZ

/-- **Central limit theorem for weighted sums of an i.i.d. sequence.**

Let `Y₀, Y₁, …` be i.i.d. with mean `0` and variance `σ² > 0`, and let `wₙ,ᵢ` be triangular
weights whose squares are individually negligible relative to their sum,
`maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`. Then
$$\frac{\sum_i w_{n,i} Y_i}{\sigma\,\bigl(\sum_i w_{n,i}^2\bigr)^{1/2}}
  \;\rightsquigarrow\; N(0,1).$$

This is `lindeberg_clt` applied to the row `Xₙ,ᵢ := wₙ,ᵢ Yᵢ / (σ (∑ⱼ wₙ,ⱼ²)^{1/2})`, whose
variances sum to `1` exactly and whose Lindeberg sums are controlled by the negligibility
condition together with the single square-integrable law of `Y₀`.

The negligibility hypothesis is spelled `∀ ε > 0, ∀ᶠ n, ∀ i, wₙ,ᵢ² ≤ ε ∑ⱼ wₙ,ⱼ²` — the
`iSup`-free form of `maxᵢ wₙ,ᵢ² / ∑ⱼ wₙ,ⱼ² → 0`. -/
theorem weighted_iid_clt {m : ℕ → ℕ} {Y : ℕ → Ω → ℝ} {w : (n : ℕ) → Fin (m n) → ℝ}
    {σ : ℝ} {Z : Ω' → ℝ}
    -- USER-INPUT: the sampled variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (Y i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun Y P)
    -- USER-INPUT: the sample is identically distributed.
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    -- USER-INPUT: square-integrable sampling law.
    (hL2 : MemLp (Y 0) 2 P)
    -- USER-INPUT: the sampling law is centered.
    (hmean : ∫ ω, Y 0 ω ∂P = 0)
    -- USER-INPUT: the scale parameter is positive (nondegenerate sampling law).
    (hσ : 0 < σ)
    -- USER-INPUT: the sampling variance is `σ²`.
    (hvar : Var[Y 0; P] = σ ^ 2)
    -- USER-INPUT: the `n`-th row of weights is not identically zero.
    (hw : ∀ n, 0 < ∑ i, (w n i) ^ 2)
    -- USER-INPUT: individual weights are asymptotically negligible.
    (hneg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, (w n i) ^ 2 ≤ ε * ∑ j, (w n j) ^ 2)
    -- USER-INPUT: `Z` realises the standard normal law on the limit space.
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution
      (fun n ω => (σ * Real.sqrt (∑ i, (w n i) ^ 2))⁻¹ * ∑ i, w n i * Y (i : ℕ) ω)
      atTop Z (fun _ => P) P' := by
  -- Abbreviations for the weight-square sum `S n`, the normalising scale `s n = σ √(S n)`,
  -- and the normalised row `X n i = (s n)⁻¹ · wₙ,ᵢ · Yᵢ`.
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℝ, S = fun n => ∑ i, (w n i) ^ 2 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ, s = fun n => σ * Real.sqrt (S n) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : (n : ℕ) → Fin (m n) → Ω → ℝ,
      X = fun n i ω => (s n)⁻¹ * w n i * Y (i : ℕ) ω := ⟨_, rfl⟩
  have hσ2 : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hSpos : ∀ n, 0 < S n := by intro n; rw [hSdef]; exact hw n
  have hspos : ∀ n, 0 < s n := by
    intro n; simp only [hsdef]; exact mul_pos hσ (Real.sqrt_pos.2 (hSpos n))
  have hsn2 : ∀ n, (s n) ^ 2 = σ ^ 2 * ∑ i, (w n i) ^ 2 := by
    intro n; simp only [hsdef, hSdef]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  -- The normalised weight squares sum to `1/σ²` on every row.
  have hasum : ∀ n, ∑ i, ((s n)⁻¹ * w n i) ^ 2 = (σ ^ 2)⁻¹ := by
    intro n
    have e : ∑ i, ((s n)⁻¹ * w n i) ^ 2 = (∑ i, (w n i) ^ 2) * ((s n) ^ 2)⁻¹ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, inv_pow, mul_comm]
    rw [e, hsn2 n, mul_inv, mul_comm ((σ ^ 2)⁻¹) ((∑ i, (w n i) ^ 2)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (hw n)), one_mul]
  -- Row regularity: measurable, `L²`, centered, independent.
  have hmeas' : ∀ n i, Measurable (X n i) := by
    intro n i; simp only [hXdef]; exact (hmeas ↑i).const_mul _
  have hL2' : ∀ n i, MemLp (X n i) 2 P := by
    intro n i; simp only [hXdef]; exact ((hident ↑i).symm.memLp_snd hL2).const_mul _
  have hmean' : ∀ n i, ∫ ω, X n i ω ∂P = 0 := by
    intro n i; simp only [hXdef]
    rw [integral_const_mul, ((hident ↑i).integral_eq).trans hmean, mul_zero]
  have hindep' : ∀ n, iIndepFun (X n) P := by
    intro n
    have h1 : iIndepFun (fun i : Fin (m n) => Y (↑i : ℕ)) P :=
      iIndepFun.precomp Fin.val_injective hindep
    have h2 := h1.comp (fun i : Fin (m n) => fun y : ℝ => (s n)⁻¹ * w n i * y)
      (fun i => measurable_id.const_mul _)
    refine (iIndepFun_congr (fun i => ?_)).2 h2
    filter_upwards with ω; simp only [hXdef, Function.comp]
  -- Row variances sum to `1`, hence trivially tend to `1`.
  have hvarval : ∀ n, ∑ i, Var[X n i; P] = 1 := by
    intro n
    have hVi : ∀ i, Var[X n i; P] = ((s n)⁻¹ * w n i) ^ 2 * σ ^ 2 := by
      intro i; simp only [hXdef]
      rw [variance_const_mul, (hident ↑i).variance_eq, hvar]
    simp_rw [hVi]
    rw [← Finset.sum_mul, hasum n, inv_mul_cancel₀ (ne_of_gt hσ2)]
  have hvar' : Tendsto (fun n => ∑ i, Var[X n i; P]) atTop (𝓝 1) := by
    have hcongr : (fun n => ∑ i, Var[X n i; P]) = fun _ => (1 : ℝ) := funext hvarval
    rw [hcongr]; exact tendsto_const_nhds
  -- The `L²`-tail of the sampling law vanishes: `∫_{K < |Y₀|} Y₀² → 0` as `K → ∞`.
  have hsq0 : Integrable (fun ω => (Y 0 ω) ^ 2) P := hL2.integrable_sq
  obtain ⟨tail, htaildef⟩ : ∃ tail : ℕ → ℝ,
      tail = fun (K : ℕ) => ∫ ω in {ω | (K : ℝ) < |Y 0 ω|}, (Y 0 ω) ^ 2 ∂P := ⟨_, rfl⟩
  have htail0 : Tendsto tail atTop (𝓝 0) := by
    simp only [htaildef]
    have hsm : ∀ K : ℕ, MeasurableSet {ω | (K : ℝ) < |Y 0 ω|} := fun K =>
      measurableSet_lt measurable_const (hmeas 0).abs
    have hanti : Antitone fun K : ℕ => {ω | (K : ℝ) < |Y 0 ω|} := by
      intro a b hab ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hab) hω
    have hint : ∃ K : ℕ, IntegrableOn (fun ω => (Y 0 ω) ^ 2) {ω | (K : ℝ) < |Y 0 ω|} P :=
      ⟨0, hsq0.integrableOn⟩
    have hlim := tendsto_setIntegral_of_antitone hsm hanti hint
    have hempty : ⋂ K : ℕ, {ω | (K : ℝ) < |Y 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      obtain ⟨K, hK⟩ := exists_nat_gt |Y 0 ω|
      exact ⟨K, hK.le⟩
    rw [hempty] at hlim
    simpa using hlim
  -- Identically-distributed rows share the same tail integral.
  have htaileq : ∀ (i K : ℕ),
      ∫ ω in {ω | (K : ℝ) < |Y i ω|}, (Y i ω) ^ 2 ∂P = tail K := by
    intro i K
    have hset : ∀ j : ℕ, MeasurableSet {ω | (K : ℝ) < |Y j ω|} := fun j =>
      measurableSet_lt measurable_const (hmeas j).abs
    have hg : Measurable fun y : ℝ => if (K : ℝ) < |y| then y ^ 2 else 0 :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
        (measurable_id.pow_const 2) measurable_const
    have hcomp : ∀ j : ℕ, ∫ ω, (if (K : ℝ) < |Y j ω| then (Y j ω) ^ 2 else 0) ∂P
        = ∫ ω in {ω | (K : ℝ) < |Y j ω|}, (Y j ω) ^ 2 ∂P := by
      intro j
      rw [← integral_indicator (hset j)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : (K : ℝ) < |Y j ω| <;> simp [Set.indicator, h]
    simp only [htaildef]
    rw [← hcomp i, ← hcomp 0]
    simpa [Function.comp] using ((hident i).comp hg).integral_eq
  -- Lindeberg's condition for the normalised row, from weight negligibility.
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · -- Each Lindeberg sum is nonnegative.
      refine Eventually.of_forall fun n => hb.trans_le (Finset.sum_nonneg fun i _ => ?_)
      exact setIntegral_nonneg (measurableSet_lt measurable_const (hmeas' n i).abs)
        fun ω _ => sq_nonneg _
    · -- Upper bound: pick a tail level `K` making `tail K < σ² b`, then use negligibility.
      obtain ⟨K, hKtail, hK1⟩ :=
        (((tendsto_order.1 htail0).2 (σ ^ 2 * b) (mul_pos hσ2 hb)).and
          (eventually_ge_atTop 1)).exists
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      filter_upwards [hneg (σ ^ 2 * (ε / K) ^ 2) (by positivity)] with n hn
      -- Uniform bound on the normalised weights from negligibility.
      have haik : ∀ i, |(s n)⁻¹ * w n i| ≤ ε / K := by
        intro i
        have hsq : ((s n)⁻¹ * w n i) ^ 2 ≤ (ε / K) ^ 2 := by
          have e1 : ((s n)⁻¹ * w n i) ^ 2 = (w n i) ^ 2 / (s n) ^ 2 := by
            rw [mul_pow, inv_pow]; ring
          rw [e1, hsn2 n, div_le_iff₀ (mul_pos hσ2 (hw n))]
          calc (w n i) ^ 2 ≤ σ ^ 2 * (ε / K) ^ 2 * ∑ i, (w n i) ^ 2 := hn i
            _ = (ε / K) ^ 2 * (σ ^ 2 * ∑ i, (w n i) ^ 2) := by ring
        calc |(s n)⁻¹ * w n i| = Real.sqrt (((s n)⁻¹ * w n i) ^ 2) :=
              (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((ε / K) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = ε / K := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      -- Per-entry bound of the truncated second moment by the shared tail.
      have hterm : ∀ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          ≤ ((s n)⁻¹ * w n i) ^ 2 * tail K := by
        intro i
        have hXsq : ∀ ω, (X n i ω) ^ 2 = ((s n)⁻¹ * w n i) ^ 2 * (Y (↑i : ℕ) ω) ^ 2 := by
          intro ω; simp only [hXdef]; rw [mul_pow]
        rw [setIntegral_congr_fun (measurableSet_lt measurable_const (hmeas' n i).abs)
              (fun ω _ => hXsq ω), integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← htaileq (↑i) K]
        refine setIntegral_mono_set (((hident ↑i).symm.memLp_snd hL2).integrable_sq).integrableOn
          (Eventually.of_forall fun ω => sq_nonneg _) (Eventually.of_forall fun ω hω => ?_)
        -- `{ε < |X n i|} ⊆ {K < |Y i|}`.
        have h1 : ε < |(s n)⁻¹ * w n i| * |Y (↑i : ℕ) ω| := by
          rw [← abs_mul]; simpa only [hXdef] using hω
        have h3 : ε < (ε / K) * |Y (↑i : ℕ) ω| :=
          lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right (haik i) (abs_nonneg _))
        show (K : ℝ) < |Y (↑i : ℕ) ω|
        by_contra hcon
        push_neg at hcon
        have hle : (ε / K) * |Y (↑i : ℕ) ω| ≤ (ε / K) * K :=
          mul_le_mul_of_nonneg_left hcon (by positivity)
        rw [div_mul_cancel₀ ε (ne_of_gt hKpos)] at hle
        exact absurd (lt_of_lt_of_le h3 hle) (lt_irrefl ε)
      -- Sum the per-entry bounds and conclude.
      calc ∑ i, ∫ ω in {ω | ε < |X n i ω|}, (X n i ω) ^ 2 ∂P
          ≤ ∑ i, ((s n)⁻¹ * w n i) ^ 2 * tail K := Finset.sum_le_sum fun i _ => hterm i
        _ = (σ ^ 2)⁻¹ * tail K := by rw [← Finset.sum_mul, hasum n]
        _ < b := by
            have hlt : (σ ^ 2)⁻¹ * tail K < (σ ^ 2)⁻¹ * (σ ^ 2 * b) :=
              mul_lt_mul_of_pos_left hKtail (inv_pos.2 hσ2)
            rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hσ2), one_mul] at hlt
  -- Assemble: rewrite the target row sum and apply the triangular-array CLT.
  have hgoaleq : (fun n ω => (σ * Real.sqrt (∑ i, (w n i) ^ 2))⁻¹ * ∑ i, w n i * Y (↑i : ℕ) ω)
      = fun n ω => ∑ i, X n i ω := by
    funext n ω
    simp only [hXdef, hsdef, hSdef]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hgoaleq]
  exact lindeberg_clt hmeas' hindep' hL2' hmean' hvar' hlin hZ

/-- **Weak law of large numbers for a triangular array** (first-absolute-moment form).

Let the `n`-th row `Yₙ,₀, …, Yₙ,ₙ₋₁` consist of independent variables with common law `Gₙ`.
If `Gₙ` converges weakly to `ν` and the first absolute moments converge,
`∫ |y| dGₙ → ∫ |y| dν < ∞`, then the row averages converge in probability to the limiting
mean:
$$\bar Y_n = n^{-1}\sum_{i<n} Y_{n,i} \;\xrightarrow{\;P\;}\; \int y \,\mathrm d\nu .$$

Weak convergence of the row laws alone is *not* enough (mass can escape to infinity); the
convergence of first absolute moments is exactly the uniform-integrability substitute that
makes the truncation argument work, and it is what the bootstrap applications can verify.

Convergence of the row laws is stated on `ProbabilityMeasure ℝ`, since the rows carry no
common random-variable representation.

## ⚠ THIS STATEMENT IS **FALSE** AS FROZEN (verified counterexample below)

The hypothesis `hL1` is stated with the **Bochner** integral `∫ y, |y| ∂(G n)`, which is the
junk value `0` whenever `|·|` is *not* `G n`-integrable (`MeasureTheory.integral_undef`).
Consequently `hL1` says nothing at all about rows with an infinite first absolute moment: it
is satisfied *vacuously* by any sequence of non-integrable `Gₙ` as soon as the limit has
`∫|y| dν = 0`. That loophole destroys the conclusion.

**Counterexample.** Let `μₙ` be any probability measure supported in `[n³, ∞)` with
`∫ |y| dμₙ = ∞` (e.g. the law of `n³ / U` with `U` uniform on `(0,1)`, a Pareto law of index
`1`), and put
`Gₙ = (1 − 1/n) · δ₀ + (1/n) · μₙ`, `ν = δ₀`.
All hypotheses hold:

* `IsProbabilityMeasure (Gₙ)`, `IsProbabilityMeasure ν`;
* `hweak`: for bounded continuous `f`, `∫ f dGₙ = (1 − 1/n) f(0) + (1/n) ∫ f dμₙ → f(0)`,
  since `|∫ f dμₙ| ≤ ‖f‖∞`; so `Gₙ ⇒ δ₀ = ν`;
* `hL1`: `|·|` is not `Gₙ`-integrable (`(1/n) ∫|y| dμₙ = ∞`), so the Bochner integral takes
  its junk value: `∫ |y| dGₙ = 0` for every `n`, and `∫ |y| dν = 0`. The sequence is
  constantly `0` and converges to `0`;
* `hν`: `Integrable id δ₀`, and `∫ y dν = 0`.

But the conclusion fails. Let `Nₙ` be the number of row entries that are nonzero; `Nₙ` is
`Binomial(n, 1/n)`, so `P(Nₙ ≥ 1) = 1 − (1 − 1/n)ⁿ → 1 − e⁻¹ ≈ 0.632`. On `{Nₙ ≥ 1}` every
nonzero entry is `≥ n³`, hence
`n⁻¹ ∑_{i<n} Yₙ,ᵢ ≥ n⁻¹ · n³ = n² ≥ 1`,
so `P{ω | 1 ≤ |n⁻¹ ∑ᵢ Yₙ,ᵢ − 0|} ≥ 1 − (1 − 1/n)ⁿ ↛ 0`: `TendstoInMeasure` fails at `ε = 1`.

(The proof note that used to sit in the body asserted the opposite — that a heavy-tailed
`Gₙ = (1−1/n)δ₀ + (1/n)·Cauchy` still concentrates. That happens to be true for the *fixed*
Cauchy tail, because `n⁻¹ × O_P(1)` many Cauchy draws is `O_P(1/n)`; it is not true once the
escaping mass is placed at height `n³`, which the hypotheses permit.)

**Forced repair.** Add the integrability of the rows, i.e. the hypothesis
`(hGint : ∀ n, Integrable id (G n))`
(or restate `hL1` with the lower Lebesgue integral `∫⁻ y, ‖y‖₊ ∂(G n)` in `ℝ≥0∞`). With it,
`hweak` + `hL1` do give uniform integrability of `{Gₙ}` and the classical Feller truncation
argument sketched below goes through. That repaired statement is *not* proved here: it is a
self-contained project (uniform integrability from weak convergence plus convergence of first
absolute moments, then an `n`-dependent truncation), and no consumer in the repository
currently discharges it (`Bootstrap/Consistency.lean` and `LikelihoodMethods/UniformLAN.lean`
only reference it as an open brick). The statement is therefore left exactly as frozen, with
the falsity recorded, rather than silently strengthened. -/
theorem triangular_wlln_of_L1 {Y : (n : ℕ) → Fin n → Ω → ℝ} {G : ℕ → Measure ℝ}
    {ν : Measure ℝ} [∀ n, IsProbabilityMeasure (G n)] [IsProbabilityMeasure ν]
    -- USER-INPUT: every array entry is measurable (data regularity).
    (hmeas : ∀ n i, Measurable (Y n i))
    -- USER-INPUT: entries inside a row are jointly independent.
    (hindep : ∀ n, iIndepFun (Y n) P)
    -- USER-INPUT: the `n`-th row is identically distributed with law `G n`.
    (hlaw : ∀ n (i : Fin n), P.map (Y n i) = G n)
    -- USER-INPUT: the row laws converge weakly to `ν` (portmanteau form: integration against
    -- bounded continuous test functions; matches the convention used elsewhere in the library).
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ y, f y ∂(G n)) atTop (𝓝 (∫ y, f y ∂ν)))
    -- USER-INPUT: the limit law has a finite first moment.
    (hν : Integrable id ν)
    -- USER-INPUT: the first absolute moments converge.
    (hL1 : Tendsto (fun n => ∫ y, |y| ∂(G n)) atTop (𝓝 (∫ y, |y| ∂ν))) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i, Y n i ω) atTop
      (fun _ => ∫ y, y ∂ν) := by
  -- FALSE AS STATED: see the docstring for the counterexample
  -- `Gₙ = (1−1/n)δ₀ + (1/n)·Pareto([n³,∞))`, `ν = δ₀`, which satisfies every hypothesis
  -- (`hL1` only because `∫ y, |y| ∂(G n)` is the junk value `0` for non-integrable `Gₙ`)
  -- while the row averages are `≥ n²` with probability `→ 1 − e⁻¹`.  The proof sketch that
  -- follows is the argument for the REPAIRED statement (add `∀ n, Integrable id (G n)`).
  --
  -- TODO (planned debt, repaired form): the faithful proof is the classical Feller weak law via
  -- truncation at an `n`-dependent level `Cₙ = n`.  Split each row entry
  -- `Y n i = U n i + V n i` with `U n i := Y n i · 1{|Y n i| ≤ n}` and control the
  -- three resulting terms of `n⁻¹∑ Y n i − ∫ y dν`:
  --   • centered truncated part `n⁻¹∑ (U n i − 𝔼[U n i])` by Chebyshev, using
  --     `Var[n⁻¹∑ U] ≤ 𝔼[U₀²]/n` and `n⁻¹∫_{|y|≤n} y² dGₙ → 0`
  --     (from `n⁻¹∫_{|y|≤K} y² → 0` plus the uniform tail `∫_{|y|>K}|y| dGₙ`);
  --   • centering shift `𝔼[U n i] − ∫ y dν = ∫_{|y|≤n} y dGₙ − ∫ y dν → 0`, from
  --     weak convergence (`hweak`) together with `L¹` convergence of first moments
  --     (`hL1`), which give `∫ y dGₙ → ∫ y dν` and vanishing truncation error;
  --   • tail part `V n i` by the union bound `n · Gₙ{|y| > n} ≤ ∫_{|y|>n}|y| dGₙ → 0`.
  -- The single nontrivial analytic input is the **uniform integrability** of `{Gₙ}`
  -- (`∀ ε, ∃ K, ∀ n, ∫_{|y|>K}|y| dGₙ < ε`), which is a standard consequence of `hL1` +
  -- `hweak` ONLY in the repaired form, i.e. once `∀ n, Integrable id (G n)` is assumed:
  -- without it `hL1` carries no information (junk value) and the statement is false.
  -- Either way the proof is a self-contained project, not a corollary of `lindeberg_clt`.
  sorry

end StatLean.HypothesisTesting
