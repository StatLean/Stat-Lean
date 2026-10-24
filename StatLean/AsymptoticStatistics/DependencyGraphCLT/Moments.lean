/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import StatLean.AsymptoticStatistics.ForMathlib.Probability.CumulantCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Janson's Lemma 1: the semiinvariant form of the method of moments

Let $(X_n)$ be real random variables with finite moments of every order. Janson's Lemma 1 says
that if $\kappa_j(X_n) \to c_j$ for every $j \ge 1$, then there is a random variable $X$ with
$\kappa_j(X) = c_j$ for all $j$, and if these values determine the law of $X$, then
$X_n \to X$ in distribution, with convergence of all moments. This file formalizes the lemma
for laws on $\mathbb{R}$ (bundled as `ProbabilityMeasure ℝ`), together with its moment form
and the Gaussian case used by Theorem 1.

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312,
Lemma 1.

**Proof formalization notes.** Convergent moments are uniformly bounded, and a uniform bound on
second moments makes the laws tight by Chebyshev's inequality
(`Janson.isTightMeasureSet_of_moment_bound`); Prokhorov's theorem then extracts a weakly
convergent subsequence. Absolute-moment bounds pass to the weak limit by the portmanteau
theorem, and moments converge along it by the truncation bound
$$ |x^j - \operatorname{clamp}_R(x)^j| \;\le\; \tfrac{2}{R}\,|x|^{j+1}, $$
which requires one extra moment, applied to the bounded continuous test function
$x \mapsto \operatorname{clamp}_R(x)^j$ (`Janson.truncPow`). Janson's polynomial $p_j$ expressing
the $j$-th moment through $\kappa_1, \dots, \kappa_j$ is `Janson.momentOf`, defined by the
moment–cumulant recursion `Cumulant.moment_recursion`. Every moment of every law in the sequence
is assumed finite (`hint : ∀ n p, …`).

## Main results

* `Janson.exists_limit_of_tendsto_moments`: a subsequence and a limit law with the limiting
  moments (tightness and Prokhorov).
* `Janson.tendsto_of_tendsto_moments`: convergence of the whole sequence under determinacy.
* `Janson.momentOf`, `Janson.tendsto_integral_pow_of_tendsto_cumulant`: Janson's `p_j`, given by
  the moment–cumulant recursion, and convergence of moments from convergence of semiinvariants.
* `Janson.exists_measure_cumulant_eq`: the existence half in semiinvariant form.
* `Janson.tendsto_gaussPM_of_tendsto_cumulant`: the Gaussian case.
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.AsymptoticStatistics.Janson

/-! ### The clamp, and the truncated power as a bounded continuous function -/

section Trunc

/-- `x` clamped to the window `[-R, R]`. -/
noncomputable def clamp (R x : ℝ) : ℝ := max (-R) (min R x)

lemma continuous_clamp (R : ℝ) : Continuous (clamp R) := by
  unfold clamp
  fun_prop

lemma abs_clamp_le (R x : ℝ) : |clamp R x| ≤ |R| := by
  rw [abs_le]
  constructor
  · exact le_trans (neg_le_neg (le_abs_self R)) (le_max_left _ _)
  · exact max_le (neg_le_abs R) ((min_le_left R x).trans (le_abs_self R))

lemma clamp_eq_self {R x : ℝ} (h : |x| ≤ R) : clamp R x = x := by
  rw [abs_le] at h
  rw [clamp, min_eq_right h.2, max_eq_right h.1]

/-- The truncated power `x ↦ (clamp R x) ^ j`, as a bounded continuous function. -/
noncomputable def truncPow (j : ℕ) (R : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clamp R x ^ j)
    ((continuous_clamp R).pow j) (|R| ^ j) (fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le R x) j)

@[simp]
lemma truncPow_apply (j : ℕ) (R x : ℝ) : truncPow j R x = clamp R x ^ j := rfl

/-- The truncation error at order `j` is controlled by one extra moment, uniformly in the
law. -/
theorem abs_sub_clamp_pow_le {R : ℝ} (hR : 0 < R) (j : ℕ) (x : ℝ) :
    |x ^ j - clamp R x ^ j| ≤ 2 / R * |x| ^ (j + 1) := by
  rcases le_or_gt |x| R with h | h
  · rw [clamp_eq_self h, sub_self, abs_zero]
    positivity
  · have hcl : |clamp R x| ≤ R := by
      have := abs_clamp_le R x
      rwa [abs_of_pos hR] at this
    have htri : |x ^ j - clamp R x ^ j| ≤ |x| ^ j + |clamp R x| ^ j := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_pow, abs_pow]
    have h2 : |clamp R x| ^ j ≤ |x| ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (hcl.trans h.le) j
    have h3 : |x| ^ j + |clamp R x| ^ j ≤ 2 * |x| ^ j := by linarith
    have h4 : 2 * |x| ^ j ≤ 2 / R * |x| ^ (j + 1) := by
      rw [pow_succ, div_mul_eq_mul_div, le_div_iff₀ hR]
      have hx : (0 : ℝ) ≤ |x| ^ j := pow_nonneg (abs_nonneg _) j
      nlinarith [hx, h.le]
    linarith

end Trunc

/-! ### Absolute moments, and uniform bounds from a convergent moment sequence -/

section Bounds

lemma integrable_abs_pow {ρ : Measure ℝ} {p : ℕ} (h : Integrable (fun x : ℝ => x ^ p) ρ) :
    Integrable (fun x : ℝ => |x| ^ p) ρ := by
  simpa [abs_pow] using h.abs

lemma abs_pow_le_one_add {p : ℕ} (x : ℝ) : |x| ^ p ≤ 1 + x ^ (2 * p) := by
  have hx2 : x ^ (2 * p) = |x| ^ (2 * p) := by
    rw [pow_mul, pow_mul, sq_abs]
  have hnn : (0 : ℝ) ≤ |x| ^ (2 * p) := by positivity
  rcases le_or_gt |x| 1 with h | h
  · have h1 : |x| ^ p ≤ 1 := pow_le_one₀ (abs_nonneg _) h
    rw [hx2]
    linarith
  · rw [hx2]
    have : |x| ^ p ≤ |x| ^ (2 * p) := pow_le_pow_right₀ h.le (by omega)
    linarith

/-- The absolute moments are uniformly bounded as soon as every ordinary moment converges,
since `|x| ^ p ≤ 1 + x ^ {2 p}` and a convergent real sequence is bounded. -/
theorem exists_abs_moment_bound {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {α : ℕ → ℝ}
    (hconv : ∀ p, Tendsto (fun n => ∫ x, x ^ p ∂(P n : Measure ℝ)) atTop (𝓝 (α p)))
    (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ C := by
  obtain ⟨B, hB⟩ := (hconv (2 * p)).bddAbove_range
  refine ⟨max 0 (1 + B), le_max_left _ _, fun n => ?_⟩
  have hle : ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ ∫ x, (1 + x ^ (2 * p)) ∂(P n : Measure ℝ) := by
    refine integral_mono (integrable_abs_pow (hint n p))
      ((integrable_const 1).add (hint n (2 * p))) ?_
    intro x
    exact abs_pow_le_one_add x
  have hsplit : ∫ x, (1 + x ^ (2 * p)) ∂(P n : Measure ℝ)
      = 1 + ∫ x, x ^ (2 * p) ∂(P n : Measure ℝ) := by
    rw [integral_add (integrable_const 1) (hint n (2 * p)), integral_const]
    simp
  have hBn : ∫ x, x ^ (2 * p) ∂(P n : Measure ℝ) ≤ B := hB ⟨n, rfl⟩
  calc ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ 1 + ∫ x, x ^ (2 * p) ∂(P n : Measure ℝ) := by
        rw [← hsplit]; exact hle
    _ ≤ 1 + B := by linarith
    _ ≤ max 0 (1 + B) := le_max_right _ _

end Bounds

/-! ### Tightness -/

section Tight

/-- By Chebyshev's inequality, a uniform second-moment bound makes a family of laws on `ℝ` tight. -/
theorem isTightMeasureSet_of_moment_bound {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n, Integrable (fun x : ℝ => x ^ 2) (P n : Measure ℝ))
    {C : ℝ} (hC : ∀ n, ∫ x, x ^ 2 ∂(P n : Measure ℝ) ≤ C) :
    IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C / r ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => C / r ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (two_ne_zero))
    simpa using ENNReal.tendsto_ofReal h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  refine iSup₂_le ?_
  rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
  -- Chebyshev for the `n`-th law
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (P n : Measure ℝ) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).aemeasurable
  have hsub : {x : ℝ | r < ‖x‖} ⊆ {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hx ⊢
    refine ENNReal.ofReal_le_ofReal ?_
    have : r ^ 2 ≤ |x| ^ 2 := by nlinarith [hr, hx]
    rwa [sq_abs] at this
  have hne : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hmark := meas_ge_le_lintegral_div hmeas hne ENNReal.ofReal_ne_top
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(P n : Measure ℝ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hC n)
  calc (P n : Measure ℝ) {x : ℝ | r < ‖x‖}
      ≤ (P n : Measure ℝ) {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (x ^ 2)} :=
        measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(P n : Measure ℝ)) / ENNReal.ofReal (r ^ 2) := hmark
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (r ^ 2) := by gcongr
    _ = ENNReal.ofReal (C / r ^ 2) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < r ^ 2)]

end Tight

/-! ### Moments pass to a weak limit

The uniform absolute-moment bound is inherited by the weak limit through the portmanteau
inequality for nonnegative continuous functions. The convergence of moments follows from
`Janson.truncPow` being a bounded continuous test function and `Janson.abs_sub_clamp_pow_le`.
-/

section Transfer

variable {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}

/-- The uniform absolute-moment bound is inherited by the weak limit, by the portmanteau
inequality for the nonnegative continuous function `x ↦ |x| ^ p`. -/
theorem lintegral_abs_pow_le_of_tendsto (hPQ : Tendsto P atTop (𝓝 Q)) {p : ℕ} {C : ℝ}
    (hint : ∀ n, Integrable (fun x : ℝ => |x| ^ p) (P n : Measure ℝ))
    (hC : ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂(Q : Measure ℝ) ≤ ENNReal.ofReal C := by
  refine (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μs := fun n => (P n : Measure ℝ)) (f := fun x : ℝ => |x| ^ p) (by fun_prop)
    (fun x => pow_nonneg (abs_nonneg x) p)
    fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hPQ hG).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
    (Eventually.of_forall fun x => pow_nonneg (abs_nonneg x) p)]
  exact ENNReal.ofReal_le_ofReal (hC n)

/-- If the absolute `p`-th moments of `P n` are bounded by `C`, then `x ^ p` is integrable under
the weak limit. -/
theorem integrable_pow_of_tendsto (hPQ : Tendsto P atTop (𝓝 Q)) {p : ℕ} {C : ℝ}
    (hint : ∀ n, Integrable (fun x : ℝ => |x| ^ p) (P n : Measure ℝ))
    (hC : ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ C) :
    Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ) := by
  refine ⟨(measurable_id.pow_const p).aestronglyMeasurable, ?_⟩
  have h := lintegral_abs_pow_le_of_tendsto hPQ hint hC
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  refine lintegral_congr fun x => ?_
  rw [Real.norm_eq_abs, abs_pow]

/-- Under the same hypotheses, the absolute `p`-th moment of the weak limit is at most `C`. -/
theorem integral_abs_pow_le_of_tendsto (hPQ : Tendsto P atTop (𝓝 Q)) {p : ℕ} {C : ℝ}
    (hC0 : 0 ≤ C) (hint : ∀ n, Integrable (fun x : ℝ => |x| ^ p) (P n : Measure ℝ))
    (hC : ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ C) :
    ∫ x, |x| ^ p ∂(Q : Measure ℝ) ≤ C := by
  have hQi : Integrable (fun x : ℝ => |x| ^ p) (Q : Measure ℝ) :=
    integrable_abs_pow (integrable_pow_of_tendsto hPQ hint hC)
  have h := lintegral_abs_pow_le_of_tendsto hPQ hint hC
  rw [← ofReal_integral_eq_lintegral_ofReal hQi
    (Eventually.of_forall fun x => by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC0).1 h

/-- The truncation error at order `p`, integrated. -/
theorem abs_integral_sub_truncPow_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {p : ℕ} {C R : ℝ}
    (hR : 0 < R) (hp : Integrable (fun x : ℝ => x ^ p) ρ)
    (hp1 : Integrable (fun x : ℝ => |x| ^ (p + 1)) ρ)
    (hC : ∫ x, |x| ^ (p + 1) ∂ρ ≤ C) :
    |(∫ x, x ^ p ∂ρ) - ∫ x, truncPow p R x ∂ρ| ≤ 2 / R * C := by
  have hT : Integrable (fun x : ℝ => truncPow p R x) ρ := (truncPow p R).integrable ρ
  rw [← integral_sub hp hT]
  refine le_trans (abs_integral_le_integral_abs) ?_
  have hmono : ∫ x, |x ^ p - truncPow p R x| ∂ρ ≤ ∫ x, 2 / R * |x| ^ (p + 1) ∂ρ := by
    refine integral_mono ((hp.sub hT).abs) (hp1.const_mul _) fun x => ?_
    exact abs_sub_clamp_pow_le hR p x
  calc ∫ x, |x ^ p - truncPow p R x| ∂ρ ≤ ∫ x, 2 / R * |x| ^ (p + 1) ∂ρ := hmono
    _ = 2 / R * ∫ x, |x| ^ (p + 1) ∂ρ := integral_const_mul _ _
    _ ≤ 2 / R * C := by
        refine mul_le_mul_of_nonneg_left hC (by positivity)

/-- Moments pass to the weak limit. -/
theorem tendsto_integral_pow_of_tendsto (hPQ : Tendsto P atTop (𝓝 Q)) (p : ℕ) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hintP : ∀ n q, Integrable (fun x : ℝ => x ^ q) (P n : Measure ℝ))
    (hCP : ∀ n, ∫ x, |x| ^ (p + 1) ∂(P n : Measure ℝ) ≤ C) :
    Tendsto (fun n => ∫ x, x ^ p ∂(P n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ p ∂(Q : Measure ℝ))) := by
  have hintPa : ∀ n, Integrable (fun x : ℝ => |x| ^ (p + 1)) (P n : Measure ℝ) :=
    fun n => integrable_abs_pow (hintP n (p + 1))
  have hQp : Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ) := by
    have hC' : ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ 1 + C := by
      intro n
      calc ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ ∫ x, (1 + |x| ^ (p + 1)) ∂(P n : Measure ℝ) := by
            refine integral_mono (integrable_abs_pow (hintP n p))
              ((integrable_const 1).add (hintPa n)) fun x => ?_
            rcases le_or_gt |x| 1 with h | h
            · have h1 : |x| ^ p ≤ 1 := pow_le_one₀ (abs_nonneg _) h
              have h2 : (0 : ℝ) ≤ |x| ^ (p + 1) := by positivity
              linarith
            · have : |x| ^ p ≤ |x| ^ (p + 1) := pow_le_pow_right₀ h.le (by omega)
              linarith
        _ = 1 + ∫ x, |x| ^ (p + 1) ∂(P n : Measure ℝ) := by
            rw [integral_add (integrable_const 1) (hintPa n), integral_const]
            simp
        _ ≤ 1 + C := by linarith [hCP n]
    exact integrable_pow_of_tendsto hPQ (fun n => integrable_abs_pow (hintP n p)) hC'
  have hQp1 : Integrable (fun x : ℝ => |x| ^ (p + 1)) (Q : Measure ℝ) :=
    integrable_abs_pow (integrable_pow_of_tendsto hPQ hintPa hCP)
  have hCQ : ∫ x, |x| ^ (p + 1) ∂(Q : Measure ℝ) ≤ C :=
    integral_abs_pow_le_of_tendsto hPQ hC0 hintPa hCP
  have hbc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPQ
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ 2 / R * C < ε / 4 := by
    have h0 : Tendsto (fun R : ℝ => 2 / R * C) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => (2 : ℝ) / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using h1.mul_const C
    obtain ⟨R, hR1, hR2⟩ :=
      ((h0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))).and
        (eventually_gt_atTop (0 : ℝ))).exists
    exact ⟨R, hR2, hR1⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hbc (truncPow p R)) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have e1 : |(∫ x, x ^ p ∂(P n : Measure ℝ)) - ∫ x, truncPow p R x ∂(P n : Measure ℝ)|
      ≤ 2 / R * C := abs_integral_sub_truncPow_le hR0 (hintP n p) (hintPa n) (hCP n)
  have e2 : |(∫ x, truncPow p R x ∂(Q : Measure ℝ)) - ∫ x, x ^ p ∂(Q : Measure ℝ)|
      ≤ 2 / R * C := by
    rw [abs_sub_comm]
    exact abs_integral_sub_truncPow_le hR0 hQp hQp1 hCQ
  have e3 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  calc |(∫ x, x ^ p ∂(P n : Measure ℝ)) - ∫ x, x ^ p ∂(Q : Measure ℝ)|
      ≤ |(∫ x, x ^ p ∂(P n : Measure ℝ)) - ∫ x, truncPow p R x ∂(P n : Measure ℝ)|
        + |(∫ x, truncPow p R x ∂(P n : Measure ℝ)) - ∫ x, truncPow p R x ∂(Q : Measure ℝ)|
        + |(∫ x, truncPow p R x ∂(Q : Measure ℝ)) - ∫ x, x ^ p ∂(Q : Measure ℝ)| := by
        have := abs_sub_le (∫ x, x ^ p ∂(P n : Measure ℝ))
          (∫ x, truncPow p R x ∂(P n : Measure ℝ)) (∫ x, x ^ p ∂(Q : Measure ℝ))
        have h2 := abs_sub_le (∫ x, truncPow p R x ∂(P n : Measure ℝ))
          (∫ x, truncPow p R x ∂(Q : Measure ℝ)) (∫ x, x ^ p ∂(Q : Measure ℝ))
        linarith
    _ < ε := by linarith

end Transfer


/-! ### Lemma 1 in moment form

The existence half yields a limit along a subsequence; the whole sequence converges under a
determinacy hypothesis, via `tendsto_of_subseq_tendsto`.
-/

section Lemma1

/-- A uniform absolute-moment bound at every order gives a subsequence converging weakly, with
every moment converging along it. -/
theorem exists_limit_of_moment_bound (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    (hb : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∫ x, |x| ^ p ∂(P n : Measure ℝ) ≤ C) :
    ∃ (Q : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => P (φ k)) atTop (𝓝 Q) ∧
      (∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ)) ∧
      ∀ p, Tendsto (fun k => ∫ x, x ^ p ∂(P (φ k) : Measure ℝ)) atTop
             (𝓝 (∫ x, x ^ p ∂(Q : Measure ℝ))) := by
  obtain ⟨C2, -, hC2⟩ := hb 2
  have hC2' : ∀ n, ∫ x, x ^ 2 ∂(P n : Measure ℝ) ≤ C2 := by
    intro n
    have he : ∫ x, x ^ 2 ∂(P n : Measure ℝ) = ∫ x, |x| ^ 2 ∂(P n : Measure ℝ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [sq_abs]
    rw [he]
    exact hC2 n
  have htight := isTightMeasureSet_of_moment_bound (fun n => hint n 2) hC2'
  have hcomp : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨Q, -, φ, hφ, hQ⟩ := hcomp.isSeqCompact (x := P) (fun n => subset_closure ⟨n, rfl⟩)
  have hQ' : Tendsto (fun k => P (φ k)) atTop (𝓝 Q) := hQ
  refine ⟨Q, φ, hφ, hQ', fun p => ?_, fun p => ?_⟩
  · obtain ⟨D, -, hD⟩ := hb p
    exact integrable_pow_of_tendsto hQ' (fun k => integrable_abs_pow (hint (φ k) p))
      (fun k => hD (φ k))
  · obtain ⟨C, hC0, hC⟩ := hb (p + 1)
    exact tendsto_integral_pow_of_tendsto hQ' p hC0 (fun k q => hint (φ k) q) (fun k => hC (φ k))

/-- **Janson's Lemma 1, existence half, in moment form.** If the moments converge, a
subsequence converges weakly to a law whose moments are the limits. -/
theorem exists_limit_of_tendsto_moments (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {α : ℕ → ℝ}
    (hconv : ∀ p, Tendsto (fun n => ∫ x, x ^ p ∂(P n : Measure ℝ)) atTop (𝓝 (α p))) :
    ∃ (Q : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => P (φ k)) atTop (𝓝 Q) ∧
      (∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ)) ∧
      ∀ p, ∫ x, x ^ p ∂(Q : Measure ℝ) = α p := by
  obtain ⟨Q, φ, hφ, hQ, hQi, hQm⟩ :=
    exists_limit_of_moment_bound P hint (fun p => exists_abs_moment_bound hint hconv p)
  refine ⟨Q, φ, hφ, hQ, hQi, fun p => ?_⟩
  exact tendsto_nhds_unique (hQm p) ((hconv p).comp hφ.tendsto_atTop)

/-- **Janson's Lemma 1, conditional half.** If the limiting moments determine the law, the whole
sequence converges in distribution to it. -/
theorem tendsto_of_tendsto_moments (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {α : ℕ → ℝ}
    (hconv : ∀ p, Tendsto (fun n => ∫ x, x ^ p ∂(P n : Measure ℝ)) atTop (𝓝 (α p)))
    (Q₀ : ProbabilityMeasure ℝ)
    (hdet : ∀ Q : ProbabilityMeasure ℝ, (∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ)) →
      (∀ p, ∫ x, x ^ p ∂(Q : Measure ℝ) = α p) → Q = Q₀) :
    Tendsto P atTop (𝓝 Q₀) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨Q, φ, -, hQ, hQi, hQm⟩ :=
    exists_limit_of_tendsto_moments (fun k => P (ns k)) (fun k p => hint (ns k) p)
      (α := α) (fun p => (hconv p).comp hns)
  refine ⟨φ, ?_⟩
  rw [← hdet Q hQi hQm]
  exact hQ

end Lemma1

/-! ### Janson's `p_j`

Janson writes `α_j = p_j (κ_1, …, κ_j)` for a polynomial `p_j`. The definition
`Janson.momentOf` gives `p_j` by the moment–cumulant recursion `Cumulant.moment_recursion`.
-/

section MomentOf

/-- Janson's `p_j (κ_1, …, κ_j)`, given by the moment–cumulant recursion. -/
noncomputable def momentOf (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | (n + 1) => ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c (j + 1) * momentOf c (n - j)
decreasing_by omega

lemma momentOf_zero (c : ℕ → ℝ) : momentOf c 0 = 1 := by rw [momentOf]

lemma momentOf_succ (c : ℕ → ℝ) (n : ℕ) :
    momentOf c (n + 1)
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c (j + 1) * momentOf c (n - j) := by
  rw [momentOf]

/-- Convergent semiinvariants give convergent moments, by strong induction on the recursion. -/
theorem tendsto_integral_pow_of_tendsto_cumulant {P : ℕ → ProbabilityMeasure ℝ} {c : ℕ → ℝ}
    (hc : ∀ j, 1 ≤ j →
      Tendsto (fun m => Cumulant.cumulant id j (P m : Measure ℝ)) atTop (𝓝 (c j)))
    (p : ℕ) :
    Tendsto (fun m => ∫ x, x ^ p ∂(P m : Measure ℝ)) atTop (𝓝 (momentOf c p)) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases p with _ | n
    · have h0 : ∀ m : ℕ, ∫ x, x ^ 0 ∂(P m : Measure ℝ) = 1 := by
        intro m
        simp
      simp only [h0, momentOf_zero]
      exact tendsto_const_nhds
    · have hrec : ∀ m : ℕ, ∫ x, x ^ (n + 1) ∂(P m : Measure ℝ)
          = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
              * Cumulant.cumulant id (j + 1) (P m : Measure ℝ)
              * ∫ x, x ^ (n - j) ∂(P m : Measure ℝ) := by
        intro m
        simpa only [id_eq] using Cumulant.moment_recursion (P m : Measure ℝ) id n
      simp only [hrec, momentOf_succ]
      refine tendsto_finsetSum _ fun j hj => ?_
      rw [Finset.mem_range] at hj
      exact (tendsto_const_nhds.mul (hc (j + 1) (by omega))).mul (ih (n - j) (by omega))

/-- A law whose moments are `momentOf c` has semiinvariants `c` (via
`Cumulant.cumulant_unique`). -/
theorem cumulant_eq_of_integral_pow_eq {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℕ → ℝ}
    (h : ∀ p, ∫ x, x ^ p ∂Q = momentOf c p) :
    ∀ j, 1 ≤ j → Cumulant.cumulant id j Q = c j := by
  refine Cumulant.cumulant_unique (fun n => ?_)
  simp only [h]
  exact momentOf_succ c n

/-- The semiinvariant is a continuous function of the moments, since the `i = n` summand of
`Cumulant.moment_recursion` is `κ_{n+1}` alone. Hence convergence of the moments along a
subsequence gives convergence of every semiinvariant. -/
theorem tendsto_cumulant_of_tendsto_integral_pow {P : ℕ → ProbabilityMeasure ℝ}
    {Q : ProbabilityMeasure ℝ}
    (h : ∀ p, Tendsto (fun l => ∫ x, x ^ p ∂(P l : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ p ∂(Q : Measure ℝ)))) (j : ℕ) :
    Tendsto (fun l => Cumulant.cumulant id j (P l : Measure ℝ)) atTop
      (𝓝 (Cumulant.cumulant id j (Q : Measure ℝ))) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | n
    · simp only [Cumulant.cumulant_zero]
      exact tendsto_const_nhds
    · have hsolve : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
          Cumulant.cumulant id (n + 1) ρ = (∫ x, x ^ (n + 1) ∂ρ)
            - ∑ i ∈ Finset.range n, (n.choose i : ℝ) * Cumulant.cumulant id (i + 1) ρ
                * ∫ x, x ^ (n - i) ∂ρ := by
        intro ρ hρ
        have hr := Cumulant.moment_recursion ρ id n
        simp only [id_eq] at hr
        rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self] at hr
        have h0 : ∫ x : ℝ, x ^ 0 ∂ρ = 1 := by simp
        rw [h0] at hr
        simp only [Nat.cast_one, one_mul, mul_one] at hr
        linarith
      simp only [hsolve _ inferInstance]
      refine Tendsto.sub (h (n + 1)) ?_
      refine tendsto_finsetSum _ fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (tendsto_const_nhds.mul (ih (i + 1) (by omega))).mul (h (n - i))

/-- Bounded semiinvariants give bounded moments. -/
theorem exists_moment_bound_of_cumulant_bound {P : ℕ → ProbabilityMeasure ℝ}
    (hb : ∀ j, 1 ≤ j → ∃ C : ℝ, ∀ k, |Cumulant.cumulant id j (P k : Measure ℝ)| ≤ C) (p : ℕ) :
    ∃ C : ℝ, ∀ k, |∫ x, x ^ p ∂(P k : Measure ℝ)| ≤ C := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases p with _ | n
    · exact ⟨1, fun k => by simp⟩
    · have hB : ∀ i : ℕ, ∃ C : ℝ, ∀ k, |Cumulant.cumulant id (i + 1) (P k : Measure ℝ)| ≤ C :=
        fun i => hb (i + 1) (by omega)
      choose B hBle using hB
      have hD : ∀ i : ℕ, ∃ C : ℝ, ∀ k, |∫ x, x ^ (n - i) ∂(P k : Measure ℝ)| ≤ C :=
        fun i => ih (n - i) (by omega)
      choose D hDle using hD
      refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |B i| * |D i|, fun k => ?_⟩
      have hr := Cumulant.moment_recursion (P k : Measure ℝ) id n
      simp only [id_eq] at hr
      rw [hr]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.choose i : ℝ))]
      refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_ (abs_nonneg _)
        (by positivity)
      · exact (hBle i k).trans (le_abs_self _)
      · exact (hDle i k).trans (le_abs_self _)

end MomentOf

/-! ### Lemma 1 in semiinvariant form, and the Gaussian case -/

section Semiinvariant

/-- **Janson's Lemma 1, existence half, in semiinvariant form.** There is a law `X` with
`κ_j (X) = c_j` for all `j ≥ 1`. -/
theorem exists_measure_cumulant_eq (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {c : ℕ → ℝ}
    (hc : ∀ j, 1 ≤ j →
      Tendsto (fun m => Cumulant.cumulant id j (P m : Measure ℝ)) atTop (𝓝 (c j))) :
    ∃ Q : ProbabilityMeasure ℝ, (∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ)) ∧
      ∀ j, 1 ≤ j → Cumulant.cumulant id j (Q : Measure ℝ) = c j := by
  obtain ⟨Q, -, -, -, hQi, hQm⟩ :=
    exists_limit_of_tendsto_moments P hint
      (fun p => tendsto_integral_pow_of_tendsto_cumulant hc p)
  exact ⟨Q, hQi, cumulant_eq_of_integral_pow_eq hQm⟩

/-- The Gaussian law as a bundled probability measure. -/
noncomputable def gaussPM (mu s2 : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal mu s2.toNNReal, inferInstance⟩

@[simp]
lemma gaussPM_toMeasure (mu s2 : ℝ) :
    (gaussPM mu s2 : Measure ℝ) = gaussianReal mu s2.toNNReal := rfl

/-- A law with finite moments of all orders, first two semiinvariants `mu` and `s2`, and
vanishing semiinvariants of order three and higher is `gaussPM mu s2`
(`Cumulant.eq_gaussianReal_of_cumulant_eq_zero`). -/
theorem eq_gaussPM_of_cumulant_eq {Q : ProbabilityMeasure ℝ} {mu s2 : ℝ}
    (hint : ∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ))
    (h1 : Cumulant.cumulant id 1 (Q : Measure ℝ) = mu)
    (h2 : Cumulant.cumulant id 2 (Q : Measure ℝ) = s2)
    (h3 : ∀ j, 3 ≤ j → Cumulant.cumulant id j (Q : Measure ℝ) = 0) :
    Q = gaussPM mu s2 := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  have h := Cumulant.eq_gaussianReal_of_cumulant_eq_zero (μ := (Q : Measure ℝ)) hint
    (m₀ := 3) (by norm_num) h3
  rw [gaussPM_toMeasure, h, h1, h2]

/-- If the semiinvariants of `P n` converge to those of `gaussPM mu s2`, then `P n` converges
weakly to `gaussPM mu s2`. -/
theorem tendsto_gaussPM_of_tendsto_cumulant {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {mu s2 : ℝ}
    (h1 : Tendsto (fun m => Cumulant.cumulant id 1 (P m : Measure ℝ)) atTop (𝓝 mu))
    (h2 : Tendsto (fun m => Cumulant.cumulant id 2 (P m : Measure ℝ)) atTop (𝓝 s2))
    (h3 : ∀ j, 3 ≤ j →
      Tendsto (fun m => Cumulant.cumulant id j (P m : Measure ℝ)) atTop (𝓝 0)) :
    Tendsto P atTop (𝓝 (gaussPM mu s2)) := by
  classical
  set c : ℕ → ℝ := fun j => if j = 1 then mu else if j = 2 then s2 else 0 with hcdef
  have hc : ∀ j, 1 ≤ j →
      Tendsto (fun m => Cumulant.cumulant id j (P m : Measure ℝ)) atTop (𝓝 (c j)) := by
    intro j hj
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j
      · simpa [hcdef] using h1
      · simpa [hcdef] using h2
    · have hz : c j = 0 := by
        simp only [hcdef]
        split_ifs <;> first | rfl | omega
      rw [hz]
      exact h3 j h
  refine tendsto_of_tendsto_moments P hint
    (fun p => tendsto_integral_pow_of_tendsto_cumulant hc p) _ ?_
  intro Q hQi hQm
  have hcum := cumulant_eq_of_integral_pow_eq hQm
  refine eq_gaussPM_of_cumulant_eq hQi ?_ ?_ ?_
  · rw [hcum 1 le_rfl]
    simp [hcdef]
  · rw [hcum 2 (by norm_num)]
    simp [hcdef]
  · intro j hj
    rw [hcum j (by omega)]
    simp only [hcdef]
    split_ifs <;> first | rfl | omega

end Semiinvariant

end StatLean.AsymptoticStatistics.Janson
