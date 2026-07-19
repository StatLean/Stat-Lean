import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A uniform-in-`n` exponential tail for the empirical process

For an i.i.d. real sample `X₁, …, Xₙ` with law `μ` and distribution function `F`, the
Kolmogorov distance between the empirical and the population distribution function,
$$D_n \;=\; \sup_{t \in \mathbb R}\bigl|\hat F_n(t) - F(t)\bigr| ,$$
satisfies an exponential tail bound *with constants free of `n` and of `μ`*:
$$\mathbb P\bigl(\sqrt n\, D_n \ge d\bigr) \;\le\; C\,e^{-c\,d^2}
  \qquad (d \ge 0).$$
This is the finite-sample input needed to calibrate a distribution-free goodness-of-fit
test at a fixed threshold, without ever invoking the Kolmogorov limit law: a rejection
threshold `d_α` with `C e^{-c d_α²} ≤ α` gives a test of level `α` at *every* sample size.

## Main results

* `empCDF`, `ksDist` — the empirical distribution function of a finite sample and its
  Kolmogorov distance to a population law.
* `integral_ksDist_le` — the in-expectation bound `E Dₙ ≤ 2/√n`.
* `ksDist_concentration` — bounded-differences concentration of `Dₙ` around its mean.
* `dkw_uniform` — the tail bound, `P(√n Dₙ ≥ d) ≤ 4 e^{-d²/8}`.

**Constants (documented deviation).** The sharp form of this inequality has the constants
`C = 2`, `c = 2`, and those are *not* what the route formalised here delivers. We state the
strictly weaker `C = 4`, `c = 1/8`, which is exactly what the two ingredients above
compose to and which is implied by the sharp form, so the statement is true:

* for `d ≤ 3.33…` one has `4 e^{-d²/8} ≥ 1` and the bound is vacuous — in particular it
  covers the whole range `d ≤ 2` where the mean bound leaves nothing to prove;
* for `d ≥ 2`, `√n Dₙ ≥ d` forces `√n (Dₙ − E Dₙ) ≥ d − 2`, so the concentration bound
  gives `e^{-2(d-2)²}`, and `2(d-2)² ≥ d²/8 − log 4` holds for all `d ≥ 2` (the left-hand
  side minus the right-hand side has minimum `≈ 0.85` near `d = 2.06`).

Sharpening `c` to `2` would require the sharp in-expectation constant, which the project
does not have; a more careful chaining bound tightens `C` and `c` without changing any
consumer, since the calibration statements only need *some* explicit pair `(C, c)`.

**Reference.** Classical empirical-process theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The empirical distribution function is defined locally, as a plain average of indicators,
  rather than imported: this file sits in the bottom (`ForMathlib`) layer and must not
  depend on another area's concept layer.
* `ksDist` is an unrestricted real supremum over `t : ℝ`. Both `t ↦ empCDF X ω t` and the
  population `cdf μ` are right-continuous, so the supremum over `ℝ` coincides with the
  supremum over `ℚ`; that identity (a deterministic, pointwise statement) is what makes the
  event measurable and is the standard first step of the proof. The supremum is bounded by
  `1`, so no junk value of `⨆` is ever hit for `n ≥ 1`.
* `ksDist_concentration` is the bounded-differences inequality applied to
  `f(x₁,…,xₙ) = supₜ |n⁻¹ ∑ᵢ 1{xᵢ ≤ t} − F(t)|`, which changes by at most `1/n` when one
  coordinate is changed; with `cᵢ = 1/n` the bound `exp(-2s²/∑cᵢ²) = exp(-2ns²)` at
  `s = d/√n` is `exp(-2d²)`. The project's McDiarmid theorem
  (`StatLean.ConcentrationInequalities.McDiarmid`) is the intended engine; it cannot be
  imported here (it lives in another area's assembly layer), so the statement is restated
  and re-proved locally, or the brick is promoted when the proof is written.
* `integral_ksDist_le` is the chaining/symmetrisation half. The half-line class has VC
  dimension `1` and a bounded entropy integral, so a symmetrisation + Dudley argument gives
  `E Dₙ ≤ C₀/√n`; the constant is stated as `2`, which leaves ample room above the true
  value (`≈ 0.63/√n`) while remaining far below what a crude chaining bound would produce
  if all numerical factors were kept. The project's chaining assets
  (`ConcentrationInequalities/Chaining/Dudley.lean`, `VC/GlivenkoCantelli.lean`) are the
  models to follow; the constant `5400` recorded there comes from a generic VC bound and is
  too lossy for this purpose, so the half-line entropy must be used directly.
* Events are stated with a closed inequality `d ≤ …`; this is the stronger form and the
  underlying sub-Gaussian Chernoff bound supplies it directly.

**Bibliographic comments.** The inequality is due to A. Dvoretzky, J. Kiefer, and
J. Wolfowitz, "Asymptotic minimax character of the sample distribution function and of the
classical multinomial estimator," *Ann. Math. Statist.* **27** (1956), 642–669, who
obtained it with an unspecified constant; the sharp constant `2` was established by
P. Massart, "The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality," *Ann.
Probab.* **18** (1990), 1269–1283. The concentration step is the bounded-differences
method of C. McDiarmid, "On the method of bounded differences," in *Surveys in
Combinatorics 1989*, LMS Lecture Note Series **141**, Cambridge Univ. Press, 1989,
148–188; the entropy/chaining bound for the expectation follows R. M. Dudley, "The sizes of
compact subsets of Hilbert space and continuity of Gaussian processes," *J. Funct. Anal.*
**1** (1967), 290–330. The statistic itself is A. N. Kolmogorov's, "Sulla determinazione
empirica di una legge di distribuzione," *Giorn. Ist. Ital. Attuari* **4** (1933), 83–91,
with the two-sample and tabulated forms due to N. V. Smirnov, "Table for estimating the
goodness of fit of empirical distributions," *Ann. Math. Statist.* **19** (1948), 279–281.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The **empirical distribution function** of a finite sample:
`F̂ₙ(t) = n⁻¹ #{i : Xᵢ ≤ t}`. For `n = 0` it is identically `0` (junk, excluded by the
side conditions of every statement below). -/
noncomputable def empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then (1 : ℝ) else 0

/-- The **Kolmogorov distance** between the empirical distribution function of a sample and
the distribution function of a law `μ`: `Dₙ = supₜ |F̂ₙ(t) − F(t)|`.

The supremum ranges over all of `ℝ`; by right-continuity of both functions it agrees with
the supremum over the rationals, which is how measurability of `Dₙ` is obtained. -/
noncomputable def ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) : ℝ :=
  ⨆ t : ℝ, |empCDF X ω t - cdf μ t|

/-- **Mean of the Kolmogorov distance.** For an i.i.d. sample of size `n ≥ 1`,
`E Dₙ ≤ 2/√n`, uniformly in the sampling law.

Symmetrisation plus a chaining bound over the half-line class; see the file header for the
provenance of the constant `2`. -/
theorem integral_ksDist_le {n : ℕ}
    -- USER-INPUT: a nonempty sample (for `n = 0` the statement is false: `D₀ = supₜ F(t)`).
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each observation has law `μ`.
    (hlaw : ∀ i, P.map (X i) = μ) :
    ∫ ω, ksDist X μ ω ∂P ≤ 2 / Real.sqrt n := by
  sorry

/-- **Concentration of the Kolmogorov distance around its mean.**
Changing one observation moves `Dₙ` by at most `1/n`, so the bounded-differences inequality
with constants `cᵢ = 1/n` gives, for `d ≥ 0`,
`P(√n (Dₙ − E Dₙ) ≥ d) ≤ exp(−2 d²)`.

Only independence of the observations is used here; they need not be identically
distributed, and no property of `μ` enters. -/
theorem ksDist_concentration {n : ℕ}
    -- USER-INPUT: a nonempty sample.
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: a nonnegative deviation level.
    {d : ℝ} (hd : 0 ≤ d) :
    P {ω | d ≤ Real.sqrt n * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)}
      ≤ ENNReal.ofReal (Real.exp (-2 * d ^ 2)) := by
  sorry

/-- **Uniform exponential tail for the empirical process.**
For an i.i.d. sample of size `n ≥ 1` from any law `μ` and any `d ≥ 0`,
$$\mathbb P\bigl(\sqrt n \sup_t |\hat F_n(t) - F(t)| \ge d\bigr) \;\le\; 4\,e^{-d^2/8} .$$
The constants are absolute: they depend neither on `n` nor on `μ`, which is what makes a
fixed rejection threshold distribution-free and valid at every sample size.

Obtained by composing `integral_ksDist_le` with `ksDist_concentration`; see the file header
for the arithmetic and for the (documented) gap to the sharp constants. -/
theorem dkw_uniform {n : ℕ}
    -- USER-INPUT: a nonempty sample.
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each observation has law `μ`.
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: a nonnegative threshold.
    {d : ℝ} (hd : 0 ≤ d) :
    P {ω | d ≤ Real.sqrt n * ksDist X μ ω}
      ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 8)) := by
  by_cases hbig : 1 ≤ 4 * Real.exp (-(d ^ 2) / 8)
  · -- the envelope is `≥ 1`; the bound is vacuous
    calc P {ω | d ≤ Real.sqrt n * ksDist X μ ω}
        ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 8)) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbig
  · push_neg at hbig
    -- `4 e^{-d²/8} < 1` forces `d > 2`
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have hexp14 : Real.exp (-(d ^ 2) / 8) < 1 / 4 := by nlinarith [Real.exp_pos (-(d ^ 2) / 8)]
    have hdsq : 8 * Real.log 4 < d ^ 2 := by
      have h2 : -(d ^ 2) / 8 < Real.log (1 / 4) := by
        calc -(d ^ 2) / 8 = Real.log (Real.exp (-(d ^ 2) / 8)) := (Real.log_exp _).symm
          _ < Real.log (1 / 4) := Real.log_lt_log (Real.exp_pos _) hexp14
      rw [show (1 : ℝ) / 4 = 4⁻¹ by norm_num, Real.log_inv] at h2
      linarith
    have hd2 : 0 ≤ d - 2 := by nlinarith [hlog4, hdsq]
    -- mean bound: `√n · E[Dₙ] ≤ 2`
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hEle : Real.sqrt (n : ℝ) * ∫ ω, ksDist X μ ω ∂P ≤ 2 := by
      calc Real.sqrt (n : ℝ) * ∫ ω, ksDist X μ ω ∂P
          ≤ Real.sqrt (n : ℝ) * (2 / Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (integral_ksDist_le hn μ X hmeas hindep hlaw)
              (le_of_lt hsqrt_pos)
        _ = 2 := by field_simp
    -- deviation event forces a bounded-differences deviation
    have hsub : {ω | d ≤ Real.sqrt (n : ℝ) * ksDist X μ ω}
        ⊆ {ω | d - 2 ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [mul_sub]
      linarith
    have hconc := ksDist_concentration hn μ X hmeas hindep hd2
    calc P {ω | d ≤ Real.sqrt (n : ℝ) * ksDist X μ ω}
        ≤ P {ω | d - 2 ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)} :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-2 * (d - 2) ^ 2)) := hconc
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 8)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm,
            ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [hlog4, sq_nonneg (15 * d - 32)]

end StatLean.HypothesisTesting
