import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import StatLean.ConcentrationInequalities.McDiarmid.McDiarmid

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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.2 (The Kolmogorov–Smirnov Test), supporting material for Theorems 16.2.1 and 16.2.2:
a uniform-in-`n` exponential tail for the empirical process. (`TSH4 §16.2 Thm 16.2.1, Thm
16.2.2`.)

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

open MeasureTheory ProbabilityTheory Filter Topology
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

/-! ### Deterministic reduction to a rational supremum -/

/-- The step indicator `t ↦ 1{a ≤ t}` is right continuous. -/
private lemma dkw_rightCont_step (a s : ℝ) :
    Filter.Tendsto (fun t => if a ≤ t then (1 : ℝ) else 0)
      (nhdsWithin s (Set.Ioi s)) (nhds (if a ≤ s then (1 : ℝ) else 0)) := by
  have hl : (fun _ : ℝ => if a ≤ s then (1 : ℝ) else 0)
      =ᶠ[nhdsWithin s (Set.Ioi s)] (fun t => if a ≤ t then (1 : ℝ) else 0) := by
    by_cases h : a ≤ s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [if_pos h, if_pos (h.trans ht.le)]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp h))] with t ht
      rw [if_neg h, if_neg (not_le.mpr ht)]
  exact Filter.Tendsto.congr' hl tendsto_const_nhds

/-- A real supremum of a right-continuous function over `ℝ` agrees with the supremum over
the rationals. -/
private lemma dkw_iSup_real_eq_iSup_rat (g : ℝ → ℝ)
    (hrc : ∀ s, Filter.Tendsto g (nhdsWithin s (Set.Ioi s)) (nhds (g s))) :
    ⨆ t : ℝ, g t = ⨆ q : ℚ, g (q : ℝ) := by
  by_cases hbdd : BddAbove (Set.range fun q : ℚ => g (q : ℝ))
  · have hle : ∀ t : ℝ, g t ≤ ⨆ q : ℚ, g (q : ℝ) := by
      intro t
      obtain ⟨u, hu_gt, hu_lt⟩ : ∃ u : ℕ → ℚ,
          (∀ k, t < (u k : ℝ)) ∧ (∀ k, (u k : ℝ) < t + 1 / ((k : ℝ) + 1)) := by
        choose u hu using fun k : ℕ =>
          exists_rat_btwn (show t < t + 1 / ((k : ℝ) + 1) from
            lt_add_of_pos_right t (by positivity))
        exact ⟨u, fun k => (hu k).1, fun k => (hu k).2⟩
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      have hnhds : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhds t) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
          (Filter.Eventually.of_forall fun k => (hu_gt k).le)
          (Filter.Eventually.of_forall fun k => (hu_lt k).le)
      have htend : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhdsWithin t (Set.Ioi t)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hnhds, Filter.Eventually.of_forall fun k => hu_gt k⟩
      exact le_of_tendsto ((hrc t).comp htend)
        (Filter.Eventually.of_forall fun k => le_ciSup hbdd (u k))
    have hbddR : BddAbove (Set.range g) :=
      ⟨⨆ q : ℚ, g (q : ℝ), by rintro _ ⟨t, rfl⟩; exact hle t⟩
    exact le_antisymm (ciSup_le hle) (ciSup_le fun q => le_ciSup hbddR (q : ℝ))
  · have hbddR : ¬ BddAbove (Set.range g) := by
      intro hR
      obtain ⟨M, hM⟩ := hR
      exact hbdd ⟨M, by rintro _ ⟨q, rfl⟩; exact hM ⟨(q : ℝ), rfl⟩⟩
    rw [ciSup_of_not_bddAbove hbddR, ciSup_of_not_bddAbove hbdd]

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

/-- The empirical distribution function as a function of the *sample vector*
`x : Fin n → ℝ`: `F̂ₙ(t) = n⁻¹ #{i : xᵢ ≤ t}`. Equal to `empCDF X ω` at `x = (Xᵢ ω)ᵢ`. -/
private noncomputable def dkwEmp {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if x i ≤ t then (1 : ℝ) else 0

/-- The Kolmogorov distance as a function of the sample vector `x : Fin n → ℝ`.
Equal to `ksDist X μ ω` at `x = (Xᵢ ω)ᵢ`; the bounded-differences function of McDiarmid. -/
private noncomputable def dkwF {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨆ t : ℝ, |dkwEmp x t - cdf μ t|

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
  classical
  set mP : ℝ := ∫ ω, ksDist X μ ω ∂P with hmP_def
  -- `ksDist X μ ω` is the sample-vector Kolmogorov distance evaluated at `(Xᵢ ω)ᵢ`.
  have hksF : ∀ ω, ksDist X μ ω = dkwF μ (StatLean.ConcentrationInequalities.allVars X ω) := by
    intro ω; rfl
  -- basic `[0,1]` bounds on the empirical CDF and hence on the integrand
  have hsum_nonneg : ∀ (z : Fin n → ℝ) (t : ℝ),
      (0 : ℝ) ≤ ∑ i, if z i ≤ t then (1 : ℝ) else 0 :=
    fun z t => Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hsum_le : ∀ (z : Fin n → ℝ) (t : ℝ),
      (∑ i, if z i ≤ t then (1 : ℝ) else 0) ≤ n := fun z t => by
    calc (∑ i, if z i ≤ t then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = n := by simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hemp0 : ∀ (z : Fin n → ℝ) t, 0 ≤ dkwEmp z t := fun z t => by
    simp only [dkwEmp]; exact mul_nonneg (by positivity) (hsum_nonneg z t)
  have hemp1 : ∀ (z : Fin n → ℝ) t, dkwEmp z t ≤ 1 := fun z t => by
    simp only [dkwEmp]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hsum_le z t
  have hA1 : ∀ (z : Fin n → ℝ) t, |dkwEmp z t - cdf μ t| ≤ 1 := fun z t => by
    rw [abs_le]
    exact ⟨by linarith [hemp0 z t, cdf_le_one μ t], by linarith [hemp1 z t, cdf_nonneg μ t]⟩
  have hbddAx : ∀ z : Fin n → ℝ,
      BddAbove (Set.range fun t => |dkwEmp z t - cdf μ t|) :=
    fun z => ⟨1, by rintro _ ⟨t, rfl⟩; exact hA1 z t⟩
  have hF0 : ∀ z, 0 ≤ dkwF μ z := fun z => by
    simp only [dkwF]
    exact le_ciSup_of_le (hbddAx z) 0 (abs_nonneg _)
  have hF1 : ∀ z, dkwF μ z ≤ 1 := fun z => by
    simp only [dkwF]; exact ciSup_le fun t => hA1 z t
  -- measurability of `dkwF μ` (reduce the real sup to a rational one)
  have hf : Measurable (dkwF (n := n) μ) := by
    have hFrat : ∀ x : Fin n → ℝ,
        dkwF μ x = ⨆ q : ℚ, |dkwEmp x (q : ℝ) - cdf μ (q : ℝ)| := by
      intro x
      refine dkw_iSup_real_eq_iSup_rat (fun t => |dkwEmp x t - cdf μ t|) fun s => ?_
      have hempRC : Tendsto (fun t => dkwEmp x t) (nhdsWithin s (Set.Ioi s))
          (nhds (dkwEmp x s)) := by
        simp only [dkwEmp]
        exact (tendsto_finset_sum Finset.univ
          fun i _ => dkw_rightCont_step (x i) s).const_mul _
      have hcdfRC : Tendsto (fun t => cdf μ t) (nhdsWithin s (Set.Ioi s)) (nhds (cdf μ s)) :=
        ((cdf μ).right_continuous s).mono Set.Ioi_subset_Ici_self
      exact Filter.Tendsto.abs (hempRC.sub hcdfRC)
    rw [show dkwF μ = fun x => ⨆ q : ℚ, |dkwEmp x (q : ℝ) - cdf μ (q : ℝ)| from funext hFrat]
    refine Measurable.iSup fun q : ℚ => Measurable.abs (Measurable.sub ?_ measurable_const)
    simp only [dkwEmp]
    exact (Finset.univ.measurable_sum fun i _ =>
      Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
        measurable_const measurable_const).const_mul _
  -- bounded differences: changing one coordinate moves `dkwF` by at most `n⁻¹`
  have hbd : ∀ (k : Fin n) (x : Fin n → ℝ) (y : ℝ),
      |dkwF μ x - dkwF μ (Function.update x k y)| ≤ (n : ℝ)⁻¹ := by
    intro k x y
    have hemp_diff : ∀ t, |dkwEmp (Function.update x k y) t - dkwEmp x t| ≤ (n : ℝ)⁻¹ := by
      intro t
      have hsum : (∑ i, if (Function.update x k y) i ≤ t then (1 : ℝ) else 0)
          - (∑ i, if x i ≤ t then (1 : ℝ) else 0)
          = (if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0) := by
        rw [← Finset.sum_sub_distrib,
          Finset.sum_eq_single k
            (fun i _ hik => by rw [Function.update_of_ne hik, sub_self])
            (fun h => absurd (Finset.mem_univ k) h),
          Function.update_self]
      have hind : |(if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0)| ≤ 1 := by
        by_cases hy : y ≤ t <;> by_cases hxk : x k ≤ t
        · rw [if_pos hy, if_pos hxk]; norm_num
        · rw [if_pos hy, if_neg hxk]; norm_num
        · rw [if_neg hy, if_pos hxk]; norm_num
        · rw [if_neg hy, if_neg hxk]; norm_num
      simp only [dkwEmp]
      rw [← mul_sub, hsum, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      calc (n : ℝ)⁻¹ * |(if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0)|
          ≤ (n : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hind (by positivity)
        _ = (n : ℝ)⁻¹ := mul_one _
    have hApt : ∀ t, |(|dkwEmp (Function.update x k y) t - cdf μ t|)
        - (|dkwEmp x t - cdf μ t|)| ≤ (n : ℝ)⁻¹ := by
      intro t
      have h1 : |(|dkwEmp (Function.update x k y) t - cdf μ t|) - (|dkwEmp x t - cdf μ t|)|
          ≤ |(dkwEmp (Function.update x k y) t - cdf μ t) - (dkwEmp x t - cdf μ t)| :=
        abs_abs_sub_abs_le_abs_sub _ _
      have h2 : (dkwEmp (Function.update x k y) t - cdf μ t) - (dkwEmp x t - cdf μ t)
          = dkwEmp (Function.update x k y) t - dkwEmp x t := by ring
      rw [h2] at h1
      exact h1.trans (hemp_diff t)
    have hle1 : dkwF μ (Function.update x k y) ≤ dkwF μ x + (n : ℝ)⁻¹ := by
      simp only [dkwF]
      refine ciSup_le fun t => ?_
      have hb : |dkwEmp x t - cdf μ t| ≤ ⨆ t', |dkwEmp x t' - cdf μ t'| := le_ciSup (hbddAx x) t
      have hh := hApt t; rw [abs_le] at hh
      linarith [hh.2, hb]
    have hle2 : dkwF μ x ≤ dkwF μ (Function.update x k y) + (n : ℝ)⁻¹ := by
      simp only [dkwF]
      refine ciSup_le fun t => ?_
      have hb : |dkwEmp (Function.update x k y) t - cdf μ t|
          ≤ ⨆ t', |dkwEmp (Function.update x k y) t' - cdf μ t'| := le_ciSup (hbddAx _) t
      have hh := hApt t; rw [abs_le] at hh
      linarith [hh.1, hb]
    rw [abs_le]
    exact ⟨by linarith [hle1], by linarith [hle2]⟩
  -- transfer to the standard-Borel product space `(Fin n → ℝ, Q)`, `Q = P.map (Xᵢ)ᵢ`
  set μi : Fin n → Measure ℝ := fun i => P.map (X i) with hμi
  haveI hμiP : ∀ i, IsProbabilityMeasure (μi i) := fun i => by
    rw [hμi]; exact Measure.isProbabilityMeasure_map (hmeas i).aemeasurable
  set Q : Measure (Fin n → ℝ) := Measure.pi μi with hQ
  have hmeasAV : Measurable (StatLean.ConcentrationInequalities.allVars X) :=
    measurable_pi_lambda _ fun i => hmeas i
  have hQeq : P.map (StatLean.ConcentrationInequalities.allVars X) = Q :=
    (iIndepFun_iff_map_fun_eq_pi_map fun i => (hmeas i).aemeasurable).1 hindep
  set Y : ∀ _ : Fin n, (Fin n → ℝ) → ℝ := fun i x => x i with hY_def
  have hYmeas : ∀ i, Measurable (Y i) := fun i => measurable_pi_apply i
  have hYindep : iIndepFun Y Q := by
    rw [hQ]; exact iIndepFun_pi (X := fun _ => id) fun i => aemeasurable_id
  have hAVYx : ∀ x, StatLean.ConcentrationInequalities.allVars Y x = x := fun _ => rfl
  have hFint : Integrable
      (dkwF μ ∘ StatLean.ConcentrationInequalities.allVars Y) Q := by
    have hInt : Integrable (dkwF μ) Q := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
      exact hF1 x
    simpa [Function.comp_def, hAVYx] using hInt
  -- the McDiarmid sub-Gaussian MGF bound and its Chernoff tail
  have hsg := StatLean.ConcentrationInequalities.mgf_sub_expectation_le
    Y hYmeas (dkwF μ) hf (fun _ => (n : ℝ)⁻¹) (fun _ => by positivity) hbd hYindep hFint
  set t : ℝ := d / Real.sqrt (n : ℝ) with ht_def
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have htge : (0 : ℝ) ≤ t := div_nonneg hd hsqrt_pos.le
  have hchern := hsg.measure_ge_le htge
  -- the sub-Gaussian proxy `∑ (‖n⁻¹‖₊/2)² = 1/(4n)`, giving the exponent `-2 d²`
  have hσcoe : ((∑ _k : Fin n, (‖(n : ℝ)⁻¹‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / (4 * (n : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    field_simp
    ring
  have ht_sq : t ^ 2 = d ^ 2 / n := by
    rw [ht_def, div_pow, Real.sq_sqrt (by positivity)]
  have hexp : -t ^ 2 / (2 * ((∑ _k : Fin n, (‖(n : ℝ)⁻¹‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))
      = -2 * d ^ 2 := by
    rw [hσcoe, ht_sq]
    field_simp
    ring
  rw [hexp] at hchern
  -- rewrite the product-space tail back to the original space
  have hint_eq : (∫ x, dkwF μ x ∂Q) = mP := by
    rw [← hQeq, integral_map hmeasAV.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hksF ω).symm)
  have hset_eq : Q {x | t ≤ dkwF μ (StatLean.ConcentrationInequalities.allVars Y x)
        - ∫ x', dkwF μ (StatLean.ConcentrationInequalities.allVars Y x') ∂Q}
      = P {ω | t ≤ ksDist X μ ω - mP} := by
    simp only [hAVYx]
    rw [hint_eq, ← hQeq,
      Measure.map_apply hmeasAV (measurableSet_le measurable_const (hf.sub measurable_const))]
    rfl
  have hbound : Q {x | t ≤ dkwF μ (StatLean.ConcentrationInequalities.allVars Y x)
        - ∫ x', dkwF μ (StatLean.ConcentrationInequalities.allVars Y x') ∂Q}
      ≤ ENNReal.ofReal (Real.exp (-2 * d ^ 2)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
    exact ENNReal.ofReal_le_ofReal hchern
  rw [hset_eq] at hbound
  -- finally match the target event via `d ≤ √n · z ↔ d/√n ≤ z`
  have hfinal : {ω | d ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - mP)}
      = {ω | t ≤ ksDist X μ ω - mP} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ht_def, div_le_iff₀' hsqrt_pos]
  rw [hfinal]
  exact hbound

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
