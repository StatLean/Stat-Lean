import StatLean.HypothesisTesting.Bootstrap.Defs
import StatLean.HypothesisTesting.ForMathlib.DKWUniform
import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Kolmogorov–Smirnov test: calibration and consistency

For i.i.d. real observations `X₁,…,Xₙ` with c.d.f. `F` and a fully specified null c.d.f.
`F₀`, the Kolmogorov–Smirnov statistic is
$$ T_n \;=\; \sup_{t\in\mathbb R} n^{1/2}\bigl|\hat F_n(t) - F_0(t)\bigr|
        \;=\; n^{1/2}\, d_K(\hat F_n, F_0), $$
where `d_K` is the sup (Kolmogorov) distance between distribution functions. This file
fixes the statistic (`ksStat`), fixes a **calibration** of the critical value, and states
the level and power theorems:

* `ksStat` — the statistic `Tₙ` above, built on the empirical c.d.f.;
* `ksThreshold` — the calibrated critical value (see the calibration note below);
* `ks_dkw_level` — the calibrated test has level `α` at every sample size;
* `ks_consistent` — pointwise consistency against every fixed `F ≠ F₀`;
* `ks_uniform_power` — power `→ 1` uniformly over `n^{1/2} d_K(F, F₀) ≥ εₙ → ∞`;
* `ks_power_lower_bound` — the nonasymptotic power bound behind the previous item.

**Calibration decision (documented deviation).** The classical calibration takes the
critical value to be the `1 − α` quantile `s_{n,1−α}` of the null law of `Tₙ`, whose
asymptotics rest on the Kolmogorov limit law
`P{Tₙ > d} → 2 ∑_{k≥1} (−1)^{k+1} exp(−2k²d²)`. We deliberately avoid that limit law and
calibrate instead through the uniform deviation bound of the sibling brick
`ForMathlib/DKWUniform`. Consequences, all of them documented deviations:

1. `ksThreshold α` does **not** depend on `n`; the level statement is nonasymptotic, and
   the classical step "`s_{n,1−α} → s_{1−α} < ∞`" disappears from every proof below.
2. No continuity assumption on `F₀` is needed anywhere in this file. (The classical
   calibration is distribution-free only for continuous `F₀`; for a discontinuous `F₀` it
   is conservative.)
3. The constants are not sharp. The sharp tail is `2 exp(−2d²)`; the brick delivers
   `4 exp(−d²/8)`, so the calibrated threshold is larger than the classical one and the
   nonasymptotic power bound below carries `4` and `(ε − s)²/8` in place of the classical
   `2` and `2(ε − s)²`. The test remains of level `α` — it is conservative, not wrong.

**Coupling with `ForMathlib/DKWUniform` (single point of contact).** `ksThreshold` is
defined by solving, for `s`, the equation `C e^{−c s²} = α` with the constants `C = 4`,
`c = 1/8` of that brick's `dkw_uniform`:
$$ \mathbb P\bigl\{\, n^{1/2} d_K(\hat F_n, F) \;\ge\; d \,\bigr\}
   \;\le\; 4\, e^{-d^{2}/8}, \qquad d \ge 0, $$
uniformly in `n ≥ 1` and in the sampling law. If those constants are sharpened, the *only*
edit required is the numeral `8 * Real.log (4 / α)` in `ksThreshold`: every statement in
this file and in `KSLocalPower.lean` continues to hold verbatim, because each of them is
phrased through `ksThreshold` and re-derives the level from the same equation.

**Reference.** Classical goodness-of-fit theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* `ksStat` reuses `MultipleTesting.empiricalCDF` (the counting c.d.f. `card {j | Xⱼ ≤ t}/n`)
  and the frozen `supCDFDist` of `Bootstrap/Defs.lean`, so the KS statistic, the bootstrap
  Kolmogorov distance and the multiple-testing empirical c.d.f. are the same objects.
* The sibling brick states its bound through its own `empCDF` / `ksDist`. The two
  presentations are reconciled once and for all by `empiricalCDF_eq_empCDF` and
  `ksStat_eq_sqrt_mul_ksDist`, which every proof below routes through; no statement in
  this file mentions `ksDist`.
* The rejection event involves an uncountable supremum. Rather than assuming its
  measurability at every use site, it is derived once in `measurable_ksStat` from right
  continuity of `F₀` (the empirical c.d.f. is right continuous by construction), i.e. the
  real supremum is a rational supremum.
* Null and alternative c.d.f.s are identified with Mathlib's `cdf` of the corresponding
  law by a single hypothesis `∀ t, F t = cdf μ t`; this supplies right continuity,
  monotonicity and the identification simultaneously.
* `ks_uniform_power` is stated in **sequence form**: the classical statement is an
  infimum of powers over the class `{F : n^{1/2} d_K(F, F₀) ≥ εₙ}`, and the two are
  equivalent (an infimum of a bounded family tends to `1` iff the value along every
  admissible selection does). The sequence form is also the form the classical proof
  argues in, and it is the form that types: each alternative carries its own sampling law,
  i.e. a triangular array `X : (n : ℕ) → Fin n → Ω → ℝ`.

**Bibliographic comments.** The statistic and its limit law are due to A. N. Kolmogorov
("Sulla determinazione empirica di una legge di distribuzione," *Giornale dell'Istituto
Italiano degli Attuari* **4** (1933), 83–91); the two-sample and further distribution
theory to N. V. Smirnov ("Table for estimating the goodness of fit of empirical
distributions," *Ann. Math. Statist.* **19** (1948), 279–281). The uniform deviation
inequality used for the calibration is due to A. Dvoretzky, J. Kiefer and J. Wolfowitz
("Asymptotic minimax character of the sample distribution function and of the classical
multinomial estimator," *Ann. Math. Statist.* **27** (1956), 642–669), with the sharp
constant obtained by P. Massart ("The tight constant in the Dvoretzky–Kiefer–Wolfowitz
inequality," *Ann. Probab.* **18** (1990), 1269–1283). The second, elementary consistency
argument transcribed in `ks_consistent` goes back to F. J. Massey ("A note on the power of
a non-parametric test," *Ann. Math. Statist.* **21** (1950), 440–443).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (empiricalCDF)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The statistic and its calibration -/

/-- The **two-sided Kolmogorov–Smirnov statistic**
`Tₙ = sup_t n^{1/2} |F̂ₙ(t) − F₀(t)| = n^{1/2} d_K(F̂ₙ, F₀)` of a sample `X` against the
fully specified null c.d.f. `F₀`. Built on `MultipleTesting.empiricalCDF` (the empirical
c.d.f. `F̂ₙ`) and on `supCDFDist` (the Kolmogorov distance `d_K`). For `n = 0` the
empirical c.d.f. is identically `0` and the statistic is `0` (junk, guarded by `0 < n`
side conditions everywhere below). -/
noncomputable def ksStat {n : ℕ} (X : Fin n → Ω → ℝ) (F₀ : ℝ → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt (n : ℝ) * supCDFDist (fun t => empiricalCDF X t ω) F₀

/-- The **DKW-calibrated critical value** of the Kolmogorov–Smirnov test at level `α`:
the solution `s` of `4 · exp(−s²/8) = α`, i.e.
$$ s_\alpha \;=\; \sqrt{8\,\log(4/\alpha)} . $$
It is a constant: it does not depend on the sample size, on the null c.d.f., or on the
sampling law. Degenerate inputs (`α ≤ 0`) fall back on the junk conventions of `Real.log`
and `Real.sqrt`; every statement below carries `0 < α < 1`.

COUPLING: the numerals `4` and `8` are the constants `C` and `1/c` of `dkw_uniform` in
`ForMathlib/DKWUniform`; see the module docstring for the reconciliation rule. -/
noncomputable def ksThreshold (α : ℝ) : ℝ :=
  Real.sqrt (8 * Real.log (4 / α))

/-! ### Reconciliation with the deviation brick -/

/-- The empirical c.d.f. of the multiple-testing library and the one of the deviation
brick agree: counting the sample points below a threshold is the same as summing their
indicators. -/
theorem empiricalCDF_eq_empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    empiricalCDF X t ω = empCDF X ω t := by
  sorry

/-- The Kolmogorov–Smirnov statistic against the c.d.f. of a law `μ` is `n^{1/2}` times the
Kolmogorov distance of `ForMathlib/DKWUniform`. This is the single bridge through which
every proof in this file and in `KSLocalPower.lean` reaches the deviation inequality. -/
theorem ksStat_eq_sqrt_mul_ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) :
    ksStat X (fun t => cdf μ t) ω = Real.sqrt (n : ℝ) * ksDist X μ ω := by
  sorry

/-- Measurability of the Kolmogorov–Smirnov statistic. The supremum defining `d_K` ranges
over all of `ℝ`, but both competing functions are right continuous — the empirical c.d.f.
by construction, `F₀` by hypothesis — so the supremum is attained along the rationals and
the statistic is a countable supremum of measurable functions. -/
theorem measurable_ksStat {n : ℕ} (X : Fin n → Ω → ℝ) (F₀ : ℝ → ℝ)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: `F₀` is a c.d.f., in particular right continuous; Kolmogorov 1933
    (hF₀ : ∀ t : ℝ, Tendsto F₀ (nhdsWithin t (Set.Ioi t)) (nhds (F₀ t))) :
    Measurable (ksStat X F₀) := by
  sorry

/-! ### Level: the DKW calibration is exact -/

/-- **Level of the calibrated test.** Under the null hypothesis the test that rejects when
`Tₙ > ksThreshold α` has level `α` — nonasymptotically, at every sample size `n ≥ 1`, and
for an arbitrary (not necessarily continuous) null law.

This is the defining property of the calibration: `ksThreshold α` is exactly the point
where the uniform deviation envelope `4 · exp(−d²/8)` of `ForMathlib/DKWUniform` equals
`α`. -/
theorem ks_dkw_level {n : ℕ} {α : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F₀ : ℝ → ℝ}
    -- USER-INPUT: nondegenerate sample size; the statistic is junk at `n = 0`
    (hn : 0 < n)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Kolmogorov 1933
    (hindep : iIndepFun X P)
    -- USER-INPUT: the null hypothesis: every observation has the null law `μ₀`
    (hlaw : ∀ i, P.map (X i) = μ₀)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t) :
    P {ω | ksThreshold α < ksStat X F₀ ω} ≤ ENNReal.ofReal α := by
  sorry

/-! ### Pointwise consistency against a fixed alternative -/

/-- **Pointwise consistency of the Kolmogorov–Smirnov test.** Against any fixed
alternative `F ≠ F₀` — equivalently, any `F` at positive Kolmogorov distance from `F₀` —
the power of the calibrated test tends to one.

The classical proof runs the Glivenko–Cantelli theorem (`d_K(F̂ₙ, F) → 0` a.s., hence
`Tₙ → ∞` a.s.) together with `s_{n,1−α} → s_{1−α} < ∞`; under the calibration of this file
the second ingredient is vacuous, since the critical value is a constant. The elementary
alternative argument fixes a `t` with `F(t) ≠ F₀(t)` and observes that
`n^{1/2}[F̂ₙ(t) − F(t)]` is bounded in probability while `s − n^{1/2}[F(t) − F₀(t)] → −∞`;
that route needs only Chebyshev's inequality and is the intended formalization. -/
theorem ks_consistent {α : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    {F F₀ : ℝ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Kolmogorov 1933
    (hindep : iIndepFun X P)
    -- USER-INPUT: the alternative: every observation has law `μ`
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: `F` is the c.d.f. of the sampling law
    (hF : ∀ t : ℝ, F t = cdf μ t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternative is genuinely different from the null: `d_K(F, F₀) > 0`
    (hne : 0 < supCDFDist F F₀) :
    Tendsto
      (fun n => (P {ω | ksThreshold α < ksStat (fun i : Fin n => X (i : ℕ)) F₀ ω}).toReal)
      atTop (nhds 1) := by
  sorry

/-! ### Uniform consistency over shrinking alternatives -/

/-- **Nonasymptotic power bound.** If the sampling law is at Kolmogorov distance at least
`ε / n^{1/2}` from the null, then the calibrated test rejects with probability at least
`1 − 4 exp(−(ε − s)²/8)`, where `s = ksThreshold α`.

This is the calibrated form of the classical nonasymptotic bound
`P{Tₙ > s} ≥ 1 − 2 exp(−2(ε − s)²)`, with the same hypothesis `s < ε` and the constants of
the sibling brick in place of the sharp ones (documented deviation; see the module
docstring). Both come from the same two lines: the triangle inequality
`d_K(F, F₀) ≤ d_K(F, F̂ₙ) + d_K(F̂ₙ, F₀)` turns the event `n^{1/2} d_K(F̂ₙ, F) < ε − s`
into a rejection, and the deviation inequality bounds its complement. -/
theorem ks_power_lower_bound {n : ℕ} {α ε : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F F₀ : ℝ → ℝ}
    -- USER-INPUT: nondegenerate sample size; the statistic is junk at `n = 0`
    (hn : 0 < n)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Dvoretzky–Kiefer–Wolfowitz 1956
    (hindep : iIndepFun X P)
    -- USER-INPUT: the alternative: every observation has law `μ`
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: `F` is the c.d.f. of the sampling law
    (hF : ∀ t : ℝ, F t = cdf μ t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternative is at distance `≥ ε/√n` from the null
    (hfar : ε ≤ Real.sqrt (n : ℝ) * supCDFDist F F₀)
    -- USER-INPUT: the separation exceeds the critical value (classical `εₙ > s_{n,1−α}`)
    (hgap : ksThreshold α < ε) :
    ENNReal.ofReal (1 - 4 * Real.exp (-((ε - ksThreshold α) ^ 2) / 8))
      ≤ P {ω | ksThreshold α < ksStat X F₀ ω} := by
  sorry

/-- **Uniform consistency in power.** The power of the calibrated Kolmogorov–Smirnov test
tends to one uniformly over the alternatives `F` with `n^{1/2} d_K(F, F₀) ≥ εₙ`, whenever
`εₙ → ∞`.

Stated in sequence form (see the module docstring): the classical infimum over the class
of admissible alternatives at stage `n` is replaced by an arbitrary selection `μ n` of
sampling laws satisfying the constraint, carried by a triangular array `X n` of
observations. Specialising to a constant selection recovers uniform consistency over
`d_K(F, F₀) ≥ ϵ` for each fixed `ϵ > 0`. -/
theorem ks_uniform_power {α : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → ℝ} {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F : ℕ → ℝ → ℝ} {F₀ : ℝ → ℝ} {ε : ℕ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Kolmogorov 1933
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every observation has law `μ n`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = μ n)
    -- USER-INPUT: `F n` is the c.d.f. of the stage-`n` sampling law
    (hF : ∀ n, ∀ t : ℝ, F n t = cdf (μ n) t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the stage-`n` alternative satisfies `n^{1/2} d_K(Fₙ, F₀) ≥ εₙ`
    (hfar : ∀ n, ε n ≤ Real.sqrt (n : ℝ) * supCDFDist (F n) F₀)
    -- USER-INPUT: the separation diverges: `εₙ → ∞`
    (hε : Tendsto ε atTop atTop) :
    Tendsto (fun n => ((P n) {ω | ksThreshold α < ksStat (X n) F₀ ω}).toReal)
      atTop (nhds 1) := by
  sorry

end StatLean.HypothesisTesting
