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

**Reference.** Classical limit theory for triangular arrays; original sources in the
bibliographic comments below.

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

open Complex in
/-- **The analytic core of the Lindeberg CLT.** Under the Lindeberg hypotheses the product
of the row characteristic functions converges pointwise to the standard-normal
characteristic function `t ↦ exp(−t²/2)`. This is the content of Lindeberg's
swapping/telescoping estimate; `lindeberg_clt` merely feeds this pointwise statement through
Lévy's continuity theorem.

TODO: assemble the swapping estimate. The quantitative pointwise remainder bound
`‖e^{iy} − (1 + iy − y²/2)‖ ≤ min(|y|³/6, y²)` — the ingredient Mathlib lacked — is now
available as `norm_cexp_sub_taylor_le`. What remains is the classical assembly on top of it:
(1) telescoping `‖∏ᵢ φₙᵢ − ∏ᵢ (1 − t²σₙᵢ²/2)‖ ≤ ∑ᵢ ‖φₙᵢ − (1 − t²σₙᵢ²/2)‖`, valid once the
row is uniformly negligible so every factor has modulus ≤ 1; (2) the per-term bound
`‖φₙᵢ − (1 − t²σₙᵢ²/2)‖ ≤ E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]` via `norm_cexp_sub_taylor_le` and
centering; (3) the split at `|Xₙᵢ| = ε` (small part `≤ |t|³ε ∑ᵢ σₙᵢ²/6`, large part
`≤ t² ∑ᵢ E[Xₙᵢ² 1{|Xₙᵢ|>ε}]` — the Lindeberg sum, which `hlin` sends to 0); and (4)
`∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²/2)` from `hvar`, uniform negligibility (a consequence of `hlin`)
and `log(1 − u) = −u + O(u²)`. -/
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
  sorry

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
  sorry

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
common random-variable representation. -/
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
  sorry

end StatLean.HypothesisTesting
