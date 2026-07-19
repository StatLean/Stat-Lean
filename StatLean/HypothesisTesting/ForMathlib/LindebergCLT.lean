import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib

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
    TendstoInDistribution (fun n ω => ∑ i, X n i ω) atTop Z (fun _ => P) P' := by
  sorry

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
  sorry

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
