import StatLean.RobustStatistics.Core.Contamination
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance

/-!
# The sub-Gaussian deviation rate is optimal — no estimator beats `σ√(log(1/δ)/n)`

The minimax counterpart of the estimators in this directory (`LM Theorem 1`, after
Devroye–Lerasle–Lugosi–Oliveira (2016)): for *any* mean estimator there is a
finite-variance distribution on which its deviation at confidence `δ` is at least
`σ√(log(1/δ)/n)`. The witness family is a two-point pair `P₊, P₋` placing mass `p` at
`±c` and `1 − p` at `0` — built here from Round-1's `contaminate` applied to Dirac
masses — coupled so that the two samples agree with probability `(1−p)ⁿ ≥ 2δ`; on that
event no estimator can be simultaneously close to both means `±pc`.

* `twoPointPM` and its mean/variance.
* `twoPointCoupling` — the joint law on `ℝ × ℝ`, its marginals, and the diagonal mass.
* `agree_pow` — the samples agree with probability `(1 − p)ⁿ`.
* `mean_estimator_deviation_lower` — `LM Theorem 1`.

**Honest reading of the statement.** LM phrase the conclusion "there exists a
distribution with mean `μ` and variance `σ²`"; the two exhibited distributions have
means `±pc`, so the centering in the deviation event is the exhibited distribution's
*own* mean (the pair cannot share it), and the free centering `μ` of LM's phrasing is
recovered by translating the whole construction. We state the translation-fixed form.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2, Theorem 1; after L. Devroye, M. Lerasle, G. Lugosi and R. I. Oliveira,
*Sub-Gaussian mean estimators*, Ann. Statist. 44 (2016).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

/-- **The two-point distribution** `P_c,p{c} = p`, `P_c,p{0} = 1 − p` (`LM Theorem 1`
proof): Round-1's `contaminate` of a Dirac mass at `0` by a Dirac mass at `c`. -/
noncomputable def twoPointPM (c p : ℝ) : Measure ℝ :=
  contaminate (Measure.dirac 0) (Measure.dirac c) p

/-- The two-point law is a probability measure for `p ∈ [0, 1]` — Round-1's
`isProbabilityMeasure_contaminate` applied to two Dirac masses. -/
theorem isProbabilityMeasure_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPointPM c p) :=
  isProbabilityMeasure_contaminate _ _ hp0 hp1

/-- Mean of the two-point distribution: `∫ x dP_{c,p} = pc` (`LM Theorem 1` proof,
"the means of the two distributions are ±pc"). -/
theorem integral_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, x ∂twoPointPM c p = p * c := by
  rw [twoPointPM, integral_contaminate hp0 hp1 (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  ring

/-- Variance of the two-point distribution: `σ² = c²p(1 − p)` (`LM Theorem 1` proof). -/
theorem variance_twoPointPM {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ x, (x - p * c) ^ 2 ∂twoPointPM c p = c ^ 2 * p * (1 - p) := by
  rw [twoPointPM, integral_contaminate hp0 hp1 (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness)), integral_dirac, integral_dirac]
  ring

/-- **The coupling** (`LM Theorem 1` proof): the joint law of a pair `(X, Y)` with
`P(X = Y = 0) = 1 − p` and `P(X = c, Y = −c) = p`. -/
noncomputable def twoPointCoupling (c p : ℝ) : Measure (ℝ × ℝ) :=
  contaminate (Measure.dirac ((0 : ℝ), (0 : ℝ))) (Measure.dirac (c, -c)) p

/-- The first marginal of the coupling is `P₊ = P_{c,p}`. -/
theorem twoPointCoupling_fst {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoPointCoupling c p).map Prod.fst = twoPointPM c p := by
  rw [twoPointCoupling, map_contaminate measurable_fst, Measure.map_dirac' measurable_fst,
    Measure.map_dirac' measurable_fst, twoPointPM]

/-- The second marginal of the coupling is `P₋ = P_{−c,p}`. -/
theorem twoPointCoupling_snd {c p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (twoPointCoupling c p).map Prod.snd = twoPointPM (-c) p := by
  rw [twoPointCoupling, map_contaminate measurable_snd, Measure.map_dirac' measurable_snd,
    Measure.map_dirac' measurable_snd, twoPointPM]

/-- **The coupled samples agree with probability `(1 − p)ⁿ`** (`LM Theorem 1` proof,
`P{X₁ⁿ = Y₁ⁿ} = (1 − p)ⁿ`): under the `n`-fold product of the coupling, all coordinate
pairs are equal exactly when every pair drew its `(0,0)` atom. Requires `c ≠ 0` (else
the atoms coincide and the probability is `1`). -/
theorem twoPointCoupling_agree_pow {c p : ℝ} (hc : c ≠ 0) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) :
    (Measure.pi fun _ : Fin n => twoPointCoupling c p).real
        {w | ∀ i, (w i).1 = (w i).2}
      = (1 - p) ^ n := by
  haveI : IsProbabilityMeasure (twoPointCoupling c p) :=
    isProbabilityMeasure_contaminate _ _ hp0 hp1
  have hD : MeasurableSet {q : ℝ × ℝ | q.1 = q.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hset : {w : Fin n → ℝ × ℝ | ∀ i, (w i).1 = (w i).2}
      = Set.univ.pi fun _ : Fin n => {q : ℝ × ℝ | q.1 = q.2} := by
    ext w; simp [Set.mem_pi]
  have hcc : ((c, -c) : ℝ × ℝ) ∉ {q : ℝ × ℝ | q.1 = q.2} := by
    intro h
    simp only [Set.mem_setOf_eq] at h
    exact hc (by linarith)
  have hν : twoPointCoupling c p {q : ℝ × ℝ | q.1 = q.2} = ENNReal.ofReal (1 - p) := by
    rw [twoPointCoupling, contaminate_apply, Measure.dirac_apply' _ hD,
      Measure.dirac_apply' _ hD, Set.indicator_of_mem (by simp) _,
      Set.indicator_of_notMem hcc]
    simp
  rw [measureReal_def, hset, Measure.pi_pi]
  simp only [hν, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 - p)]
  exact ENNReal.toReal_ofReal (pow_nonneg (by linarith) n)

/-- **No mean estimator beats the sub-Gaussian rate** (`LM Theorem 1`): for every
sample size `n > 5`, confidence `δ ∈ (2e^{−n/4}, 1/2)`, target variance `σ² > 0`, and
*any* measurable estimator `μ̂ : (Fin n → ℝ) → ℝ`, there is a probability distribution
`P` with variance `σ²` whose own mean `μ_P` satisfies

  `Pⁿ( |μ̂ − μ_P| > σ√(log(1/δ)/n) ) ≥ δ`.

The witness is one of the coupled two-point pair with `p = log(2/δ)/(2n)` and
`c = σ/√(p(1−p))`; the agreement event has probability `≥ 2δ` and forces one of the two
means — which are `2pc ≥ 2σ√(p/2)` apart — to be missed. -/
theorem mean_estimator_deviation_lower {n : ℕ} (hn : 5 < n) {δ σ2 : ℝ}
    -- USER-INPUT: confidence window; LM Theorem 1 (`δ ∈ (2e^{−n/4}, 1/2)`)
    (hδlo : 2 * Real.exp (-(n : ℝ) / 4) < δ) (hδhi : δ < 1 / 2)
    -- USER-INPUT: nondegenerate variance; LM Theorem 1 (`σ > 0`)
    (hσ : 0 < σ2)
    -- USER-INPUT: the estimator, an arbitrary statistic of the sample; LM §2
    (μhat : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the estimator, for the deviation event
    (hμhat : Measurable μhat) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
      (∫ x, (x - ∫ y, y ∂P) ^ 2 ∂P = σ2) ∧
      δ ≤ (Measure.pi fun _ : Fin n => P).real
        {x | Real.sqrt σ2 * Real.sqrt (Real.log (1 / δ) / n)
          < |μhat x - ∫ y, y ∂P|} := by
  sorry

end StatLean.RobustStatistics
