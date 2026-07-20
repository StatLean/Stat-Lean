import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT
import Mathlib.Probability.HasLawExists

/-!
# Pearson's chi-squared statistic for a simple multinomial null

`n` independent trials, each resulting in one of `k + 1` outcomes, outcome `j` occurring
with probability `pⱼ`. Writing `Yⱼ` for the number of trials resulting in outcome `j`, the
vector `(Y₁, …, Y_{k+1})` is multinomial. For the simple null `pⱼ = πⱼ`, the classical
statistic rejects for large values of
$$ Q_n \;=\; \sum_{j=1}^{k+1} \frac{(Y_j - n\pi_j)^2}{n\pi_j}. $$
This file fixes the cell counts and the statistic, and states the three asymptotic facts
about it:

* `multinomialCount`, `pearsonQ` — the cell counts `Yⱼ` and the statistic `Qₙ`;
* `pearsonQ_weakConverges_chiSquared` — under the null, `Qₙ ⇒ χ²_k`;
* `pearsonQ_weakConverges_noncentral` — under the local alternatives
  `p⁽ⁿ⁾ⱼ = πⱼ + hⱼ n^{-1/2}` with `∑ⱼ hⱼ = 0`, `Qₙ ⇒ χ²_k(λ)` with `λ = ∑ⱼ hⱼ²/πⱼ`;
* `pearsonQ_consistent` — against a fixed alternative `p ≠ π` the power tends to one;
* `pearsonQ_local_power_nondegenerate` — against the local alternatives with some `hⱼ ≠ 0`
  the power tends to a limit strictly between `α` and `1`.

The degrees of freedom are `k`, one less than the number of cells `k + 1`: the counts are
constrained by `∑ⱼ Yⱼ = n`, so only `k` of the centred and scaled cell frequencies are
free. Correspondingly, the noncentrality parameter is a sum over all `k + 1` cells, of the
squared local shifts standardized by the null cell probabilities.

**Reference.** Classical goodness-of-fit theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* `multinomialCount` and `pearsonQ` are defined directly on categorical observations
  `X : Fin n → Ω → Fin (k+1)` rather than on a multinomial random vector: the counts are
  then genuine functions of the sample, the multinomial law is a consequence of
  independence rather than an assumption, and independence enters as `iIndepFun` exactly
  as in the other sampling models of the area.
* Cell probabilities are recorded as `((μ) {j}).toReal = πⱼ`, i.e. through the law of a
  single observation; this keeps the null and the local alternatives in one and the same
  format and avoids carrying a multinomial p.m.f. as data.
* The null hypothesis `π` is required to have all cells strictly positive (`0 < πⱼ`) —
  the "interior point" condition. It is genuinely needed: `Qₙ` divides by `nπⱼ`, and the
  limiting covariance matrix is singular without it.
* Convergence in law is `AsymptoticStatistics.WeakConverges` applied to the pushforwards
  of the stage-`n` sampling laws under the statistic, matching the convention of that
  area's `ForMathlib/Contiguity.lean`.
* The intended proof of the first two items is the multivariate central limit theorem
  (`ProbabilityTheory.tendstoInDistribution_multivariate_clt`) applied to the vector of
  the first `k` centred cell frequencies, followed by the continuous mapping theorem for
  the quadratic form with matrix `Σ⁻¹`; the algebraic identity that this quadratic form
  equals `Qₙ` (which reintroduces the `(k+1)`-st cell) is the only combinatorial step.
* The third item is the law of large numbers: if `pⱼ ≠ πⱼ` for some `j` then
  `Qₙ ≥ n (Yⱼ/n − πⱼ)²/πⱼ → ∞` in probability.
* `noncentralChiSquared` of `ForMathlib/NoncentralChiSquared.lean` takes its noncentrality
  parameter in `ℝ≥0`, while `multinomialNoncentrality` is a real sum; the two are joined
  by `Real.toNNReal`, which is the identity here because all `πⱼ > 0` makes the sum
  nonnegative.

**Bibliographic comments.** The statistic and the chi-squared approximation to its null
distribution are due to K. Pearson ("On the criterion that a given system of deviations
from the probable in the case of a correlated system of variables is such that it can be
reasonably supposed to have arisen from random sampling," *Philosophical Magazine*,
Series 5, **50** (1900), 157–175). The noncentral chi-squared limit under local
alternatives, and the resulting local power calculation, go back to R. A. Fisher
("The conditions under which χ² measures the discrepancy between observation and
hypothesis," *J. Roy. Statist. Soc.* **87** (1924), 442–450) and to
E. S. Pearson ("The probability integral transformation for testing goodness of fit and
combining independent tests of significance," *Biometrika* **30** (1938), 134–148); the
modern treatment via the multivariate central limit theorem is standard.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators Matrix RealInnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The cell counts and Pearson's statistic -/

/-- The **multinomial cell count** `Yⱼ = #{ i : Xᵢ = j }`: the number of the `n` trials
resulting in outcome `j`, for categorical observations taking values in the `k + 1`
outcomes `Fin (k+1)`. -/
noncomputable def multinomialCount {n k : ℕ} (X : Fin n → Ω → Fin (k + 1))
    (j : Fin (k + 1)) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun i => X i ω = j).card

/-- **Pearson's chi-squared statistic**
`Qₙ = ∑_{j=1}^{k+1} (Yⱼ − nπⱼ)² / (nπⱼ)` for the simple null `p = π`, where `Yⱼ` are the
cell counts of the sample `X`. Degenerate cells (`πⱼ = 0`) or an empty sample (`n = 0`)
produce division by zero, i.e. the junk value `0` in that summand; every statement below
assumes `0 < n` and `0 < πⱼ` for all `j`. -/
noncomputable def pearsonQ {n k : ℕ} (π : Fin (k + 1) → ℝ) (X : Fin n → Ω → Fin (k + 1))
    (ω : Ω) : ℝ :=
  ∑ j : Fin (k + 1), ((multinomialCount X j ω : ℝ) - (n : ℝ) * π j) ^ 2 / ((n : ℝ) * π j)

/-- The **noncentrality parameter** attached to a local shift `h` of the cell
probabilities: `λ = ∑_{j=1}^{k+1} hⱼ² / πⱼ`. This is `|I^{1/2}(π) h|²` for the multinomial
information matrix, which is why it is the noncentrality of the limiting law. -/
noncomputable def multinomialNoncentrality {k : ℕ} (π h : Fin (k + 1) → ℝ) : ℝ :=
  ∑ j : Fin (k + 1), (h j) ^ 2 / π j

/-! ### Algebraic core: reduction to the first `k` cells

The proof drops the last cell and works with the first `k` centred, scaled cell
frequencies `reducedVec`.  The `(k+1)`-st cell is reconstructed from the linear constraint
`∑ⱼ (Yⱼ − nπⱼ) = 0`, which is the algebraic content of `pearsonQ_eq_reducedQ` below:
Pearson's `Qₙ` equals the reduced quadratic form `reducedQ`, a sum over the first `k` cells
plus a single term standing in for the dropped cell.  The matrix realisation of `reducedQ`
as `⟪z, Σ⁻¹ z⟫` (Sherman–Morrison) is `reducedQ_eq_quadForm`. -/

/-- The number of trials is the sum of the cell counts (partition of `Fin n` by outcome). -/
private lemma sum_multinomialCount {n k : ℕ} (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    ∑ j : Fin (k + 1), multinomialCount X j ω = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin (k + 1))))
    (f := fun i => X i ω) (fun i _ => Finset.mem_univ _)
  simpa [multinomialCount, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The centred cell frequencies sum to zero: this is the linear constraint that makes the
limiting covariance singular and lets the last cell be reconstructed from the first `k`. -/
private lemma sum_centered_eq_zero {n k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπsum : ∑ j, π j = 1) (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    ∑ j : Fin (k + 1), ((multinomialCount X j ω : ℝ) - (n : ℝ) * π j) = 0 := by
  have hcount : (∑ j : Fin (k + 1), (multinomialCount X j ω : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_sum, sum_multinomialCount]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hπsum, mul_one, hcount, sub_self]

/-- The reduced quadratic form: a sum over the first `k` cells plus one term for the dropped
cell (reconstructed via the linear constraint). -/
private noncomputable def reducedQ {k : ℕ} (π : Fin (k + 1) → ℝ) (z : Fin k → ℝ) : ℝ :=
  (∑ i : Fin k, z i ^ 2 / π i.castSucc) + (∑ i : Fin k, z i) ^ 2 / π (Fin.last k)

/-- The first `k` centred, scaled cell frequencies `(Yⱼ − nπⱼ)/√n`, `j < k`. -/
private noncomputable def reducedVec {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) (i : Fin k) : ℝ :=
  ((multinomialCount X i.castSucc ω : ℝ) - (n : ℝ) * π i.castSucc) / Real.sqrt n

/-- **The combinatorial step.** Pearson's statistic equals the reduced quadratic form of the
first `k` centred frequencies; the dropped `(k+1)`-st cell reappears through the constraint
`∑ⱼ (Yⱼ − nπⱼ) = 0`.  Holds for every `n` (both sides are the junk value `0` when `n = 0`). -/
private lemma pearsonQ_eq_reducedQ {n k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπsum : ∑ j, π j = 1) (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    pearsonQ π X ω = reducedQ π (reducedVec π X ω) := by
  -- the square-and-divide identity `(c/√n)² / p = c² / (n p)`
  have hsq : ∀ (c p : ℝ), (c / Real.sqrt n) ^ 2 / p = c ^ 2 / ((n : ℝ) * p) := by
    intro c p
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_div]
  -- the reconstruction: `∑_{i<k} (Y_{i} − nπ_{i}) = − (Y_last − nπ_last)`
  have hlast : (∑ i : Fin k, ((multinomialCount X i.castSucc ω : ℝ) - (n : ℝ) * π i.castSucc))
      = - ((multinomialCount X (Fin.last k) ω : ℝ) - (n : ℝ) * π (Fin.last k)) := by
    have h0 := sum_centered_eq_zero hπsum X ω
    rw [Fin.sum_univ_castSucc] at h0
    linarith [h0]
  rw [pearsonQ, reducedQ]
  simp only [reducedVec]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsq]
  · rw [← Finset.sum_div, hsq, hlast, neg_sq]

/-- **The noncentrality identity.** The multinomial noncentrality `∑ⱼ hⱼ²/πⱼ` equals the
reduced quadratic form of the first `k` drift components; the dropped cell reappears via the
constraint `∑ⱼ hⱼ = 0`. This is `pearsonQ_eq_reducedQ` for the drift `h` in place of the
centred counts. -/
private lemma multinomialNoncentrality_eq_reducedQ {k : ℕ} {π h : Fin (k + 1) → ℝ}
    (hhsum : ∑ j, h j = 0) :
    multinomialNoncentrality π h = reducedQ π (fun i => h i.castSucc) := by
  rw [multinomialNoncentrality, reducedQ, Fin.sum_univ_castSucc]
  have hlast : (∑ i : Fin k, h i.castSucc) = - h (Fin.last k) := by
    have := hhsum; rw [Fin.sum_univ_castSucc] at this; linarith
  congr 1
  rw [hlast, neg_sq]

/-- The reduced `k × k` covariance `Σ = diag(π') − π' π'ᵀ` of the first `k` cell
frequencies (`π' j = π j.castSucc`). It is `PosDef` (`reducedCov_posDef`), unlike the full
`(k+1)`-dimensional covariance which is singular. -/
private noncomputable def reducedCov {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    (if i = j then π i.castSucc else 0) - π i.castSucc * π j.castSucc

/-- The Sherman–Morrison inverse of `reducedCov`: `Σ⁻¹ = diag(1/π') + (1/π_{k}) 𝟙 𝟙ᵀ`. -/
private noncomputable def reducedCovInv {k : ℕ} (π : Fin (k + 1) → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    (if i = j then (π i.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹

/-- The action of `Σ⁻¹` on a vector: `(Σ⁻¹ z)_i = z_i/π_i + (∑_j z_j)/π_{k}`. -/
private lemma reducedCovInv_mulVec {k : ℕ} {π : Fin (k + 1) → ℝ} (z : Fin k → ℝ) (i : Fin k) :
    (reducedCovInv π *ᵥ z) i
      = (π i.castSucc)⁻¹ * z i + (π (Fin.last k))⁻¹ * ∑ j, z j := by
  simp only [reducedCovInv, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have h : ∀ j : Fin k,
      ((if i = j then (π i.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹) * z j
        = (if i = j then (π i.castSucc)⁻¹ * z j else 0) + (π (Fin.last k))⁻¹ * z j := by
    intro j
    by_cases hij : i = j
    · simp only [if_pos hij, add_mul]
    · simp only [if_neg hij, zero_add, add_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => (π i.castSucc)⁻¹ * z j), ← Finset.mul_sum]
  simp

/-- **The quadratic form.** `z ⬝ᵥ Σ⁻¹ z = reducedQ π z`. -/
private lemma dotProduct_reducedCovInv {k : ℕ} {π : Fin (k + 1) → ℝ} (z : Fin k → ℝ) :
    z ⬝ᵥ (reducedCovInv π) *ᵥ z = reducedQ π z := by
  rw [reducedQ]
  simp only [dotProduct]
  simp_rw [reducedCovInv_mulVec, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv]; ring)
  · rw [← Finset.sum_mul, div_eq_mul_inv]; ring

/-- **Sherman–Morrison.** `Σ · Σ⁻¹ = 1`.  The cancellation uses `π_{k} = 1 − ∑_{j<k} π_j`
(the last cell probability), i.e. the null-probability normalisation. -/
private lemma reducedCov_mul_inv {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    reducedCov π * reducedCovInv π = 1 := by
  have hlne : π (Fin.last k) ≠ 0 := (hπpos _).ne'
  ext i l
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [reducedCov, reducedCovInv, Matrix.of_apply]
  have step : ∀ j : Fin k,
      (((if i = j then π i.castSucc else 0) - π i.castSucc * π j.castSucc) *
        ((if j = l then (π j.castSucc)⁻¹ else 0) + (π (Fin.last k))⁻¹))
      = (if i = j then (if j = l then (1 : ℝ) else 0) else 0)
        + (if i = j then π i.castSucc * (π (Fin.last k))⁻¹ else 0)
        - (if j = l then π i.castSucc else 0)
        - π i.castSucc * π j.castSucc * (π (Fin.last k))⁻¹ := by
    intro j
    have hj : π j.castSucc ≠ 0 := (hπpos _).ne'
    split_ifs <;> subst_vars <;> field_simp <;> ring
  rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun j => if j = l then (1 : ℝ) else 0),
    Finset.sum_ite_eq Finset.univ i (fun _ => π i.castSucc * (π (Fin.last k))⁻¹),
    Finset.sum_ite_eq' Finset.univ l (fun _ => π i.castSucc)]
  simp only [Finset.mem_univ, if_true]
  have hD : (∑ j : Fin k, π i.castSucc * π j.castSucc * (π (Fin.last k))⁻¹)
      = π i.castSucc * (π (Fin.last k))⁻¹ * ∑ j : Fin k, π j.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  have hs : (∑ j : Fin k, π j.castSucc) = 1 - π (Fin.last k) := by
    have := hπsum; rw [Fin.sum_univ_castSucc] at this; linarith
  rw [hD, hs]
  have hz : π i.castSucc * (π (Fin.last k))⁻¹ - π i.castSucc
      - π i.castSucc * (π (Fin.last k))⁻¹ * (1 - π (Fin.last k)) = 0 := by
    field_simp; ring
  linear_combination hz

/-- `Σ⁻¹` is positive definite (`∑ z_i²/π_i + (∑ z_i)²/π_{k} > 0` for `z ≠ 0`). -/
private lemma reducedCovInv_posDef {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) : (reducedCovInv π).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, reducedCovInv, Matrix.of_apply, star_trivial]
    by_cases h : i = j <;> simp [h, eq_comm]
  · intro x hx
    rw [star_trivial, dotProduct_reducedCovInv, reducedQ]
    have hA : 0 < ∑ i : Fin k, x i ^ 2 / π i.castSucc := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · exact div_nonneg (sq_nonneg _) (hπpos _).le
      · exact div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))) (hπpos _)
    have hB : 0 ≤ (∑ i : Fin k, x i) ^ 2 / π (Fin.last k) :=
      div_nonneg (sq_nonneg _) (hπpos _).le
    linarith

/-- `Σ = reducedCov` is positive definite (inverse of the `PosDef` matrix `Σ⁻¹`). -/
private lemma reducedCov_posDef {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) : (reducedCov π).PosDef := by
  have hinv : (reducedCovInv π)⁻¹ = reducedCov π :=
    Matrix.inv_eq_left_inv (reducedCov_mul_inv hπpos hπsum)
  rw [← hinv]
  exact (reducedCovInv_posDef hπpos).inv

/-- `Σ⁻¹ = reducedCovInv` as matrices. -/
private lemma reducedCov_inv_eq {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    (reducedCov π)⁻¹ = reducedCovInv π :=
  Matrix.inv_eq_right_inv (reducedCov_mul_inv hπpos hπsum)

/-- The cell count as a real-valued measurable function of the sample. -/
private lemma measurable_multinomialCount {n k : ℕ} {X : Fin n → Ω → Fin (k + 1)}
    (hX : ∀ i, Measurable (X i)) (j : Fin (k + 1)) :
    Measurable (fun ω => (multinomialCount X j ω : ℝ)) := by
  classical
  have hrw : (fun ω => (multinomialCount X j ω : ℝ))
      = fun ω => ∑ i : Fin n, if X i ω = j then (1 : ℝ) else 0 := by
    funext ω
    rw [multinomialCount, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => by by_cases h : X i ω = j <;> simp [h])
  rw [hrw]
  refine Finset.univ.measurable_sum (fun i _ => ?_)
  exact Measurable.ite ((hX i) (measurableSet_singleton j)) measurable_const measurable_const

/-- The standardised reduced cell-count vector `((Yⱼ − nπⱼ)/√n)_{j<k}` as an element of
`EuclideanSpace ℝ (Fin k)`; the object the multivariate CLT is applied to. -/
private noncomputable def reducedCount {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (reducedVec π X ω)

private lemma measurable_reducedCount {n k : ℕ} {π : Fin (k + 1) → ℝ}
    {X : Fin n → Ω → Fin (k + 1)} (hX : ∀ i, Measurable (X i)) :
    Measurable (reducedCount π X) := by
  have hg : Measurable (fun ω => reducedVec π X ω) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    simp only [reducedVec]
    exact ((measurable_multinomialCount hX i.castSucc).sub measurable_const).div measurable_const
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp hg

/-! #### The canonical i.i.d. transfer

We realise `reducedCount` as the standardised sum of the centred per-observation indicator
vectors `g x = indicatorVec x − piVec π`, transfer the per-stage law to the canonical
infinite-product i.i.d. model (via `iIndepFun_iff_map_fun_eq_pi_map`), and apply the
reusable fixed-i.i.d. CLT `clt_finDim`. -/

/-- The cell count as a real-valued sum of indicators. -/
private lemma multinomialCount_cast_eq_sum {n k : ℕ} (X : Fin n → Ω → Fin (k + 1))
    (j : Fin (k + 1)) (ω : Ω) :
    (multinomialCount X j ω : ℝ) = ∑ i : Fin n, if X i ω = j then (1 : ℝ) else 0 := by
  classical
  rw [multinomialCount, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : X i ω = j <;> simp [h])

/-- The per-observation indicator vector in the reduced space:
`(indicatorVec x)_i = 1[x = i.castSucc]`. -/
private noncomputable def indicatorVec {k : ℕ} (x : Fin (k + 1)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => if x = i.castSucc then (1 : ℝ) else 0)

/-- The reduced null-probability vector `(piVec π)_i = π i.castSucc`. -/
private noncomputable def piVec {k : ℕ} (π : Fin (k + 1) → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => π i.castSucc)

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_euclidean_eq_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The centred indicator vector `g x = indicatorVec x − piVec π` paired with a direction
`u`, in coordinate form. -/
private lemma inner_u_g {k : ℕ} (π : Fin (k + 1) → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : Fin (k + 1)) :
    ⟪u, indicatorVec x - piVec π⟫
      = ∑ i, u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc) := by
  rw [inner_euclidean_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

/-- The `∑_x π_x 1[x = i.castSucc] = π i.castSucc` pick identity. -/
private lemma sum_pi_ite_castSucc {k : ℕ} (π : Fin (k + 1) → ℝ) (i : Fin k) :
    ∑ x : Fin (k + 1), π x * (if x = i.castSucc then (1 : ℝ) else 0) = π i.castSucc := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i.castSucc (fun x => π x)]
  simp

/-- The `∑_x π_x 1[x = i.cs] 1[x = j.cs] = δ_{ij} π i.castSucc` product-pick identity. -/
private lemma sum_pi_ite_ite {k : ℕ} (π : Fin (k + 1) → ℝ) (i j : Fin k) :
    ∑ x : Fin (k + 1),
        π x * ((if x = i.castSucc then (1 : ℝ) else 0) * (if x = j.castSucc then 1 else 0))
      = if i = j then π i.castSucc else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hx : ∀ x : Fin (k + 1),
        π x * ((if x = i.castSucc then (1 : ℝ) else 0) * (if x = i.castSucc then 1 else 0))
          = π x * (if x = i.castSucc then 1 else 0) := by
      intro x; by_cases hx : x = i.castSucc <;> simp [hx]
    simp_rw [hx]; exact sum_pi_ite_castSucc π i
  · rw [if_neg hij]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hxi : x = i.castSucc
    · by_cases hxj : x = j.castSucc
      · exact absurd (Fin.castSucc_injective k (hxi.symm.trans hxj)) hij
      · simp [hxj]
    · simp [hxi]

/-- The covariance-entry integral: `∑_x π_x (b_i − π'_i)(b_j − π'_j) = reducedCov π i j`. -/
private lemma sum_pi_center_prod {k : ℕ} (π : Fin (k + 1) → ℝ) (hπsum : ∑ j, π j = 1)
    (i j : Fin k) :
    ∑ x : Fin (k + 1),
        π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
          * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
      = reducedCov π i j := by
  have hexp : ∀ x : Fin (k + 1),
      π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
          * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
        = π x * ((if x = i.castSucc then 1 else 0) * (if x = j.castSucc then 1 else 0))
          - π j.castSucc * (π x * (if x = i.castSucc then 1 else 0))
          - π i.castSucc * (π x * (if x = j.castSucc then 1 else 0))
          + π i.castSucc * π j.castSucc * π x := by
    intro x; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_pi_ite_ite, ← Finset.mul_sum, sum_pi_ite_castSucc, ← Finset.mul_sum, sum_pi_ite_castSucc,
    ← Finset.mul_sum, hπsum]
  simp only [reducedCov, Matrix.of_apply]
  ring

/-- `reducedCount` is the standardised sum of the centred per-observation indicator vectors. -/
private lemma reducedCount_eq_smul_sum {n k : ℕ} (π : Fin (k + 1) → ℝ)
    (X : Fin n → Ω → Fin (k + 1)) (ω : Ω) :
    reducedCount π X ω
      = (Real.sqrt n)⁻¹ • ∑ i : Fin n, (indicatorVec (X i ω) - piVec π) := by
  classical
  rw [reducedCount]
  simp only [indicatorVec, piVec]
  simp_rw [← WithLp.toLp_sub]
  rw [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  refine congrArg (WithLp.toLp 2) ?_
  funext j
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [reducedVec, multinomialCount_cast_eq_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_eq_inv_mul]

/-- **Multivariate CLT for the reduced cell frequencies** (the single deep analytic brick of
the null-limit proof). The standardised reduced count vector converges in law to the centred
Gaussian with the reduced covariance `Σ = diag π' − π' π'ᵀ`.

The proof realises `reducedCount` as the standardised sum of the centred per-observation
indicator vectors `g x = indicatorVec x − piVec π` (`reducedCount_eq_smul_sum`), transfers the
per-stage law to the canonical infinite-product i.i.d. model produced by
`ProbabilityTheory.exists_iid` (matching both sequences to `(Measure.pi …).map` via
`iIndepFun_iff_map_fun_eq_pi_map`), and applies the reusable fixed-i.i.d. CLT
`AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`. The covariance side-condition
`∫ ⟪u, g⟫⟪v, g⟫ = u ⬝ᵥ Σ v` is the finite computation `sum_pi_center_prod`, and the zero-mean
side-condition is `sum_pi_ite_castSucc`. -/
private lemma reducedCount_weakConverges_gaussian {k : ℕ} {π : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, Measure.map (X n i) (P n) = μ)
    (hcell : ∀ j, (μ {j}).toReal = π j) :
    WeakConverges (fun n => (P n).map (reducedCount π (X n)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (reducedCov π)) := by
  classical
  -- `μ` is the common observation law, a probability measure.
  haveI hP1prob : IsProbabilityMeasure (P 1) := ‹∀ n, IsProbabilityMeasure (P n)› 1
  haveI hμprob : IsProbabilityMeasure μ := by
    rw [← hlaw 1 0]
    exact Measure.isProbabilityMeasure_map (μ := P 1) (hX 1 0).aemeasurable
  -- the canonical i.i.d. model `(Ω₀, P₀, Z)` with marginal law `μ`
  obtain ⟨Ω₀, mΩ₀, P₀, Z, hZmeas, hZlaw, hZindep, hP₀prob⟩ :=
    ProbabilityTheory.exists_iid ℕ μ
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀ := hP₀prob
  -- centred per-observation indicator map `g` and per-observation vectors `Y`
  set g : Fin (k + 1) → EuclideanSpace ℝ (Fin k) := fun x => indicatorVec x - piVec π with hg
  have hgmeas : Measurable g := (measurable_of_finite indicatorVec).sub measurable_const
  set Y : ℕ → Ω₀ → EuclideanSpace ℝ (Fin k) := fun i ω => g (Z i ω) with hY
  -- an integral of `F ∘ Z 0` reduces to a finite `π`-weighted sum
  have hkey : ∀ (F : Fin (k + 1) → ℝ), ∫ ω, F (Z 0 ω) ∂P₀ = ∑ x, π x * F x := by
    intro F
    have hFmeas : Measurable F := measurable_of_finite F
    rw [show (∫ ω, F (Z 0 ω) ∂P₀) = ∫ x, F x ∂(P₀.map (Z 0)) from
          (integral_map (hZmeas 0).aemeasurable hFmeas.aestronglyMeasurable).symm,
        (hZlaw 0).map_eq, integral_fintype (f := F) Integrable.of_finite]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [MeasureTheory.Measure.real, hcell x, smul_eq_mul]
  -- inputs to `clt_finDim`
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hgmeas.comp (hZmeas i)
  have hYindep : iIndepFun Y P₀ := hZindep.comp (fun _ => g) (fun _ => hgmeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P₀ P₀ := fun i =>
    (show IdentDistrib (Z i) (Z 0) P₀ P₀ from
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp hgmeas
  -- the centred indicators have zero mean
  have h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫ ∂P₀ = 0 := by
    intro u
    have hint : (∫ ω, ⟪u, Y 0 ω⟫ ∂P₀) = ∑ x, π x * ⟪u, g x⟫ := hkey (fun x => ⟪u, g x⟫)
    rw [hint]
    simp_rw [hg, inner_u_g, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hterm : ∀ x : Fin (k + 1),
        π x * (u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc))
          = u i * (π x * (if x = i.castSucc then 1 else 0)) - u i * π i.castSucc * π x := by
      intro x; ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_pi_ite_castSucc, ← Finset.mul_sum, hπsum]
    ring
  -- the covariance identity `∫ ⟪u,·⟫⟪v,·⟫ = u ⬝ Σ v`
  have h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P₀ = u.ofLp ⬝ᵥ (reducedCov π).mulVec v.ofLp := by
    intro u v
    have hRHS : u.ofLp ⬝ᵥ (reducedCov π).mulVec v.ofLp
        = ∑ i, ∑ j, (u i * v j) * reducedCov π i j := by
      simp only [dotProduct, Matrix.mulVec]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show u i * (reducedCov π i j * v j) = (u i * v j) * reducedCov π i j
      ring
    have hint : (∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P₀) = ∑ x, π x * (⟪u, g x⟫ * ⟪v, g x⟫) :=
      hkey (fun x => ⟪u, g x⟫ * ⟪v, g x⟫)
    rw [hint, hRHS]
    simp_rw [hg, inner_u_g, Finset.sum_mul_sum]
    have hswap : ∀ x : Fin (k + 1),
        π x * ∑ i, ∑ j, (u i * ((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc))
              * (v j * ((if x = j.castSucc then 1 else 0) - π j.castSucc))
          = ∑ i, ∑ j, (u i * v j)
              * (π x * (((if x = i.castSucc then (1 : ℝ) else 0) - π i.castSucc)
                  * ((if x = j.castSucc then 1 else 0) - π j.castSucc))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp_rw [hswap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, sum_pi_center_prod π hπsum i j]
  -- the centred indicators are square-integrable (bounded, factoring through a finite type)
  have h_L2 : MemLp (Y 0) 2 P₀ := by
    obtain ⟨C, hC⟩ := (Set.finite_range (fun x => ‖g x‖)).bddAbove
    have hbd : ∀ ω, ‖Y 0 ω‖ ≤ C := fun ω => hC ⟨Z 0 ω, rfl⟩
    exact (memLp_top_of_bound (hYmeas 0).aestronglyMeasurable C
      (Filter.Eventually.of_forall hbd)).mono_exponent le_top
  -- the fixed-i.i.d. CLT for the canonical model
  have hclt := AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim
    P₀ Y hYmeas hYindep hYident h_zero_mean (reducedCov π)
    (reducedCov_posDef hπpos hπsum).posSemidef h_cov h_L2
  -- the canonical standardised sum has, at each `n`, the same law as `reducedCount`
  have hmatch : ∀ n : ℕ,
      P₀.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = (P n).map (reducedCount π (X n)) := by
    intro n
    set F : (Fin n → Fin (k + 1)) → EuclideanSpace ℝ (Fin k) :=
      fun d => (Real.sqrt n)⁻¹ • ∑ i : Fin n, g (d i) with hF
    have hFmeas : Measurable F := measurable_of_finite F
    have hgZ : Measurable (fun ω (i : Fin n) => Z (i : ℕ) ω) :=
      measurable_pi_lambda _ (fun i => hZmeas i)
    have hgX : Measurable (fun ω (i : Fin n) => X n i ω) :=
      measurable_pi_lambda _ (fun i => hX n i)
    have hLHSfun : (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = F ∘ (fun ω (i : Fin n) => Z (i : ℕ) ω) := by
      funext ω
      simp only [hF, hY, Function.comp]
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (Z i ω)) n]
    have hRHSfun : reducedCount π (X n) = F ∘ (fun ω (i : Fin n) => X n i ω) := by
      funext ω
      rw [reducedCount_eq_smul_sum π (X n) ω]
      simp only [hF, hg, Function.comp]
    have hpiZ : P₀.map (fun ω (i : Fin n) => Z (i : ℕ) ω) = Measure.pi (fun _ : Fin n => μ) := by
      have hsub : iIndepFun (fun (i : Fin n) => Z (i : ℕ)) P₀ :=
        hZindep.precomp Fin.val_injective
      rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) => Z (i : ℕ))
        (fun i => (hZmeas (i : ℕ)).aemeasurable)).1 hsub]
      congr 1; funext i; exact (hZlaw (i : ℕ)).map_eq
    have hpiX : (P n).map (fun ω (i : Fin n) => X n i ω) = Measure.pi (fun _ : Fin n => μ) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n)]
      congr 1; funext i; exact hlaw n i
    rw [hLHSfun, hRHSfun, ← Measure.map_map hFmeas hgZ, ← Measure.map_map hFmeas hgX,
      hpiZ, hpiX]
  simp only [hmatch] at hclt
  exact hclt

/-- **Null limiting distribution.** Under the simple null hypothesis `pⱼ = πⱼ` for
`j = 1, …, k+1`, Pearson's statistic converges in law to the chi-squared distribution with
`k` degrees of freedom. -/
theorem pearsonQ_weakConverges_chiSquared {k : ℕ} {π : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom; `χ²₀` is degenerate
    (hk : 0 < k)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at every stage every trial has the common law `μ`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ)
    -- USER-INPUT: the null hypothesis: the cell probabilities of `μ` are `π`
    (hcell : ∀ j, (μ {j}).toReal = π j) :
    WeakConverges (fun n => Measure.map (pearsonQ π (X n)) (P n)) (chiSquared k) := by
  -- the continuous quadratic form `q z = ⟪z, Σ⁻¹ z⟫`
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  -- pointwise: `q (reducedCount ω) = pearsonQ ω` (bridge algebra)
  have hq : ∀ n ω, q (reducedCount π (X n) ω) = pearsonQ π (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, pearsonQ_eq_reducedQ hπsum,
      ← dotProduct_reducedCovInv]
    rfl
  -- the lifted CLT brick, then continuous mapping
  have hbrick := reducedCount_weakConverges_gaussian (π := π) (P := P) (X := X) (μ := μ)
    hπpos hπsum hX hindep hlaw hcell
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  -- the target is `χ²_k` (Gaussian → chi-squared bridge)
  have htarget : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (reducedCov π)).map q
      = chiSquared k := by
    simp only [hqdef, hTdef]
    exact multivariateGaussian_map_inner_inv_eq_chiSquared hk (reducedCov_posDef hπpos hπsum)
  -- each pushforward term equals the law of `pearsonQ`
  have hseq : (fun n => ((P n).map (reducedCount π (X n))).map q)
      = fun n => Measure.map (pearsonQ π (X n)) (P n) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_reducedCount (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

/-! ### (ii) Local alternatives and the noncentral limit -/

/-- **Multivariate CLT for the reduced cell frequencies under local alternatives** (LIFTED —
the deep analytic brick of the noncentral-limit proof). Under `p⁽ⁿ⁾ = π + h/√n` the
standardised reduced count vector converges in law to `N(ν, Σ)` with drift
`ν = (hⱼ)_{j<k}` and covariance `Σ = reducedCov π`.

TODO: unlike the null case this is a *triangular array* — the per-observation law `μ n`
drifts with `n` — so the fixed-i.i.d. brick `tendstoInDistribution_multivariate_clt` does
not apply directly. The intended route is a multivariate Lindeberg / Cramér–Wold CLT (the
repo has the scalar `HypothesisTesting.ForMathlib.LindebergCLT.lindeberg_clt`), or Le Cam's
third lemma (`AsymptoticStatistics.ForMathlib.Contiguity`), plus the same canonical transfer
as `reducedCount_weakConverges_gaussian`. The drift `ν = hⱼ` is the limit of
`E[reducedCount]ⱼ = (n p⁽ⁿ⁾ⱼ − nπⱼ)/√n = hⱼ`, and `Σ → diag π − π πᵀ` since `p⁽ⁿ⁾ → π`. -/
private lemma reducedCount_weakConverges_noncentral {k : ℕ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) (hhsum : ∑ j, h j = 0)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, Measure.map (X n i) (P n) = μ n)
    (hcell : ∀ n j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    WeakConverges (fun n => (P n).map (reducedCount π (X n)))
      (multivariateGaussian (WithLp.toLp 2 (fun i => h i.castSucc)) (reducedCov π)) := by
  sorry

/-- **Limiting distribution under local alternatives.** Under the alternative sequence
`p⁽ⁿ⁾ⱼ = πⱼ + hⱼ n^{-1/2}` with `∑_{j=1}^{k+1} hⱼ = 0`, Pearson's statistic converges in
law to the noncentral chi-squared distribution with `k` degrees of freedom and
noncentrality parameter
$$ \lambda \;=\; \sum_{j=1}^{k+1} \frac{h_j^2}{\pi_j}. $$
The constraint `∑ⱼ hⱼ = 0` is what makes `p⁽ⁿ⁾` a probability vector; positivity of the
perturbed cells is assumed separately, since it fails for small `n` when some `hⱼ < 0`. -/
theorem pearsonQ_weakConverges_noncentral {k : ℕ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: the local shifts sum to zero, so the perturbed vector is a probability
    -- vector
    (hhsum : ∑ j, h j = 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every trial has the stage-`n` law `μ n`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ n)
    -- USER-INPUT: the local alternative: the stage-`n` cell probabilities are
    -- `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n, ∀ j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    WeakConverges (fun n => Measure.map (pearsonQ π (X n)) (P n))
      (noncentralChiSquared k (multinomialNoncentrality π h).toNNReal) := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  have hq : ∀ n ω, q (reducedCount π (X n) ω) = pearsonQ π (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, pearsonQ_eq_reducedQ hπsum,
      ← dotProduct_reducedCovInv]
    rfl
  have hbrick := reducedCount_weakConverges_noncentral (π := π) (h := h) (P := P) (X := X) (μ := μ)
    hπpos hπsum hhsum hX hindep hlaw hcell
  set ν : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i => h i.castSucc) with hνdef
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  have hnc_id : (⟪ν, Matrix.toEuclideanCLM (𝕜 := ℝ) (reducedCov π)⁻¹ ν⟫ : ℝ)
      = multinomialNoncentrality π h := by
    rw [Matrix.inner_toEuclideanCLM, reducedCov_inv_eq hπpos hπsum, dotProduct_reducedCovInv,
      hνdef]
    exact (multinomialNoncentrality_eq_reducedQ hhsum).symm
  have htarget : (multivariateGaussian ν (reducedCov π)).map q
      = noncentralChiSquared k (multinomialNoncentrality π h).toNNReal := by
    simp only [hqdef, hTdef]
    rw [multivariateGaussian_map_inner_inv_eq_noncentralChiSquared
      (reducedCov_posDef hπpos hπsum) ν, hnc_id]
  have hseq : (fun n => ((P n).map (reducedCount π (X n))).map q)
      = fun n => Measure.map (pearsonQ π (X n)) (P n) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_reducedCount (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

/-! ### (iii) Power -/

/-- **Consistency against a fixed alternative.** If the true cell probabilities differ
from `π` in at least one cell, the power of the chi-squared test tends to one. The reason
is that `Qₙ ≥ n (Yⱼ/n − πⱼ)²/πⱼ` for the offending cell `j`, and `Yⱼ/n → pⱼ ≠ πⱼ` in
probability by the law of large numbers, so `Qₙ → ∞` in probability. -/
theorem pearsonQ_consistent {k : ℕ} {α c : ℝ} {π p : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at every stage every trial has the common alternative law `μ`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ)
    -- USER-INPUT: the alternative cell probabilities of `μ` are `p`
    (hcell : ∀ j, (μ {j}).toReal = p j)
    -- USER-INPUT: the alternative genuinely differs from the null in some cell
    (hne : ∃ j, p j ≠ π j) :
    Tendsto (fun n => ((P n) {ω | c < pearsonQ π (X n) ω}).toReal) atTop (nhds 1) := by
  -- TODO (planned debt): consistency is a law-of-large-numbers argument, not a CLT one, so
  -- neither supplied brick applies. The intended proof:
  --   (1) a WLLN for the offending cell frequency `Yⱼ/n → pⱼ` in `P n`-probability (an
  --       offending `j` with `pⱼ ≠ πⱼ` exists by `hne`); the repo's
  --       `HypothesisTesting.ForMathlib.LindebergCLT.triangular_wlln_of_L1` or a direct
  --       Chebyshev bound on the Bernoulli indicators `1[Xᵢ = j]` supplies it;
  --   (2) the one-summand lower bound `pearsonQ π (X n) ω ≥ n (Yⱼ/n − πⱼ)²/πⱼ` (drop the
  --       other nonnegative summands), whence `pearsonQ → ∞` in `P n`-probability and
  --       therefore `P n {ω | c < pearsonQ} → 1` for the fixed critical value `c`.
  sorry

/-- **Nondegenerate local power.** Against the local alternatives of
`pearsonQ_weakConverges_noncentral` with not all `hⱼ` equal to zero, the power of the
chi-squared test tends to a limit strictly greater than `α` and strictly less than one,
namely `P{χ²_k(λ) > c}` with `λ = ∑ⱼ hⱼ²/πⱼ > 0`. -/
theorem pearsonQ_local_power_nondegenerate {k : ℕ} {α c : ℝ} {π h : Fin (k + 1) → ℝ}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {μ : ℕ → Measure (Fin (k + 1))}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: the local shifts sum to zero
    (hhsum : ∑ j, h j = 0)
    -- USER-INPUT: the local alternative is nondegenerate: not all shifts vanish
    (hhne : ∃ j, h j ≠ 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every trial has the stage-`n` law `μ n`
    (hlaw : ∀ n, ∀ i, Measure.map (X n i) (P n) = μ n)
    -- USER-INPUT: the local alternative cell probabilities are `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n, ∀ j, ((μ n) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    Tendsto (fun n => ((P n) {ω | c < pearsonQ π (X n) ω}).toReal) atTop
        (nhds ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal)
      ∧ α < ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal
      ∧ ((noncentralChiSquared k (multinomialNoncentrality π h).toNNReal)
          (Set.Ioi c)).toReal < 1 := by
  -- TODO (planned debt): the three conjuncts build on `pearsonQ_weakConverges_noncentral`
  -- (ii) but need analytic facts about the limit that are not among the supplied bricks:
  --   (1) a portmanteau step upgrading the weak limit (ii) to convergence of the tail
  --       probability `((P n).map pearsonQ)(Ioi c) → noncentralChiSquared k λ (Ioi c)`,
  --       valid because `{c}` is `noncentralChiSquared`-null (absolute continuity); the
  --       `WeakConverges` API in `ForMathlib.Contiguity` has no such continuity-set lemma;
  --   (2) `α < tail` is STRICT: `chiSquared_tail_le_noncentralChiSquared` gives only `≤`;
  --       strictness needs `λ = multinomialNoncentrality π h > 0` (from `hhne` + `hπpos`,
  --       provable) together with STRICT monotonicity of `l ↦ noncentralChiSquared k l (Ioi c)`
  --       at `l > 0` — only the non-strict `noncentralChiSquared_tail_mono` is imported;
  --   (3) `tail < 1`: `noncentralChiSquared` is absolutely continuous with support `(0,∞)`,
  --       so `Iic c` carries positive mass for the finite `c` fixed by `hc` (`0 < α < 1`).
  sorry

end StatLean.HypothesisTesting
