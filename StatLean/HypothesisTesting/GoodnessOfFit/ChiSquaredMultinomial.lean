import StatLean.HypothesisTesting.Tests.Defs
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT

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
open scoped ENNReal BigOperators Matrix

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
  sorry

/-! ### (ii) Local alternatives and the noncentral limit -/

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
  sorry

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
  sorry

end StatLean.HypothesisTesting
