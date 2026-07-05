import StatLean.ConcentrationInequalities.Orlicz.SumNorm
import StatLean.ConcentrationInequalities.Orlicz.Triangle
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Sub-Gaussian random vectors

A random vector $X$ in $\mathbb{R}^n$ is *sub-Gaussian* if every
one-dimensional marginal $\langle X, v\rangle$ is a sub-Gaussian random
variable; its norm is
$$ \|X\|_{\psi_2} \;=\; \sup_{v \in S^{n-1}} \|\langle X, v\rangle\|_{\psi_2}. $$
For independent mean-zero coordinates (Lemma 3.4.2),
$$ \max_i \|X_i\|_{\psi_2} \;\le\; \|X\|_{\psi_2}
   \;\le\; \sqrt{18}\, \max_i \|X_i\|_{\psi_2}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §3.4, Definition 3.4.1 and Lemma 3.4.2.

**Proof formalization notes.** Carrier `EuclideanSpace ℝ (Fin n)`; the norm
is a `⨆` of `ℝ≥0∞`-numbers over the unit sphere — a supremum of *numbers*,
so the batch's E-sup measurability policy is not triggered. Constants:
Lemma 3.4.2's lower bound holds with constant `1` (coordinate directions
`EuclideanSpace.single i 1`); the upper bound is frozen at `C = √18 = 3√2`
(formula: B3 ∘ B2 through `subGaussianNorm_weighted_sum_le` at
`∑ vᵢ² = ‖v‖² = 1`; book's absolute `C`). Work-item single named-sorry
fallback: `subGaussianVecNorm_le_of_indep` (Lemma 3.4.2 upper — the
inner-product/sphere plumbing); the definitions, the lower bound, and the
marginal predicate lemmas must close.

**Bibliographic comments.** Sub-Gaussian random vectors via one-dimensional
marginals follow HDP §3.4; the idea of controlling a vector norm by
coordinate norms under independence is standard (see also
Hsu–Kakade–Zhang, "A tail inequality for quadratic forms of subgaussian
random vectors," *Electron. Commun. Probab.* 17 (2012), for the quadratic
sequel).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Sub-Gaussian vector norm** (HDP Definition 3.4.1): the supremum of the
marginal ψ₂ norms over unit directions. A `⨆` of `ℝ≥0∞` values over the
sphere — no measurability content. Edge behavior: `n = 0` gives an empty
sphere and norm `0`; a non-sub-Gaussian marginal makes the sup `⊤`. -/
noncomputable def subGaussianVecNorm {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω := by volume_tac) : ℝ≥0∞ :=
  ⨆ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ

/-- **Sub-Gaussian random vector** (HDP Definition 3.4.1): every
one-dimensional marginal is sub-Gaussian (finite marginal ψ₂ norm; stated
over all `v`, not just unit `v`, which is equivalent by homogeneity). -/
def IsSubGaussianVec {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n))
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n),
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ ≠ ⊤

/-- Unit-direction marginals are bounded by the vector norm (LEAN-ONLY:
`le_biSup`). -/
theorem subGaussianNorm_inner_le_vecNorm {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω}
    {v : EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: unit direction; HDP Def 3.4.1 (the sup runs over S^{n−1})
    (hv : ‖v‖ = 1) :
    subGaussianNorm (fun ω => ⟪X ω, v⟫) μ ≤ subGaussianVecNorm X μ := by
  sorry

/-- Coordinate marginals are bounded by the vector norm (HDP Lemma 3.4.2,
lower bound, constant `1`; direction `EuclideanSpace.single i 1`). -/
theorem subGaussianNorm_coord_le_vecNorm {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} (i : Fin n) :
    subGaussianNorm (fun ω => X ω i) μ ≤ subGaussianVecNorm X μ := by sorry

/-- Finite-dimensional marginal criterion (LEAN-ONLY: expand
`⟪X, v⟫ = ∑ vᵢ Xᵢ` and use the finset-sum triangle inequality +
homogeneity from `Orlicz/Triangle.lean`/`Orlicz/Basic.lean`). -/
theorem isSubGaussianVec_of_coords {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurable coordinates; triangle-lemma regularity
    (hmeas : ∀ i, AEMeasurable (fun ω => X ω i) μ)
    -- USER-INPUT: sub-Gaussian coordinates; HDP Def 3.4.1 discussion
    (h : ∀ i, subGaussianNorm (fun ω => X ω i) μ ≠ ⊤) :
    IsSubGaussianVec X μ := by sorry

/-- **Lemma 3.4.2, upper bound** (HDP §3.4; frozen constant `√18 = 3√2`,
formula B3∘B2 via `subGaussianNorm_weighted_sum_le` at `‖v‖ = 1`): for
independent mean-zero coordinates with uniform ψ₂ bound `K`,
`‖X‖_{ψ₂} ≤ √18 · K`. This work item's single named-sorry fallback. -/
theorem subGaussianVecNorm_le_of_indep
    {μ : Measure Ω}
    -- LEAN-ONLY: probability measure (bridge B2/B3 requirement)
    [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    -- LEAN-ONLY: positive bound (mild strengthening, see module notes)
    (hK : 0 < K)
    -- LEAN-ONLY: measurable coordinates
    (hmeas : ∀ i, Measurable (fun ω => X ω i))
    -- USER-INPUT: independent coordinates; HDP Lemma 3.4.2
    (hindep : ProbabilityTheory.iIndepFun (fun i ω => X ω i) μ)
    -- USER-INPUT: mean-zero coordinates; HDP Lemma 3.4.2
    (hmean : ∀ i, ∫ x, X x i ∂μ = 0)
    -- USER-INPUT: uniform coordinate ψ₂ bound; HDP Lemma 3.4.2
    (hnorm : ∀ i, subGaussianNorm (fun ω => X ω i) μ ≤ K) :
    subGaussianVecNorm X μ ≤ (NNReal.sqrt 18 * K : ℝ≥0∞) := by sorry

/-- Lemma 3.4.2 statement packaging: the coordinate-max lower bound as a
finite `⨆` (HDP §3.4). -/
theorem max_coord_le_subGaussianVecNorm {n : ℕ} [NeZero n]
    {X : Ω → EuclideanSpace ℝ (Fin n)} {μ : Measure Ω} :
    (⨆ i : Fin n, subGaussianNorm (fun ω => X ω i) μ) ≤
      subGaussianVecNorm X μ := by sorry

end StatLean.ConcentrationInequalities
