import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.Anderson
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Independence.Basic

/-!
# The noncentral chi-squared distribution

The **noncentral chi-squared law** with `k` degrees of freedom and noncentrality parameter
`λ ≥ 0` is the law of the squared norm of a `k`-dimensional Gaussian vector with identity
covariance whose mean has squared length `λ`:
$$\chi^2_k(\lambda) \;=\; \mathcal L\bigl(\|Z + \mu\|^2\bigr), \qquad
  Z \sim N(0, I_k),\quad \|\mu\|^2 = \lambda .$$
It is the limiting law of quadratic-form goodness-of-fit statistics under local
alternatives, and the whole asymptotic power theory of such tests is a statement about the
function `λ ↦ χ²_k(λ)((c, ∞))`.

We take as the definition the pushforward of `multivariateGaussian` under `z ↦ ‖z‖²`, with
the mean placed on the first coordinate axis; that the direction of the mean is irrelevant
is `map_normSq_multivariateGaussian_of_norm_eq`, which is what licenses calling `λ` "the"
noncentrality parameter.

## Main results

* `noncentralChiSquared` — the definition, and `noncentralChiSquared_zero` identifying
  `λ = 0` with the central chi-squared law already in the library.
* `map_normSq_multivariateGaussian_of_norm_eq` — direction invariance: any mean vector of
  squared length `λ` produces the same law.
* `chiSquared_tail_le_noncentralChiSquared`, `noncentralChiSquared_tail_mono` — the upper
  tail is at least the central one, and increases with the noncentrality parameter.
* `weakConverges_chiSquared_standardized`,
  `tendsto_chiSquared_quantile_standardized`,
  `weakConverges_noncentralChiSquared_standardized` — the large-`k` normalisations:
  `(χ²_k − k)/√(2k) ⇝ N(0,1)`, the matching convergence of standardised upper quantiles,
  and the noncentral version with a drift.

**Reference.** Classical distribution theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* Edge cases of the definition. For `k = 0` the ambient space is a single point, so
  `noncentralChiSquared 0 λ = δ₀` for every `λ`; the bridge to the library's central
  `chiSquared` therefore requires `0 < k` (the library's `chiSquared 0` is the degenerate
  `Gamma(0, 1/2)`, not `δ₀`). The mean vector is built by an `if (i : ℕ) = 0` test rather
  than `EuclideanSpace.single`, so that no inhabitant of `Fin k` is needed and `k = 0`
  elaborates.
* The covariance is the identity matrix `(1 : Matrix (Fin k) (Fin k) ℝ)`, which is positive
  semidefinite, so the degenerate `multivariateGaussian` branch is never taken.
* `noncentralChiSquared_zero` reduces, via `multivariateGaussian_zero_one`, to the
  library's exact sum-of-squares law for i.i.d. standard normals.
* Tail comparison with the central law is the set form of Anderson's inequality
  (`AsymptoticStatistics.anderson_lemma_set` in the asymptotics area): closed balls are
  convex and symmetric, so shifting the Gaussian away from the origin can only decrease the
  ball probability, i.e. only increase the complementary upper tail.
* Full monotonicity in `λ` is *not* a direct corollary of that set form (which compares a
  shift with no shift). The route is a one-dimensional reduction: by direction invariance
  and independence of the coordinates, `χ²_k(h²)` is the law of `(Z₁ + h)² + W` with `W`
  independent of `Z₁`; conditionally on `W`, the map `h ↦ P((Z₁ + h)² ≤ s)` is
  nonincreasing in `|h|` because the standard normal density is symmetric and unimodal and
  `{z : z² ≤ s}` is a symmetric interval. Integrating over `W` gives the claim.
* Large-`k` statements use the project's measure-level weak-convergence predicate
  `AsymptoticStatistics.WeakConverges` (indexed by the degrees of freedom, which is the
  quantity going to infinity here); no random-variable representation is needed. Junk
  values at `k = 0` are irrelevant to an `atTop` statement.
* In the quantile statement the upper-`α` quantiles `c k` and `z` are supplied as data
  together with their defining tail identities, rather than through a quantile
  construction; `α ∈ (0,1)` is then forced by those identities and is not assumed.

**Bibliographic comments.** The noncentral chi-squared distribution appears in R. A. Fisher,
"The general sampling distribution of the multiple correlation coefficient," *Proc. Roy.
Soc. A* **121** (1928), 654–673; its systematic study and tabulation are due to
P. B. Patnaik, "The non-central χ²- and F-distributions and their applications,"
*Biometrika* **36** (1949), 202–232. The role of the central chi-squared law in
goodness-of-fit testing originates with K. Pearson, "On the criterion that a given system
of deviations from the probable in the case of a correlated system of variables is such
that it can be reasonably supposed to have arisen from random sampling," *Phil. Mag.* **50**
(1900), 157–175. The monotonicity of the tail in the noncentrality parameter rests on
T. W. Anderson, "The integral of a symmetric unimodal function over a symmetric convex set
and some probability inequalities," *Proc. Amer. Math. Soc.* **6** (1955), 170–176.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace StatLean.HypothesisTesting

/-- The mean vector used to define the noncentral chi-squared law: the vector of squared
length `l` supported on the first coordinate. For `k = 0` this is the unique point of the
zero-dimensional space. -/
noncomputable def noncentralMean (k : ℕ) (l : ℝ≥0) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => if (i : ℕ) = 0 then Real.sqrt (l : ℝ) else 0

/-- The **noncentral chi-squared distribution** with `k` degrees of freedom and
noncentrality parameter `l`: the law of `‖Z‖²` for `Z ∼ N(μ, I_k)` with `‖μ‖² = l`.

Edge behaviour: for `k = 0` the ambient space is a point and the law is `δ₀` for every `l`;
for `l = 0` it is the central chi-squared law (`noncentralChiSquared_zero`, for `0 < k`). -/
noncomputable def noncentralChiSquared (k : ℕ) (l : ℝ≥0) : Measure ℝ :=
  (multivariateGaussian (noncentralMean k l) 1).map fun z => ‖z‖ ^ 2

/-- With unit covariance, `multivariateGaussian` is a translate of the standard Gaussian. -/
private lemma multivariateGaussian_one_eq_map_add {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The mean vector vanishes when the noncentrality parameter is `0`. -/
@[simp] private lemma noncentralMean_zero {k : ℕ} : noncentralMean k (0 : ℝ≥0) = 0 := by
  ext i
  simp [noncentralMean]

/-- The mean vector has the prescribed length `√l` (when there is at least one coordinate). -/
private lemma noncentralMean_norm {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ‖noncentralMean k l‖ = Real.sqrt (l : ℝ) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h2 : ‖noncentralMean k l‖ ^ 2 = (l : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hval : ∀ i : Fin k,
        (noncentralMean k l i) ^ 2 = if i = 0 then (l : ℝ) else 0 := by
      intro i
      by_cases hi : i = 0
      · simp only [noncentralMean, hi, Fin.val_zero, if_pos, if_true]
        rw [Real.sq_sqrt l.coe_nonneg]
      · have hi' : (i : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hi
        simp [noncentralMean, hi, hi']
    simp_rw [hval]
    simp [Finset.sum_ite_eq']
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- Direction-invariance core: translating the standard Gaussian by mean vectors of equal
length gives the same squared-norm law. Proved with the reflection that swaps the means. -/
private lemma map_normSq_stdGaussian_add_congr {k : ℕ}
    {v w : EuclideanSpace ℝ (Fin k)} (h : ‖v‖ = ‖w‖) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖v + x‖ ^ 2)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖w + x‖ ^ 2) := by
  obtain ⟨f, hf⟩ : ∃ f : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k), f v = w :=
    ⟨_, Submodule.reflection_sub h⟩
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (f : _ → _)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := stdGaussian_map f
  symm
  calc (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖w + x‖ ^ 2)
      = ((stdGaussian (EuclideanSpace ℝ (Fin k))).map (f : _ → _)).map
          (fun x => ‖w + x‖ ^ 2) := by rw [hmap]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => ‖w + f y‖ ^ 2) := by
          rw [Measure.map_map (by fun_prop)
            (LinearIsometryEquiv.continuous f).measurable]; rfl
    _ = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => ‖v + y‖ ^ 2) := by
          have hfun : (fun y => ‖w + f y‖ ^ 2)
              = (fun y : EuclideanSpace ℝ (Fin k) => ‖v + y‖ ^ 2) := by
            funext y
            rw [← hf, ← map_add, LinearIsometryEquiv.norm_map]
          rw [hfun]

/-- The noncentral chi-squared law is a probability measure: it is the pushforward of a
Gaussian (hence probability) measure under a continuous map. -/
instance isProbabilityMeasure_noncentralChiSquared (k : ℕ) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralChiSquared k l) := by
  rw [noncentralChiSquared]
  exact Measure.isProbabilityMeasure_map
    (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2).aemeasurable

/-- **Direction invariance.** Any Gaussian mean vector whose norm is `√l` yields the same
squared-norm law, so the noncentrality parameter `l = ‖μ‖²` is a complete invariant. Follows
from the orthogonal invariance of the standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
theorem map_normSq_multivariateGaussian_of_norm_eq (k : ℕ) (l : ℝ≥0)
    {v : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the mean vector has the prescribed length.
    (hv : ‖v‖ = Real.sqrt (l : ℝ)) :
    (multivariateGaussian v 1).map (fun z => ‖z‖ ^ 2) = noncentralChiSquared k l := by
  have hnorm : ‖v‖ = ‖noncentralMean k l‖ := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Subsingleton.elim v (noncentralMean 0 l)]
    · rw [hv, noncentralMean_norm hk]
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add,
    multivariateGaussian_one_eq_map_add,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  exact map_normSq_stdGaussian_add_congr hnorm

/-- **Zero noncentrality is the central chi-squared law.** For `0 < k`,
`χ²_k(0) = χ²_k`. Via `multivariateGaussian_zero_one` the Gaussian becomes standard, its
coordinates are i.i.d. `N(0,1)`, and `‖z‖² = ∑ᵢ zᵢ²` has the central chi-squared law by the
library's sum-of-squares theorem. -/
theorem noncentralChiSquared_zero {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) :
    noncentralChiSquared k 0 = StatLean.MultipleTesting.chiSquared k := by
  haveI : NeZero k := ⟨hk.ne'⟩
  rw [noncentralChiSquared, noncentralMean_zero, multivariateGaussian_zero_one,
    ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : ((fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2) ∘ (WithLp.toLp 2))
      = (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2) := by
    funext x
    simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq]
  rw [hfun]
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared hk
    (Measure.pi fun _ => gaussianReal 0 1)
    (fun i x => x i) (fun i => measurable_pi_apply i)
    (fun i => (measurePreserving_eval _ i).map_eq)
    (iIndepFun_pi (fun _ => aemeasurable_id))

/-- **The Gaussian ↔ chi-squared bridge (noncentral case).** For a positive-definite
covariance `S` and any mean `μ`, the Gaussian quadratic form `z ↦ ⟪z, S⁻¹ z⟫` pushes
`N(μ, S)` forward to the noncentral chi-squared law with `k` degrees of freedom and
noncentrality parameter `⟪μ, S⁻¹ μ⟫`.

Proof by whitening. With `A = (√S)⁻¹` (the inverse of the positive-definite matrix square
root) one has `A · S · Aᴴ = I` and `A · A = S⁻¹`, so
`(N(μ, S)).map A = N(Aμ, I)` (`multivariateGaussian_map_toEuclideanCLM`), while
`⟪z, S⁻¹ z⟫ = ‖A z‖²` because `A` is self-adjoint and `A² = S⁻¹`. Pushing the squared norm
through the whitened Gaussian `N(Aμ, I)` gives `noncentralChiSquared k ‖Aμ‖²`, and
`‖Aμ‖² = ⟪μ, S⁻¹ μ⟫`, whose `toNNReal` is the stated noncentrality. -/
theorem multivariateGaussian_map_inner_inv_eq_noncentralChiSquared {k : ℕ}
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) (μ : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian μ S).map
        (fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
      = noncentralChiSquared k
          (⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫).toNNReal := by
  classical
  -- The whitening matrix `A = (√S)⁻¹`.
  set B : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt S with hB_def
  have hB_sa : IsSelfAdjoint B := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hB_unit : IsUnit B := hS.posDef_sqrt.isUnit
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB_unit
  have hBl : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBdet
  have hBr : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdet
  set A : Matrix (Fin k) (Fin k) ℝ := B⁻¹ with hA_def
  -- `A` is self-adjoint.
  have hA_sa : IsSelfAdjoint A := by
    show star A = A
    rw [hA_def, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
      ← Matrix.star_eq_conjTranspose, hB_sa]
  have hAH : Aᴴ = A := by rw [← Matrix.star_eq_conjTranspose]; exact hA_sa
  -- `A · A = S⁻¹`.
  have hAA : A * A = S⁻¹ := by rw [hA_def, ← Matrix.mul_inv_rev, hBB]
  -- `A · S · Aᴴ = I`.
  have hASA : A * S * Aᴴ = 1 := by
    rw [hAH, hA_def, ← hBB, Matrix.mul_assoc, Matrix.mul_assoc, hBr, Matrix.mul_one, hBl]
  -- CLM-level self-adjointness and `A ∘ A = S⁻¹`.
  have hAclSA : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) :=
    hA_sa.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hAAcl :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A) ∘L (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) A * Matrix.toEuclideanCLM (𝕜 := ℝ) A = _
    rw [← map_mul, hAA]
  -- Pointwise: `‖A z‖² = ⟪z, S⁻¹ z⟫`.
  have hnorm : ∀ z : EuclideanSpace ℝ (Fin k),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ^ 2
        = ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫ := by
    intro z
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
    have hswap :
        ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A z, Matrix.toEuclideanCLM (𝕜 := ℝ) A z⟫
          = ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) A (Matrix.toEuclideanCLM (𝕜 := ℝ) A z)⟫ := by
      have := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint_inner_right z
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A z)
      rw [hAclSA.adjoint_eq] at this
      exact this.symm
    rw [hswap]
    congr 1
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) A ∘L Matrix.toEuclideanCLM (𝕜 := ℝ) A) z = _
    rw [hAAcl]
  -- Assemble via the whitening pushforward and the squared-norm law of `N(Aμ, I)`.
  have hqnn : 0 ≤ ⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫ := by
    rw [← hnorm μ]; positivity
  have hv : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A μ‖
      = Real.sqrt ((⟪μ, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ μ⟫).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hqnn, ← hnorm μ, Real.sqrt_sq (norm_nonneg _)]
  have hcomp :
      (fun z : EuclideanSpace ℝ (Fin k) => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
        = (fun w => ‖w‖ ^ 2) ∘ (Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
    funext z; simp only [Function.comp_apply]; exact (hnorm z).symm
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    multivariateGaussian_map_toEuclideanCLM A μ hS.posSemidef, hASA]
  exact map_normSq_multivariateGaussian_of_norm_eq k _ hv

/-- **The Gaussian ↔ chi-squared bridge (central case).** For a positive-definite covariance
`S` (with `0 < k`), the Gaussian quadratic form `z ↦ ⟪z, S⁻¹ z⟫` pushes the centred Gaussian
`N(0, S)` forward to the central chi-squared law `χ²_k`. The exact distributional identity
`Zᵀ S⁻¹ Z ∼ χ²_k` for `Z ∼ N(0, S)`, the `μ = 0` specialisation of
`multivariateGaussian_map_inner_inv_eq_noncentralChiSquared`. -/
theorem multivariateGaussian_map_inner_inv_eq_chiSquared {k : ℕ} (hk : 0 < k)
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S).map
        (fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫)
      = StatLean.MultipleTesting.chiSquared k := by
  rw [multivariateGaussian_map_inner_inv_eq_noncentralChiSquared hS 0,
    show (⟪(0 : EuclideanSpace ℝ (Fin k)), Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ 0⟫).toNNReal
        = 0 from by rw [inner_zero_left]; simp]
  exact noncentralChiSquared_zero hk

/-- The upper tail of `noncentralChiSquared` as a standard-Gaussian ball-complement measure. -/
private lemma noncentralChiSquared_Ioi_eq {k : ℕ} (l : ℝ≥0) (t : ℝ) :
    noncentralChiSquared k l (Set.Ioi t)
      = stdGaussian (EuclideanSpace ℝ (Fin k))
          {x | t < ‖noncentralMean k l + x‖ ^ 2} := by
  rw [noncentralChiSquared, multivariateGaussian_one_eq_map_add,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  rfl

/-- **The noncentral upper tail dominates the central one.** Direct consequence of the set
form of Anderson's inequality applied to the closed ball `{z : ‖z‖² ≤ t}`, which is convex
and symmetric: shifting the mean can only decrease its probability. -/
theorem chiSquared_tail_le_noncentralChiSquared {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) (l : ℝ≥0) (t : ℝ) :
    (StatLean.MultipleTesting.chiSquared k) (Set.Ioi t)
      ≤ (noncentralChiSquared k l) (Set.Ioi t) := by
  rw [← noncentralChiSquared_zero hk, noncentralChiSquared_Ioi_eq,
    noncentralChiSquared_Ioi_eq, noncentralMean_zero]
  set E := EuclideanSpace ℝ (Fin k)
  set μ := stdGaussian E
  -- the closed ball `C = {z : ‖z‖² ≤ t}`, convex and symmetric
  set C : Set E := {z | ‖z‖ ^ 2 ≤ t} with hC
  have hCmeas : MeasurableSet C := by
    have : Measurable fun z : E => ‖z‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have hCconv : Convex ℝ C := by
    by_cases ht : (0 : ℝ) ≤ t
    · have hset : C = Metric.closedBall (0 : E) (Real.sqrt t) := by
        ext z
        simp only [hC, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
        constructor
        · intro h
          rw [← Real.sqrt_sq (norm_nonneg z)]
          exact Real.sqrt_le_sqrt h
        · intro h
          have hmul := mul_self_le_mul_self (norm_nonneg z) h
          rw [Real.mul_self_sqrt ht] at hmul
          rw [pow_two]; exact hmul
      rw [hset]; exact convex_closedBall _ _
    · have ht' : t < 0 := not_le.mp ht
      have hset : C = (∅ : Set E) := by
        ext z
        simp only [hC, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le ht' (sq_nonneg _)
      rw [hset]; exact convex_empty
  have hCsymm : ∀ z ∈ C, -z ∈ C := by
    intro z hz; simpa [hC] using hz
  -- both tails are complements of `{· ∈ C}` events under the standard Gaussian
  have hmeasA : MeasurableSet {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t} := by
    have : Measurable fun x : E => ‖(0 : E) + x‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have hmeasB : MeasurableSet {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := by
    have : Measurable fun x : E => ‖noncentralMean k l + x‖ ^ 2 := by fun_prop
    exact measurableSet_le this measurable_const
  have key : μ {x | noncentralMean k l + x ∈ C} ≤ μ C := by
    have hand := AsymptoticStatistics.anderson_lemma_set_stdGaussian hCmeas hCconv hCsymm
      (noncentralMean k l)
    rwa [show {x : E | x + noncentralMean k l ∈ C}
        = {x : E | noncentralMean k l + x ∈ C} from by
      ext x; simp only [Set.mem_setOf_eq]; rw [add_comm]] at hand
  have hCeq : {x : E | (0 : E) + x ∈ C} = {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t} := rfl
  have hBeq : {x : E | noncentralMean k l + x ∈ C}
      = {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t} := rfl
  have hEA : {x : E | t < ‖(0 : E) + x‖ ^ 2} = {x : E | ‖(0 : E) + x‖ ^ 2 ≤ t}ᶜ := by
    ext x; simp [not_le]
  have hEB : {x : E | t < ‖noncentralMean k l + x‖ ^ 2}
      = {x : E | ‖noncentralMean k l + x‖ ^ 2 ≤ t}ᶜ := by
    ext x; simp [not_le]
  rw [hEA, hEB, measure_compl hmeasA (measure_ne_top _ _),
    measure_compl hmeasB (measure_ne_top _ _)]
  have key' : μ {x | ‖noncentralMean k l + x‖ ^ 2 ≤ t} ≤ μ {x | ‖(0 : E) + x‖ ^ 2 ≤ t} := by
    have h0 : μ {x | (0 : E) + x ∈ C} = μ C := by
      simp
    rw [← hBeq, ← hCeq]
    calc μ {x | noncentralMean k l + x ∈ C} ≤ μ C := key
      _ = μ {x | (0 : E) + x ∈ C} := h0.symm
  exact tsub_le_tsub_left key' _

/-- **The upper tail increases with the noncentrality parameter.** The noncentral
chi-squared family is stochastically ordered in `l`. Proved by the one-dimensional
reduction described in the file header (symmetric unimodal shift inequality), Anderson's
inequality covering the special case `l = 0`. -/
theorem noncentralChiSquared_tail_mono (k : ℕ) (t : ℝ) :
    Monotone fun l : ℝ≥0 => (noncentralChiSquared k l) (Set.Ioi t) := by
  sorry

/-- **Large-`k` normalisation of the central chi-squared law.**
`(χ²_k − k)/√(2k)` converges weakly to the standard normal law as the number of degrees of
freedom grows: the chi-squared variable is a sum of `k` i.i.d. squared standard normals
with mean `1` and variance `2`, so this is the i.i.d. central limit theorem. -/
theorem weakConverges_chiSquared_standardized :
    AsymptoticStatistics.WeakConverges
      (fun k : ℕ => (StatLean.MultipleTesting.chiSquared k).map
        (fun x => (x - k) / Real.sqrt (2 * k)))
      (gaussianReal 0 1) := by
  sorry

/-- **Large-`k` normalisation of the chi-squared upper quantiles.**
If `c k` is the upper-`α` quantile of `χ²_k` and `z` the upper-`α` quantile of `N(0,1)`,
then `(c k − k)/√(2k) → z`.

Consequence of `weakConverges_chiSquared_standardized`: the limiting distribution function
is continuous and strictly increasing, so weak convergence upgrades to convergence of
quantiles. The identities also force `α ∈ (0,1)`, which is therefore not assumed. -/
theorem tendsto_chiSquared_quantile_standardized {α : ℝ} {c : ℕ → ℝ} {z : ℝ}
    -- USER-INPUT: `c k` is the upper-`α` quantile of `χ²_k` (`k ≥ 1`).
    (hc : ∀ k : ℕ, 0 < k →
      (StatLean.MultipleTesting.chiSquared k) (Set.Ioi (c k)) = ENNReal.ofReal α)
    -- USER-INPUT: `z` is the upper-`α` quantile of the standard normal law.
    (hz : (gaussianReal 0 1) (Set.Ioi z) = ENNReal.ofReal α) :
    Tendsto (fun k : ℕ => (c k - k) / Real.sqrt (2 * k)) atTop (𝓝 z) := by
  sorry

/-- **Large-`k` normalisation of the noncentral chi-squared law.**
If the noncentrality parameters satisfy `l k / √(2k) → c`, then
`(χ²_k(l k) − k)/√(2k)` converges weakly to `N(c, 1)`: writing the noncentral variable as
`(Z₁ + h)² + ∑_{i≥2} Z_i²` with `h = √(l k)`, the tail sum contributes the standard normal
limit, `h²/√(2k) → c` contributes the drift, and both `Z₁²/√(2k)` and `2hZ₁/√(2k)` vanish in
probability. Taking `l = 0` recovers the central normalisation. -/
theorem weakConverges_noncentralChiSquared_standardized {l : ℕ → ℝ≥0} {c : ℝ}
    -- USER-INPUT: the standardised noncentrality parameters converge.
    (hl : Tendsto (fun k : ℕ => (l k : ℝ) / Real.sqrt (2 * k)) atTop (𝓝 c)) :
    AsymptoticStatistics.WeakConverges
      (fun k : ℕ => (noncentralChiSquared k (l k)).map
        (fun x => (x - k) / Real.sqrt (2 * k)))
      (gaussianReal c 1) := by
  sorry

end StatLean.HypothesisTesting
