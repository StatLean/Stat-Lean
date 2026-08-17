import StatLean.RobustStatistics.LocationScale.Median
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import Mathlib.Probability.Variance

/-!
# The median-of-means estimator — sub-Gaussian deviation under two moments

The median-of-means estimator (`LM §2.1`; going back to Nemirovsky–Yudin (1983),
Jerrum–Valiant–Vazirani (1986) and Alon–Matias–Szegedy (1999)) partitions the sample
into `k` blocks of size `m`, averages within each block, and takes the (low) median of
the block means. Its deviation is *sub-Gaussian* under nothing but a finite variance
(`LM Theorem 2`): each block mean is within `σ√(4/m)` of `μ` with probability `≥ 3/4`
(Chebyshev), so the median misses only if at least `k/2` blocks do — a binomial tail
event of probability `≤ e^{−k/8}` (Hoeffding).

* `medianOfMeans` — `sampleMedian` of the `k` blockwise `sampleMean`s.
* `abs_medianOfMeans_sub_le_of_majority` — the deterministic median step: if strictly
  more than `k/2` block means lie within `a` of `μ₀`, so does the median-of-means.
* `iIndepFun_blockMean` — block means of jointly independent data are independent.
* `medianOfMeans_deviation` — `LM Theorem 2`, exponential form.
* `medianOfMeans_subGaussian` — `LM Theorem 2`, `k = ⌈8 log(1/δ)⌉` corollary.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.1, Theorem 2. The median step reuses Round-1's `sampleMedian` counting API;
the binomial tail is `ConcentrationInequalities.hoeffding` on indicator variables
(bounded, hence sub-Gaussian by `isSubGaussian_of_mem_Icc`).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **The median-of-means estimator** (`LM §2.1`): partition the data into `k` blocks of
`m` observations each (the data is presented already blocked, `x j i` = observation `i`
of block `j`), average within blocks, and take the median of the block means. The median
is Round-1's low `sampleMedian`, which satisfies LM's defining property ("at least `k/2`
of the values on each side"); for `k = 0` both `sampleMedian` and this estimator are the
junk value `0`. -/
noncomputable def medianOfMeans {k m : ℕ} (x : Fin k → Fin m → ℝ) : ℝ :=
  sampleMedian (fun j => sampleMean (x j))

/-- **The deterministic median step** (`LM Theorem 2` proof, the counting display): if
strictly more than `k/2` of the block means lie in `[μ₀ − a, μ₀ + a]`, then so does the
median-of-means. Strict majority in ℕ is written `k < 2 * card`. -/
theorem abs_medianOfMeans_sub_le_of_majority {k m : ℕ} (hk : k ≠ 0)
    (x : Fin k → Fin m → ℝ) {μ₀ a : ℝ}
    (hmaj : k < 2 * (Finset.univ.filter
      fun j => |sampleMean (x j) - μ₀| ≤ a).card) :
    |medianOfMeans x - μ₀| ≤ a := by
  sorry

/-- **Block means of independent data are independent** (`LM Theorem 2` proof,
implicit): if the doubly-indexed family is jointly independent, the `k` blockwise sample
means are jointly independent, each being a function of its own block's coordinates. -/
theorem iIndepFun_blockMean {k m : ℕ} {X : Fin k → Fin m → Ξ → ℝ}
    -- LEAN-ONLY: coordinate measurability, to compose independence; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n = k·m observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob) :
    iIndepFun (fun j ξ => sampleMean (fun i => X j i ξ)) μprob := by
  sorry

/-- **Median-of-means is sub-Gaussian, exponential form** (`LM Theorem 2`, first
display): for i.i.d. data with mean `μ₀` and variance `σ²`, arranged in `k` blocks of
size `m`,

  `P( |μ̂ − μ₀| > σ√(4/m) ) ≤ exp(−k/8)`.

Chebyshev puts each block mean within `σ√(4/m)` with probability `≥ 3/4`; missing the
band is an independent Bernoulli event of parameter `≤ 1/4` per block, and the median
misses only if at least `k/2` blocks do (Hoeffding's inequality on the indicators). -/
theorem medianOfMeans_deviation {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → ℝ} {μ₀ σ2 : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n = k·m observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Theorem 2 ("identically distributed")
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 2 ("with variance σ²")
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nondegenerate variance (σ = 0 makes the band trivial); LM Theorem 2
    (hσ : 0 < σ2) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt (4 / m)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      ≤ Real.exp (-(k : ℝ) / 8) := by
  sorry

/-- **Median-of-means is sub-Gaussian, confidence form** (`LM Theorem 2`, "in
particular"): choosing `k = ⌈8 log(1/δ)⌉` blocks, with probability at least `1 − δ`,

  `|μ̂ − μ₀| ≤ σ √((32 log(1/δ) + 4)/n)`.

**Constant note.** LM state the radius as `σ√(32 log(1/δ)/n)`, silently absorbing the
ceiling: with `k = ⌈8 log(1/δ)⌉ ≤ 8 log(1/δ) + 1` the provable radius is
`σ√(4k/n) ≤ σ√((32 log(1/δ) + 4)/n)`, and the `+4` cannot be dropped unless
`8 log(1/δ)` is an integer. We state the provable constant (project constants policy). -/
theorem medianOfMeans_subGaussian {k m n : ℕ} (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → ℝ} {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Theorem 2
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 2
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    (hσ : 0 < σ2)
    -- USER-INPUT: confidence level; LM Theorem 2
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: sample size and block count; LM Theorem 2 ("n = mk",
    -- "k = ⌈8 log(1/δ)⌉")
    (hn : n = k * m) (hkc : k = ⌈8 * Real.log (1 / δ)⌉₊) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt ((32 * Real.log (1 / δ) + 4) / n)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      ≤ δ := by
  sorry

end StatLean.RobustStatistics
