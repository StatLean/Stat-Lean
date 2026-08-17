import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Probability.Moments.Variance

/-!
# Multivariate median-of-means via minimal-radius majority balls — dimension-free

Extending median-of-means to `ℝᵈ` requires a multivariate median. The coordinate-wise
median pays a `√(Tr(Σ) log(d/δ))` price; the *minimal-radius majority ball* median of
`LM §3.2` is dimension-free: define `μ̂` as a center whose ball containing **more than
half** of the block means has minimal radius. Chebyshev in norm puts each block mean
within `r = 2√(Tr(Σ)/m)` of `μ` with probability `≥ 3/4`; on the majority event the
optimal ball has radius `≤ r`, any two majority balls share a block mean, and the
triangle inequality gives `‖μ̂ − μ‖ ≤ 2r` (`LM Proposition 1`):

  `‖μ̂ − μ‖ ≤ 4 √( Tr(Σ)(8 log(1/δ) + 1) / n )`  with probability `≥ 1 − δ`.

Here `Tr(Σ) = E‖X − μ‖²` is carried directly as the second moment. The sub-Gaussian
benchmark this should be compared against is `LM (3.1)`; the truly sub-Gaussian
median-of-means *tournament* estimator (`LM §3.4`) and the geometric median-of-means
(Minsker (2015)) are bib notes only, not formalized this round.

* `blockMeanVec`, `momCount`, `momRadius`, `IsBallMoMCenter`.
* `momRadius_le_of_majority`, `majority_of_lt_momRadius` — the `sInf` interface.
* `dist_le_of_majority_two` — two majority balls intersect (the pigeonhole).
* `norm_blockMeanVec_sq_moment` — `E‖Z_j − μ‖² = Tr(Σ)/m`.
* `ballMoM_deviation` — `LM Proposition 1`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §3.1–§3.2, display (3.1), Proposition 1.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {d : ℕ}

/-- The blockwise mean of vector observations (`LM §3.2`, `Z_j = (1/m) ∑_{i∈B_j} X_i`),
with the block structure presented as a double index. -/
noncomputable def blockMeanVec {k m : ℕ} (x : Fin k → Fin m → EuclideanSpace ℝ (Fin d))
    (j : Fin k) : EuclideanSpace ℝ (Fin d) :=
  (m : ℝ)⁻¹ • ∑ i, x j i

/-- The number of the `k` points within distance `r` of a candidate center `c`
(`LM §3.2`, "the ball centered at `μ̂` that contains more than `k/2` of the points"). -/
noncomputable def momCount {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℕ :=
  (Finset.univ.filter fun j => ‖Z j - c‖ ≤ r).card

/-- **The majority-ball radius** (`LM §3.2`): the infimum radius of a ball at `c`
containing *strictly more than half* of the points (`k < 2·count`). The defining set is
nonempty (any radius dominating all distances works) and bounded below by `0`, so the
infimum is honest; it is `0` when a strict majority of the points coincide with `c`. -/
noncomputable def momRadius {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ k < 2 * momCount Z c r}

/-- **The ball-MoM center property** (`LM §3.2`): `c` minimizes the majority-ball
radius over all candidate centers. As with all argmin estimators in this library, the
estimator is a predicate; the theorems consume any selection satisfying it. -/
def IsBallMoMCenter {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ a : EuclideanSpace ℝ (Fin d), momRadius Z c ≤ momRadius Z a

/-- If a radius `r ≥ 0` captures a strict majority, the majority-ball radius is `≤ r`. -/
theorem momRadius_le_of_majority {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 ≤ r)
    (h : k < 2 * momCount Z c r) : momRadius Z c ≤ r := by
  sorry

/-- Any radius strictly above the majority-ball radius captures a strict majority (the
count is monotone in `r`, and the infimum's defining set is upward closed). -/
theorem majority_of_lt_momRadius {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hk : k ≠ 0)
    (h : momRadius Z c < r) : k < 2 * momCount Z c r := by
  sorry

/-- **Two majority balls intersect in a data point** (`LM §3.2` proof, "at least one of
the `Z_j` is within distance `r` to both `μ` and `μ̂`"): if balls of radii `r₁, r₂` at
`c₁, c₂` each capture a strict majority, some `Z_j` lies in both, so
`‖c₁ − c₂‖ ≤ r₁ + r₂`. -/
theorem dist_le_of_majority_two {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c₁ c₂ : EuclideanSpace ℝ (Fin d)} {r₁ r₂ : ℝ}
    (h₁ : k < 2 * momCount Z c₁ r₁) (h₂ : k < 2 * momCount Z c₂ r₂) :
    ‖c₁ - c₂‖ ≤ r₁ + r₂ := by
  sorry

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]

/-- **Second moment of a block mean** (`LM §3.2` proof, `E‖Z_j − μ‖² = Tr(Σ)/m`): for a
block of `m` i.i.d. centered square-integrable vectors, the squared-norm moment of the
block mean is `trΣ/m`, where `trΣ = E‖X − μ₀‖²` is the trace of the covariance. -/
theorem norm_blockMeanVec_sq_moment {m : ℕ} (hm : m ≠ 0)
    {X : Fin m → Ξ → EuclideanSpace ℝ (Fin d)} {μ₀ : EuclideanSpace ℝ (Fin d)}
    {trΣ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §3 regularity
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent block coordinates; LM Proposition 1
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM Proposition 1
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: square-integrability, mean, and trace second moment; LM §3
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (htr : ∫ x, ‖x - μ₀‖ ^ 2 ∂P = trΣ) :
    ∫ ξ, ‖(m : ℝ)⁻¹ • (∑ i, X i ξ) - μ₀‖ ^ 2 ∂μprob = trΣ / m := by
  sorry

/-- **The minimal-radius-ball median-of-means is dimension-free** (`LM Proposition 1`):
for i.i.d. random vectors with mean `μ₀` and covariance trace `trΣ`, blocked into
`k = ⌈8 log(1/δ)⌉` blocks of size `m` with `n = km`, any measurable selection `Ĉ` of
ball-MoM centers satisfies, with probability at least `1 − δ`,

  `‖Ĉ − μ₀‖ ≤ 4 √( trΣ (8 log(1/δ) + 1) / n )`. -/
theorem ballMoM_deviation {k m n : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → EuclideanSpace ℝ (Fin d)}
    {Chat : Ξ → EuclideanSpace ℝ (Fin d)} {μ₀ : EuclideanSpace ℝ (Fin d)}
    {trΣ δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §3 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n observations are jointly independent; LM Proposition 1
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Proposition 1
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: square-integrability, mean, covariance trace; LM Proposition 1
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (htr : ∫ x, ‖x - μ₀‖ ^ 2 ∂P = trΣ) (htrpos : 0 < trΣ)
    -- USER-INPUT: confidence level and block count; LM Proposition 1
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : n = k * m)
    (hkc : k = ⌈8 * Real.log (1 / δ)⌉₊)
    -- USER-INPUT: Ĉ is a ball-MoM center of the block means, sample-wise; LM §3.2
    (hChat : ∀ ξ, IsBallMoMCenter (fun j => blockMeanVec (fun j i => X j i ξ) j)
      (Chat ξ))
    -- LEAN-ONLY: measurability of the selection, for the deviation event
    (hCmeas : Measurable Chat) :
    μprob.real {ξ | 4 * Real.sqrt (trΣ * (8 * Real.log (1 / δ) + 1) / n)
        < ‖Chat ξ - μ₀‖}
      ≤ δ := by
  sorry

end StatLean.RobustStatistics
