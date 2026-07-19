import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest

/-!
# Smooth tests with a growing number of score directions

For fixed `k` the smooth test is consistent only against alternatives that move at least
one of the first `k` score directions — for the classical construction on `[0,1]`, only
against laws differing from the uniform in one of their first `k` moments. Letting `k` grow
with the sample size removes that restriction, at the price of a different limit theory:
the chi-squared approximation to the null law of `S_{n,k} = ∑_{j≤k} Z_{n,j}²` is replaced by
a normal one, since `χ²_k ≈ N(k, 2k)` for large `k`. The statement is
$$ \frac{S_{n,k_n} - k_n}{(2k_n)^{1/2}} \;\Longrightarrow\; N(0,1)
   \qquad (k_n \to \infty,\ k_n^3/n \to 0), $$
so that the test rejecting when that ratio exceeds `z_{1−α}` is asymptotically of level
`α`.

Contents:

* `bentkus_berry_esseen_convex`, `bentkus_berry_esseen_ball` — the multivariate
  Berry–Esseen bound the limit theorem rests on, over convex sets and over Euclidean
  balls; **statement only**;
* `smoothStat_largeK_weakConverges_gaussian` — the limit theorem itself.

**Why a Berry–Esseen bound is needed.** For fixed `k` the null limit of `S_{n,k}` follows
from the central limit theorem alone. Here the dimension grows with `n`, so a limit theorem
at fixed `k` is useless: one needs a bound on the normal approximation error that is
explicit in `k` and `n`. The bound over Euclidean balls has an absolute constant — no
dimensional factor — which is exactly what makes the growth condition as weak as
`k_n^3/n → 0`: with `sup_j E|ψ_j|³ ≤ B` one gets `β = E|Y|³ ≤ B k^{3/2}` by Minkowski's
inequality, hence an error `≤ C B k_n^{3/2} n^{-1/2} → 0`. The convex-set bound, whose
constant carries a factor `k^{1/4}`, would force the strictly stronger `k_n^{7/2}/n → 0`.

**DEFERRAL-ELIGIBLE (planned debt; proofless in the reference tradition, cf. Bentkus
2003).** Both Berry–Esseen statements are recorded as named debts: they are quoted, not
proved, in the goodness-of-fit literature that uses them, and proving them is a
self-contained research-level project in its own right (Fourier analysis over convex
bodies, not an application of anything in this library). The limit theorem
`smoothStat_largeK_weakConverges_gaussian` is *not* deferral-eligible: it closes modulo
the ball bound.

**Reference.** Classical goodness-of-fit theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* Both Berry–Esseen statements are phrased at the level of laws — a probability measure
  `ν` on `EuclideanSpace ℝ (Fin k)` and the pushforward of the `n`-fold product under
  `y ↦ n^{-1/2} ∑ᵢ yᵢ` — rather than through random vectors on an ambient space. The
  i.i.d. hypothesis is then built into the product measure, and, more importantly, the
  absolute constant of the ball bound can be existentially quantified *outside* all of
  `k`, `n` and `ν` without dragging an ambient type through the existential.
* "Absolute constant" is transcribed literally: the constant is quantified outside the
  dimension, the sample size and the law. This is the whole content of that half of the
  statement — with a `k`-dependent constant it would follow from the convex-set half.
* Convex sets are required to be measurable as well as convex. In dimension at least two
  there exist convex sets that are not Borel (their boundary can carry a non-Borel set),
  so measurability is not implied and the probability of an arbitrary convex set is not
  otherwise defined.
* The third-moment quantity is `β = ∫ ‖y‖³ dν`, matching the source; the growth condition
  is `sup_j E|ψⱼ|³ ≤ B` uniformly in `j`, which yields `β ≤ B k^{3/2}` through Minkowski's
  inequality applied to `(∑ⱼ ψⱼ²)^{3/2}`.
* The limit theorem is stated with `AsymptoticStatistics.WeakConverges` for the
  standardized statistic, consistent with the rest of the directory, and the score system
  is an infinite family `ψ : ℕ → 𝓧 → ℝ` truncated to its first `kₙ` members at stage `n`.
* A one-line consequence, not stated separately: the test rejecting when
  `(S_{n,kₙ} − kₙ)/(2kₙ)^{1/2} > z_{1−α}` is asymptotically of level `α`.

**Bibliographic comments.** The smooth test and its score system are due to J. Neyman
("Smooth test for goodness of fit," *Skandinavisk Aktuarietidskrift* **20** (1937),
149–199). The multivariate Berry–Esseen bound over convex sets and, with a
dimension-free constant, over Euclidean balls is due to V. Bentkus ("On the dependence of
the Berry–Esseen bound on dimension," *J. Statist. Plann. Inference* **113** (2003),
385–402); the one-dimensional ancestors are A. C. Berry ("The accuracy of the Gaussian
approximation to the sum of independent variates," *Trans. Amer. Math. Soc.* **49** (1941),
122–136) and C.-G. Esseen ("On the Liapunoff limit of error in the theory of probability,"
*Ark. Mat. Astr. Fys.* **28A** (1942), 1–19). Normal limits for chi-squared-type statistics
with growing dimension go back to H. Cramér and, in the goodness-of-fit setting, to the
analyses of the number of cells by H. Mann and A. Wald (*Ann. Math. Statist.* **13** (1942),
306–317).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The multivariate Berry–Esseen bound (statement only) -/

/-- **Berry–Esseen bound over convex sets.** For i.i.d. mean-zero random vectors in `ℝ^k`
with identity covariance and third absolute moment `β = E‖Y‖³`, the normal approximation
to the law of `n^{-1/2} ∑ᵢ Yᵢ` is accurate to `400 k^{1/4} β n^{-1/2}`, uniformly over
measurable convex sets.

DEFERRAL-ELIGIBLE (planned debt; proofless in the reference tradition, cf. Bentkus 2003):
this statement is quoted, not proved, wherever it is used, and its proof is an independent
project. -/
theorem bentkus_berry_esseen_convex {k n : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    {B : Set (EuclideanSpace ℝ (Fin k))}
    -- USER-INPUT: a nonempty sample
    (hn : 0 < n)
    -- USER-INPUT: a nondegenerate dimension
    (hk : 0 < k)
    -- USER-INPUT: `ν` is the common law of the summands
    (hν : IsProbabilityMeasure ν)
    -- USER-INPUT: the summands are centred; Bentkus 2003
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    -- USER-INPUT: the summands have identity covariance; Bentkus 2003
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k),
      (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    -- USER-INPUT: the third absolute moment is finite
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    -- USER-INPUT: the comparison set is measurable (convexity does not imply it in
    -- dimension `≥ 2`)
    (hBmeas : MeasurableSet B)
    -- USER-INPUT: the comparison set is convex; Bentkus 2003
    (hBconv : Convex ℝ B) :
    |((((Measure.pi fun _ : Fin n => ν)).map
          fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
        - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
      ≤ 400 * (k : ℝ) ^ ((1 : ℝ) / 4) * (∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ) := by
  sorry

/-- **Berry–Esseen bound over Euclidean balls, with a dimension-free constant.** There is
an absolute constant `C` — independent of the dimension, of the sample size and of the
sampling law — such that the normal approximation to the law of `‖n^{-1/2} ∑ᵢ Yᵢ‖²` is
accurate to `C β n^{-1/2}` uniformly in the threshold.

The absence of a dimensional factor is the entire content of the statement, and is what
the growing-`k` limit theorem below consumes; the constant is therefore quantified outside
`k`, `n` and the law.

DEFERRAL-ELIGIBLE (planned debt; proofless in the reference tradition, cf. Bentkus 2003). -/
theorem bentkus_berry_esseen_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * (∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ) := by
  sorry

/-! ### The normal limit of the smooth statistic with `kₙ → ∞` -/

/-- **Normal limit of the smooth statistic with a growing number of score directions.**
Let `ψ₁, ψ₂, …` be an infinite orthonormal system in `L²(P₀)`, orthogonal to the constants,
with uniformly bounded third absolute moments `sup_j E_{P₀}|ψⱼ(X)|³ = B < ∞`. If
`kₙ → ∞` and `kₙ³/n → 0`, then under the null hypothesis
$$ \frac{S_{n,k_n} - k_n}{(2 k_n)^{1/2}} \;\Longrightarrow\; N(0,1). $$

Both growth conditions are the source's, transcribed unchanged; `kₙ³/n → 0` is exactly
what makes the ball Berry–Esseen error `C B kₙ^{3/2} n^{-1/2}` vanish, and `kₙ → ∞` is
what makes the chi-squared law with `kₙ` degrees of freedom normal in the limit. The proof
consumes `bentkus_berry_esseen_ball`. -/
theorem smoothStat_largeK_weakConverges_gaussian {Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀] {ψ : ℕ → 𝓧 → ℝ}
    {kseq : ℕ → ℕ} {B : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: the score functions are measurable
    (hψmeas : ∀ j, Measurable (ψ j))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: uniformly bounded third absolute moments; Bentkus 2003 is applied
    -- through this bound
    (hthird : ∀ j, (∫ x, |ψ j x| ^ 3 ∂P₀) ≤ B)
    -- USER-INPUT: the number of score directions diverges
    (hkinf : Tendsto kseq atTop atTop)
    -- USER-INPUT: it diverges slowly enough: `kₙ³/n → 0`
    (hkgrowth : Tendsto (fun n => (kseq n : ℝ) ^ 3 / (n : ℝ)) atTop (nhds 0))
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Neyman 1937
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: the null hypothesis: every observation has law `P₀`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = P₀) :
    WeakConverges
      (fun n => (P n).map fun ω =>
        (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
          / Real.sqrt (2 * (kseq n : ℝ)))
      (gaussianReal 0 1) := by
  sorry

end StatLean.HypothesisTesting
