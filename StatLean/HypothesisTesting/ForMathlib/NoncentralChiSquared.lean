import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.AsymptoticStatistics.ForMathlib.Anderson
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.Probability.Distributions.Gaussian.Multivariate

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
open scoped Topology ENNReal NNReal

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

/-- The noncentral chi-squared law is a probability measure: it is the pushforward of a
Gaussian (hence probability) measure under a continuous map. -/
instance isProbabilityMeasure_noncentralChiSquared (k : ℕ) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralChiSquared k l) := by
  sorry

/-- **Direction invariance.** Any Gaussian mean vector whose norm is `√l` yields the same
squared-norm law, so the noncentrality parameter `l = ‖μ‖²` is a complete invariant. Follows
from the orthogonal invariance of the standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
theorem map_normSq_multivariateGaussian_of_norm_eq (k : ℕ) (l : ℝ≥0)
    {v : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: the mean vector has the prescribed length.
    (hv : ‖v‖ = Real.sqrt (l : ℝ)) :
    (multivariateGaussian v 1).map (fun z => ‖z‖ ^ 2) = noncentralChiSquared k l := by
  sorry

/-- **Zero noncentrality is the central chi-squared law.** For `0 < k`,
`χ²_k(0) = χ²_k`. Via `multivariateGaussian_zero_one` the Gaussian becomes standard, its
coordinates are i.i.d. `N(0,1)`, and `‖z‖² = ∑ᵢ zᵢ²` has the central chi-squared law by the
library's sum-of-squares theorem. -/
theorem noncentralChiSquared_zero {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) :
    noncentralChiSquared k 0 = StatLean.MultipleTesting.chiSquared k := by
  sorry

/-- **The noncentral upper tail dominates the central one.** Direct consequence of the set
form of Anderson's inequality applied to the closed ball `{z : ‖z‖² ≤ t}`, which is convex
and symmetric: shifting the mean can only decrease its probability. -/
theorem chiSquared_tail_le_noncentralChiSquared {k : ℕ}
    -- USER-INPUT: at least one degree of freedom (`chiSquared 0` is degenerate).
    (hk : 0 < k) (l : ℝ≥0) (t : ℝ) :
    (StatLean.MultipleTesting.chiSquared k) (Set.Ioi t)
      ≤ (noncentralChiSquared k l) (Set.Ioi t) := by
  sorry

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
