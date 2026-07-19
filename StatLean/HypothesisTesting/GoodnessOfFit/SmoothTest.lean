import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin
import StatLean.PointEstimation.ExponentialFamily.Defs

/-!
# Smooth tests of fit: the fixed-`k` theory

To test a fully specified null law `P₀` on an arbitrary sample space, embed it in the
`k`-parameter exponential family of densities with respect to `P₀`
$$ p_\theta(x) \;=\; C_k(\theta)\,
     \exp\Bigl(\sum_{j=1}^{k} \theta_j\, \psi_j(x)\Bigr), \qquad \theta \in \mathbb R^k, $$
where `ψ₁, …, ψ_k` — together with the constant function `ψ₀ = 1` — are orthonormal in
`L²(P₀)`. The null hypothesis is `θ = 0`, and the score test for it rejects for large
values of
$$ S_n \;=\; \sum_{j=1}^{k} Z_{n,j}^2, \qquad
   Z_{n,j} \;=\; n^{-1/2}\sum_{i=1}^{n} \psi_j(X_i). $$
This is the smooth test. It is the score (Rao) test of the embedding family, whence its
optimality; and it contains the chi-squared test of the previous files as the special case
of a multinomial sample space with `ψ` the standardized cell indicators.

Contents:

* `smoothModel` — the embedding exponential family, built through the point-estimation
  area's `ExpFamily.ofDensity` over the base `P₀`;
* `smoothScore`, `smoothStat` — the score components `Z_{n,j}` and the statistic `Sₙ`;
* `smoothStat_weakConverges_chiSquared` — under `P₀`, `Sₙ ⇒ χ²_k`;
* `smoothTest_maximin_upper_bound` — no asymptotically level-`α` test beats
  `P{χ²_k(b²) > c_{k,1−α}}` in minimum power over `b ≤ |h| ≤ B`;
* `smoothTest_asymptotically_maximin` — the smooth test attains that value.

The last two are the instances of `AsymptoticMaximin.asymptotic_maximin_upper_bound` in
which the information matrix is the identity: orthonormality of the `ψⱼ` in `L²(P₀)` makes
the Fisher information of the embedding family at `θ = 0` equal to `Iₖ`, so the local shell
of the transfer lemma is the Euclidean shell `b ≤ |h| ≤ B` and the maximin value is the
same noncentral chi-squared number that appeared for Pearson's test.

**Reference.** Classical goodness-of-fit theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* `smoothModel` is `ExpFamily.ofDensity P₀ 1 ψ⃗ _`: the carrier is trivial and the base of
  the exponential family is `P₀` itself (`P₀.withDensity 1 = P₀`, a lemma at the point of
  use, not a definitional equality). The natural statistic is the vector
  `x ↦ (ψ₁ x, …, ψ_k x)` in `EuclideanSpace ℝ (Fin k)`, so `E.P θ` is exactly the density
  displayed above, with `A(θ) = −log C_k(θ)` the log-partition function. The prototype —
  testing uniformity on `[0,1]` with normalized Legendre polynomials — is the case
  `P₀ = ` uniform, and nothing in this file is special to it.
* Orthonormality is recorded as two hypotheses: `∫ ψᵢψⱼ dP₀ = δᵢⱼ` and `∫ ψⱼ dP₀ = 0`. The
  second is orthogonality to the constant function `ψ₀ = 1` and is what makes the score at
  `θ = 0` centred; it is a consequence of the first only if the constant is included in
  the system, which is why it is stated separately.
* `θ = 0` is required to be an interior point of the natural parameter set — the full-rank
  condition making the family q.m.d. at the null and its information matrix invertible.
* The score is scaled as `n^{-1/2} ∑ᵢ ψⱼ(Xᵢ)` rather than as a derivative of the
  log-likelihood: the identification of the two (the derivative of the log-partition
  function vanishes at `θ = 0` because `E₀ψⱼ = 0`) is a lemma about `smoothModel`, not
  part of the definition of the statistic.
* The local experiments of the two maximin statements are carried as data `Q n h` and tied
  to `smoothModel` by the requirement that the observations be i.i.d. with law
  `E.P (n^{-1/2} • h)`; this is the same format as in `ChiSquaredMaximin.lean`.
* The upper bound is stated for a finite outer radius `B`. The unbounded case `B = ∞`
  follows a fortiori, the infimum over a larger set being smaller. The *attainment* half,
  in contrast, genuinely needs `B < ∞` in general; it extends to `B = ∞` under the extra
  condition that `Var_θ[ψⱼ(X₁)]` be bounded uniformly in `θ` — automatic when the `ψⱼ` are
  bounded functions, as they are for the Legendre system.

**Bibliographic comments.** The smooth test, the embedding family, and the asymptotic
maximin property against the alternatives it generates are due to J. Neyman ("Smooth test
for goodness of fit," *Skandinavisk Aktuarietidskrift* **20** (1937), 149–199). The score
statistic it specialises is due to C. R. Rao ("Large sample tests of statistical hypotheses
concerning several parameters with applications to problems of estimation," *Proc. Camb.
Phil. Soc.* **44** (1948), 50–57). The reduction of the local optimality question to a
Gaussian shift experiment follows L. Le Cam (*Univ. California Publ. Statist.* **3**
(1960), 37–98); the special case in which the statistic reduces to Pearson's is due to
K. Pearson (*Phil. Mag.* **50** (1900), 157–175). Later developments, including data-driven
choice of `k`, are surveyed in J. C. W. Rayner and D. J. Best, *Smooth Tests of Goodness of
Fit*, Oxford University Press, 1989.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)
open StatLean.PointEstimation (ExpFamily)

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-! ### The embedding family and the statistic -/

/-- The **smooth model**: the `k`-parameter exponential family through the score functions
`ψ₁, …, ψ_k`, with densities `C_k(θ) exp(∑ⱼ θⱼ ψⱼ(x))` with respect to the null law `P₀`.

Built with the point-estimation area's `ExpFamily.ofDensity` with trivial carrier, so that
the base measure of the family is `P₀` itself and the natural statistic is the vector of
score functions. The null hypothesis is the canonical parameter `θ = 0`, at which the
member measure is `P₀`. -/
noncomputable def smoothModel {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k))) :
    ExpFamily 𝓧 (EuclideanSpace ℝ (Fin k)) :=
  ExpFamily.ofDensity P₀ (fun _ => 1) (fun x => WithLp.toLp 2 fun j => ψ j x) hψ

/-- The **`j`-th smooth score component** `Z_{n,j} = n^{-1/2} ∑ᵢ ψⱼ(Xᵢ)`. Under the null
law it is centred (because `∫ ψⱼ dP₀ = 0`) with variance one (because `∫ ψⱼ² dP₀ = 1`), and
its components are asymptotically uncorrelated (because `∫ ψᵢψⱼ dP₀ = 0` for `i ≠ j`).
For `n = 0` it is the junk value `0`. -/
noncomputable def smoothScore {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (j : Fin k) (ω : Ω) : ℝ :=
  (∑ i, ψ j (X i ω)) / Real.sqrt (n : ℝ)

/-- **Neyman's smooth statistic** `Sₙ = ∑_{j=1}^{k} Z_{n,j}²`: the squared Euclidean norm
of the score vector, i.e. the score (Rao) statistic of the smooth model at `θ = 0`, the
Fisher information there being the identity. -/
noncomputable def smoothStat {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (ω : Ω) : ℝ :=
  ∑ j : Fin k, (smoothScore ψ X j ω) ^ 2

/-! ### The null limiting distribution -/

/-- **Null limit of the smooth statistic.** For an i.i.d. sample from the null law `P₀`
and score functions orthonormal in `L²(P₀)` and orthogonal to the constants, the smooth
statistic converges in law to `χ²_k`. Hence the test rejecting when `Sₙ > c_{k,1−α}` is
asymptotically of level `α`.

This is the multivariate central limit theorem for the score vector (`Zₙ ⇒ N(0, Iₖ)`)
followed by the continuous mapping theorem applied to the squared norm. -/
theorem smoothStat_weakConverges_chiSquared {k : ℕ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ} {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)] {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: at least one score direction; `χ²₀` is degenerate
    (hk : 0 < k)
    -- USER-INPUT: the score functions are measurable
    (hψmeas : ∀ j, Measurable (ψ j))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Neyman 1937
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: the null hypothesis: every observation has law `P₀`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = P₀) :
    WeakConverges (fun n => (P n).map (smoothStat ψ (X n))) (chiSquared k) := by
  sorry

/-! ### Asymptotic maximin optimality over the `O(n^{-1/2})` sphere -/

/-- **No test beats the chi-squared value on the local shell.** For any test sequence whose
power at `θ = 0` tends to `α`, and any radii `0 < b < B < ∞`, the limiting minimum power
over the local alternatives `θ = h n^{-1/2}` with `b ≤ |h| ≤ B` is at most
`P{χ²_k(b²) > c_{k,1−α}}`.

The instance of `asymptotic_maximin_upper_bound` in which the information matrix is the
identity — see the module docstring. The statement remains true, a fortiori, with the
outer radius removed. -/
theorem smoothTest_maximin_upper_bound {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧} {φ : ℕ → Ω → ℝ}
    -- USER-INPUT: at least one score direction
    (hk : 0 < k)
    -- USER-INPUT: the shell is nondegenerate
    (hb : 0 < b) (hbB : b < B)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the vector of score functions is measurable; this is the certificate
    -- the exponential-family structure carries, and it implies measurability of each `ψⱼ`
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: the null parameter is interior to the natural parameter set (full rank)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the observations are i.i.d.
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the observations have law
    -- `p_{h n^{-1/2}}`, the smooth model at the local alternative
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
    -- USER-INPUT: the competitors are randomized tests
    (hφ : ∀ n, IsCriticalFn (φ n))
    -- USER-INPUT: the competitors are asymptotically of level `α` at the null
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) ''
        {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  sorry

/-- **The smooth test is asymptotically maximin.** For any radii `0 < b < B < ∞`, the
minimum power of the smooth test `1{Sₙ > c}` over the local alternatives `θ = h n^{-1/2}`
with `b ≤ |h| ≤ B` converges to `P{χ²_k(b²) > c_{k,1−α}}` (first conjunct); by
`smoothTest_maximin_upper_bound` it therefore maximizes the limiting minimum power among
all test sequences of asymptotic level `α` (second conjunct).

The worst case over the shell is asymptotically attained on its inner boundary `|h| = b`,
the noncentral chi-squared tail being increasing in the noncentrality parameter. -/
theorem smoothTest_asymptotically_maximin {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: at least one score direction
    (hk : 0 < k)
    -- USER-INPUT: the shell is nondegenerate and bounded (see the module docstring on
    -- removing the outer radius)
    (hb : 0 < b) (hbB : b < B)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the vector of score functions is measurable; this is the certificate
    -- the exponential-family structure carries, and it implies measurability of each `ψⱼ`
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: the null parameter is interior to the natural parameter set (full rank)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the observations are i.i.d.
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the observations have law
    -- `p_{h n^{-1/2}}`, the smooth model at the local alternative
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h)
        '' {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal))
      ∧ ∀ ψtest : ℕ → Ω → ℝ, (∀ n, IsCriticalFn (ψtest n)) →
        Tendsto (fun n => power (Q n) (ψtest n) 0) atTop (nhds α) →
        limsup (fun n => sInf ((fun h => power (Q n) (ψtest n) h) ''
            {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
          ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  sorry

end StatLean.HypothesisTesting
