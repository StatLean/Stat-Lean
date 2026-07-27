import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin
import StatLean.PointEstimation.ExponentialFamily.Defs
import StatLean.AsymptoticStatistics.ParametricFamily.ScoreCLT
import Mathlib.Probability.HasLawExists

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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.4 (Neyman's Smooth Tests), Theorem 16.4.1 (§16.4.1, Fixed `k` Asymptotics): Neyman's
smooth test is asymptotically maximin. (`TSH4 §16.4 Thm 16.4.1`.)

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

/-! #### Vectorised scores and the multivariate CLT brick

The null-limit proof mirrors `GoodnessOfFit/ChiSquaredMultinomial.lean`. The score functions
are already centred in `L²(P₀)` (`E₀ψⱼ = 0`) with covariance the identity (`∫ψᵢψⱼ = δᵢⱼ`),
so the per-observation vector `psiVec x = (ψ₁ x, …, ψ_k x)` has mean zero and covariance
`Iₖ`; the standardised sum converges to `N(0, Iₖ)` and the squared norm is `Sₙ`. -/

/-- The per-observation score vector `x ↦ (ψ₁ x, …, ψ_k x)` in `EuclideanSpace ℝ (Fin k)`. -/
private noncomputable def psiVec {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (x : 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ψ j x)

/-- The standardised score vector `Zₙ = (√n)⁻¹ ∑ᵢ ψ(Xᵢ)`, whose `j`-th coordinate is
`smoothScore ψ X j` and whose squared norm is `smoothStat`. -/
private noncomputable def scoreVec {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧) (ω : Ω) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => smoothScore ψ X j ω)

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_euclidean_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The standardised score vector is measurable. -/
private lemma measurable_scoreVec {n k : ℕ} {ψ : Fin k → 𝓧 → ℝ}
    {X : Fin n → Ω → 𝓧} (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i)) :
    Measurable (scoreVec ψ X) := by
  have hg : Measurable (fun ω (j : Fin k) => smoothScore ψ X j ω) := by
    refine measurable_pi_iff.mpr (fun j => ?_)
    simp only [smoothScore]
    exact (Finset.univ.measurable_sum (fun i _ => (hψmeas j).comp (hX i))).div measurable_const
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp hg

/-- `scoreVec` is the standardised sum of the per-observation score vectors. -/
private lemma scoreVec_eq_smul_sum {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ)
    (X : Fin n → Ω → 𝓧) (ω : Ω) :
    scoreVec ψ X ω = (Real.sqrt n)⁻¹ • ∑ i : Fin n, psiVec ψ (X i ω) := by
  rw [scoreVec]
  simp only [psiVec]
  rw [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  refine congrArg (WithLp.toLp 2) ?_
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [smoothScore, div_eq_inv_mul]

/-- **Multivariate CLT for the score vector** (the single deep analytic brick of the
null-limit proof). Under `P₀`, with the score functions orthonormal and centred in `L²(P₀)`,
the standardised score vector converges in law to the standard Gaussian `N(0, Iₖ)`.

The proof realises `scoreVec` as the standardised sum of the per-observation score vectors
`psiVec x = (ψⱼ x)ⱼ` (`scoreVec_eq_smul_sum`), transfers the per-stage law to the canonical
infinite-product i.i.d. model produced by `ProbabilityTheory.exists_iid` (matching both
sequences to `(Measure.pi …).map` via `iIndepFun_iff_map_fun_eq_pi_map`), and applies the
reusable fixed-i.i.d. CLT `AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim`. The
zero-mean side-condition is `hcentred`, and the covariance side-condition
`∫ ⟪u, g⟫⟪v, g⟫ = u ⬝ᵥ Iₖ v` is `hortho`. -/
private lemma scoreVec_weakConverges_gaussian {k : ℕ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ} {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)] {X : (n : ℕ) → Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hX : ∀ n i, Measurable (X n i))
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = P₀) :
    WeakConverges (fun n => (P n).map (scoreVec ψ (X n)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  classical
  -- Integrability from `L²` (the covariance identity `∫ ψᵢ² = 1` forces `ψᵢ ∈ L²`).
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  have hψint : ∀ i, Integrable (ψ i) P₀ := fun i => (hψL2 i).integrable one_le_two
  have hψψint : ∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀ := fun i j => by
    simpa using (hψL2 i).integrable_mul (hψL2 j)
  -- the canonical i.i.d. model `(Ω₀, P₀c, Z)` with marginal law `P₀`
  obtain ⟨Ω₀, mΩ₀, P₀c, Z, hZmeas, hZlaw, hZindep, hP₀cprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P₀
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀c := hP₀cprob
  -- per-observation score map `g` and per-observation vectors `Y`
  set g : 𝓧 → EuclideanSpace ℝ (Fin k) := fun x => psiVec ψ x with hg
  have hgmeas : Measurable g :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ (fun j => hψmeas j))
  set Y : ℕ → Ω₀ → EuclideanSpace ℝ (Fin k) := fun i ω => g (Z i ω) with hY
  -- an integral of `F ∘ Z 0` reduces to an integral over `P₀`
  have hkey : ∀ (F : 𝓧 → ℝ), AEStronglyMeasurable F P₀ →
      ∫ ω, F (Z 0 ω) ∂P₀c = ∫ x, F x ∂P₀ := by
    intro F hF
    rw [show (∫ ω, F (Z 0 ω) ∂P₀c) = ∫ x, F x ∂(P₀c.map (Z 0)) from
          (integral_map (hZmeas 0).aemeasurable (by rw [(hZlaw 0).map_eq]; exact hF)).symm,
        (hZlaw 0).map_eq]
  -- inputs to `clt_finDim`
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hgmeas.comp (hZmeas i)
  have hYindep : iIndepFun Y P₀c := hZindep.comp (fun _ => g) (fun _ => hgmeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P₀c P₀c := fun i =>
    (show IdentDistrib (Z i) (Z 0) P₀c P₀c from
      ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
        (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp hgmeas
  -- the score vector has zero mean
  have h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k), ∫ ω, ⟪u, Y 0 ω⟫_ℝ ∂P₀c = 0 := by
    intro u
    have hFint : Integrable (fun x => ⟪u, g x⟫_ℝ) P₀ := by
      have hpt : (fun x => ⟪u, g x⟫_ℝ) = (fun x => ∑ i, u i * ψ i x) := by
        funext x; rw [inner_euclidean_sum]; rfl
      rw [hpt]
      exact integrable_finset_sum _ (fun i _ => (hψint i).const_mul (u i))
    rw [hkey _ hFint.aestronglyMeasurable]
    have hpt : (fun x => ⟪u, g x⟫_ℝ) = (fun x => ∑ i, u i * ψ i x) := by
      funext x; rw [inner_euclidean_sum]; rfl
    rw [hpt, integral_finset_sum _ (fun i _ => (hψint i).const_mul (u i))]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  -- the covariance identity `∫ ⟪u,·⟫⟪v,·⟫ = u ⬝ Iₖ v`
  have h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      ∫ ω, ⟪u, Y 0 ω⟫_ℝ * ⟪v, Y 0 ω⟫_ℝ ∂P₀c
        = u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec v.ofLp := by
    intro u v
    have hpt : (fun x => ⟪u, g x⟫_ℝ * ⟪v, g x⟫_ℝ)
        = (fun x => ∑ i, ∑ j, (u i * v j) * (ψ i x * ψ j x)) := by
      funext x
      rw [inner_euclidean_sum, inner_euclidean_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      show (u i * ψ i x) * (v j * ψ j x) = (u i * v j) * (ψ i x * ψ j x)
      ring
    have hFint : Integrable (fun x => ⟪u, g x⟫_ℝ * ⟪v, g x⟫_ℝ) P₀ := by
      rw [hpt]
      exact integrable_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j)))
    rw [hkey _ hFint.aestronglyMeasurable, hpt,
      integral_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j)))]
    have hRHS : u.ofLp ⬝ᵥ (1 : Matrix (Fin k) (Fin k) ℝ).mulVec v.ofLp = ∑ i, u i * v i := by
      rw [Matrix.one_mulVec]; rfl
    rw [hRHS]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j))]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, mul_one]
  -- the score vector is square-integrable
  have h_L2 : MemLp (Y 0) 2 P₀c := by
    have hg_L2 : MemLp g 2 P₀ := by
      refine (memLp_two_iff_integrable_sq_norm hgmeas.aestronglyMeasurable).2 ?_
      have hnorm : (fun x => ‖g x‖ ^ 2) = (fun x => ∑ i, ψ i x ^ 2) := by
        funext x
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Real.norm_eq_abs, sq_abs]
        rfl
      rw [hnorm]
      exact integrable_finset_sum _ (fun i _ => hsqint i)
    have hmap : MemLp g 2 (P₀c.map (Z 0)) := by rw [(hZlaw 0).map_eq]; exact hg_L2
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable (hZmeas 0).aemeasurable).1 hmap
  -- the fixed-i.i.d. CLT for the canonical model
  have hclt := AsymptoticStatistics.ParametricFamily.ScoreCLT.clt_finDim
    P₀c Y hYmeas hYindep hYident h_zero_mean (1 : Matrix (Fin k) (Fin k) ℝ)
    Matrix.PosDef.one.posSemidef h_cov h_L2
  -- the canonical standardised sum matches `scoreVec` in law at each `n`
  have hmatch : ∀ n : ℕ,
      P₀c.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = (P n).map (scoreVec ψ (X n)) := by
    intro n
    set F : (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
      fun d => (Real.sqrt n)⁻¹ • ∑ i : Fin n, g (d i) with hF
    have hsum : Measurable (fun d : Fin n → 𝓧 => ∑ i : Fin n, g (d i)) :=
      Finset.univ.measurable_sum (fun i _ => hgmeas.comp (measurable_pi_apply i))
    have hFmeas : Measurable F := by rw [hF]; exact measurable_const.smul hsum
    have hgZ : Measurable (fun ω (i : Fin n) => Z (i : ℕ) ω) :=
      measurable_pi_lambda _ (fun i => hZmeas i)
    have hgX : Measurable (fun ω (i : Fin n) => X n i ω) :=
      measurable_pi_lambda _ (fun i => hX n i)
    have hLHSfun : (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω)
        = F ∘ (fun ω (i : Fin n) => Z (i : ℕ) ω) := by
      funext ω
      simp only [hF, hY, Function.comp]
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (Z i ω)) n]
    have hRHSfun : scoreVec ψ (X n) = F ∘ (fun ω (i : Fin n) => X n i ω) := by
      funext ω
      rw [scoreVec_eq_smul_sum ψ (X n) ω]
      simp only [hF, hg, Function.comp]
    have hpiZ : P₀c.map (fun ω (i : Fin n) => Z (i : ℕ) ω)
        = Measure.pi (fun _ : Fin n => P₀) := by
      have hsub : iIndepFun (fun (i : Fin n) => Z (i : ℕ)) P₀c :=
        hZindep.precomp Fin.val_injective
      rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) => Z (i : ℕ))
        (fun i => (hZmeas (i : ℕ)).aemeasurable)).1 hsub]
      congr 1; funext i; exact (hZlaw (i : ℕ)).map_eq
    have hpiX : (P n).map (fun ω (i : Fin n) => X n i ω)
        = Measure.pi (fun _ : Fin n => P₀) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n)]
      congr 1; funext i; exact hlaw n i
    rw [hLHSfun, hRHSfun, ← Measure.map_map hFmeas hgZ, ← Measure.map_map hFmeas hgX,
      hpiZ, hpiX]
  simp only [hmatch] at hclt
  exact hclt

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
  -- the continuous quadratic form `q z = ⟪z, Iₖ⁻¹ z⟫ = ‖z‖²`
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin k) (Fin k) ℝ)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫_ℝ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  -- pointwise: `q (scoreVec ω) = smoothStat ω`
  have hq : ∀ n ω, q (scoreVec ψ (X n) ω) = smoothStat ψ (X n) ω := by
    intro n ω
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, inv_one, Matrix.one_mulVec]
    simp only [smoothStat, dotProduct]
    exact Finset.sum_congr rfl (fun j _ => by rw [sq]; rfl)
  -- the lifted CLT brick, then continuous mapping
  have hbrick := scoreVec_weakConverges_gaussian (P₀ := P₀) (ψ := ψ) (P := P) (X := X)
    hψmeas hortho hcentred hX hindep hlaw
  have hmapped := hbrick.map hq_cont hq_cont.measurable
  -- the target is `χ²_k` (Gaussian → chi-squared bridge, covariance the identity)
  have htarget : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (1 : Matrix (Fin k) (Fin k) ℝ)).map q = chiSquared k := by
    simp only [hqdef, hTdef]
    exact multivariateGaussian_map_inner_inv_eq_chiSquared hk Matrix.PosDef.one
  -- each pushforward term equals the law of `smoothStat`
  have hseq : (fun n => ((P n).map (scoreVec ψ (X n))).map q)
      = fun n => (P n).map (smoothStat ψ (X n)) := by
    funext n
    rw [Measure.map_map hq_cont.measurable (measurable_scoreVec hψmeas (hX n))]
    exact Measure.map_congr (Filter.Eventually.of_forall (fun ω => hq n ω))
  rw [hseq, htarget] at hmapped
  exact hmapped

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
  -- TODO (genuine deep gap; NOT closeable from the imported deferral as stated). Two pieces:
  --   1. Asymptotic-normality data for `smoothModel` to invoke `asymptotic_maximin_upper_bound`
  --      with `I = Iₖ`: the centring `Zₙ = scoreVec` (with `Zₙ ⇒ N(0, Iₖ)` under `Q n 0 = P₀`
  --      from `scoreVec_weakConverges_gaussian`) is available, but the log-likelihood field
  --      `L n h` and its quadratic LAN expansion (`hdens`, `hLAN`) still have to be built from
  --      the exponential-family log-partition `A` (its Fisher information at `0` is `Iₖ` by
  --      orthonormality); this needs `PointEstimation.ExponentialFamily.Smoothness`.
  --   2. A *bounded*-shell (`b ≤ ‖h‖ ≤ B`) transfer. The imported
  --      `asymptotic_maximin_upper_bound` concludes only for the UNBOUNDED shell
  --      `{b² ≤ h⊤ I h} = {b ≤ ‖h‖}` (with `I = Iₖ`), which is the a-fortiori WEAKER bound:
  --      `sInf` over the bounded shell (a subset) is ≥ `sInf` over the unbounded one, so the
  --      lemma's bound does not transfer in the needed direction (see the module docstring's
  --      "a fortiori" remark — bounded ⟹ unbounded, not the reverse). The bounded bound is
  --      provable by the SAME mixture–Neyman–Pearson argument (the least-favourable `σ` sits
  --      on the inner sphere `‖h‖ = b ⊆` the bounded shell), but that machinery lives inside
  --      the deferred `asymptotic_maximin_upper_bound`; a bounded-shell restatement of it is
  --      needed and is absent from `AsymptoticMaximin.lean` (which must not be edited here).
  sorry

/-- **The smooth test attains the maximin value on the local shell** (LIFTED — the deep half
of `smoothTest_asymptotically_maximin`). Under the local alternatives `θ = h n^{-1/2}` with
`b ≤ |h| ≤ B`, the minimum power of the smooth test `1{Sₙ > c}` converges to
`P{χ²_k(b²) > c_{k,1−α}}`.

TODO (genuine deep gap): this is the noncentral analogue of
`smoothStat_weakConverges_chiSquared`. Its intended proof is: (i) the weak limit of `Sₙ`
under the *local alternatives* is `χ²_k(‖h‖²)` — a multivariate *triangular-array* CLT
giving `scoreVec ⇒ N((hⱼ)ⱼ, Iₖ)`, hence `Sₙ ⇒ χ²_k(‖h‖²)` by the same continuous-mapping /
`multivariateGaussian_map_inner_inv_eq_noncentralChiSquared` bridge used in the null case;
(ii) the map `h ↦ P{χ²_k(‖h‖²) > c}` is increasing in `‖h‖` (`noncentralChiSquared_tail_mono`),
so the minimum over the shell is asymptotically attained at the inner boundary `‖h‖ = b`,
giving `P{χ²_k(b²) > c}`.

TODO (re-derived).  The triangular-array CLT is no longer the obstruction: its multinomial
twin `ChiSquaredMultinomial.reducedCount_weakConverges_noncentral` is now CLOSED, by running
the drifting-row multivariate limit law `HypothesisTesting.meanVec_root_tendsto` on the
sequence of per-observation laws.  The same route applies here, with `F n` the law of
`psiVec` under the *tilted* member `(smoothModel P₀ ψ hψ).P (n^{-1/2} • h)`: what has to be
supplied for it is the class condition `meanVecSeqClass`, i.e. that the exponential tilt
`p_{θ}` converges weakly to `P₀` with mean vector `→ h` and covariance `→ Iₖ` as `θ → 0`
along `θ = n^{-1/2}h`.  That is a differentiability-in-quadratic-mean statement about
`smoothModel`, and needs `PointEstimation.ExponentialFamily.Smoothness` (the log-partition
`A` and its first two derivatives at `0`), which is not imported here.  The two remaining
obstructions are therefore (a) that exponential-family expansion, and (b) the pinning of the
shell infimum to the inner boundary, which consumes `noncentralChiSquared_tail_mono` —
itself resting on the still-open `stdGaussian_normSq_le_antitone` — together with a
uniform-in-`h` version of the per-`h` limit.  The statement stays lifted here as a single
named debt. -/
private lemma smoothTest_shell_minPower_tendsto {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    (hk : 0 < k) (hb : 0 < b) (hbB : b < B) (hα : 0 < α) (hα1 : α < 1)
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hint : (0 : EuclideanSpace ℝ (Fin k)) ∈ interior (smoothModel P₀ ψ hψ).natSet)
    (hX : ∀ n, ∀ i, Measurable (X n i))
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < smoothStat ψ (X n) ω then (1 : ℝ) else 0) h)
        '' {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal)) := by
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
  refine ⟨?_, ?_⟩
  · -- Attainment on the shell: the deep noncentral-limit half (lifted).
    exact smoothTest_shell_minPower_tendsto hk hb hbB hα hα1 hc hψ hortho hcentred hint
      hX hindep hlaw
  · -- Optimality: for any level-`α` test this is exactly `smoothTest_maximin_upper_bound`.
    intro ψtest hψt hlvl
    exact smoothTest_maximin_upper_bound hk hb hbB hα hα1 hc hψ hortho hcentred hint
      hX hindep hlaw hψt hlvl

end StatLean.HypothesisTesting
