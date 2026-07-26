import StatLean.HypothesisTesting.Randomization.Asymptotics
import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
import StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The two-sample permutation central limit theorem

Two independent samples $Y_1, \dots, Y_m \sim P_Y$ and $Z_1, \dots, Z_n \sim P_Z$ are
pooled into $X = (Y_1, \dots, Y_m, Z_1, \dots, Z_n)$ of length $N = m + n$, and the
permutation group of $\{1, \dots, N\}$ acts by relabelling coordinates. The statistic is
the scaled difference of sample means
$$ T_{m,n} = m^{1/2}\bigl(\bar Y_m - \bar Z_n\bigr) . $$

Assume $m/n \to \lambda \in (0, \infty)$, finite nonzero variances, and equal means
$\mu(P_Y) = \mu(P_Z)$. The **permutation** limit is
$$ \bigl(T_{m,n}(\pi X),\, T_{m,n}(\pi' X)\bigr) \;\xrightarrow{d}\;
   N(0, \tau^2) \otimes N(0, \tau^2), \qquad
   \tau^2 = \lambda\,\sigma^2(P_Y) + \sigma^2(P_Z) , $$
for two independent uniform random permutations $\pi, \pi'$, so the randomization
distribution satisfies $\hat R_{m,n}(t) \xrightarrow{P} \Phi(t/\tau)$.

The **unconditional** limit is a different Gaussian,
$$ T_{m,n} \;\xrightarrow{d}\; N\bigl(0, \sigma^2(P_Y) + \lambda\,\sigma^2(P_Z)\bigr) , $$
with the roles of $\lambda$ and the two variances exchanged. The two variances coincide
exactly when $\lambda = 1$ or $\sigma^2(P_Y) = \sigma^2(P_Z)$ — which is precisely why the
unstudentized permutation test can fail to be asymptotically level $\alpha$ for testing
equality of *means* when the variances differ and the sample sizes are unbalanced, and why
the studentized version of the companion file is needed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.1 (the two-sample
permutation central limit theorem). (`TSH4 §17.3 Thm 17.3.1`.)

**Proof formalization notes.**
* *The permutation action.* `Equiv.Perm (Fin N)` acts on `Fin N → ℝ` through Mathlib's
  `arrowAction`, declared here as a scoped instance since Mathlib deliberately leaves it a
  plain definition. This gives `(σ • x) i = x (σ⁻¹ i)`, whereas the classical display
  writes `(σ • x) i = x (σ i)`. The two conventions differ by inversion, a bijection of the
  group, so every group-averaged object — `randDist`, `randTest`, `randPValue`,
  `randPairLaw` — is literally unchanged; only the labelling of individual summands moves.
* *The pooled law.* `twoSampleLaw` is the product measure on `Fin (m + n) → ℝ` whose first
  `m` coordinates are `P_Y` and whose last `n` are `P_Z`, assembled with `Fin.addCases`.
  Independence within and across the two samples is exactly the product structure.
* *Degenerate corners.* `twoSampleMeanDiff` uses `(m : ℝ)⁻¹` and `(n : ℝ)⁻¹`, which are
  `0` when the sample is empty; the statistic is therefore total, with junk value at
  `m = 0` or `n = 0`. The theorems send both sample sizes to infinity, so those corners are
  never reached.
* *Both scales are carried explicitly.* `τ` is the permutation scale and `s` the
  unconditional one, each introduced with its defining equation (`τ² = λσ²_Y + σ²_Z`,
  `s² = σ²_Y + λσ²_Z`) and a positivity hypothesis. Writing them as separate parameters
  keeps the asymmetry — the whole content of the comparison — visible in the signatures.
* *Route to the limit.* Conditionally on the permutation weights, the statistic is a
  weighted sum of independent terms; the Cramér–Wold device reduces the bivariate claim to
  a scalar one, and the weighted i.i.d. central limit theorem of the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.LindebergCLT` supplies the scalar limit. The
  weights are indicators of sampling **without replacement**, so their moments — the
  variance of the weight average and the covariance across two independent permutations —
  come from the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments`.
* The statement is deliberately given in the `WeakConverges`-to-a-product form, so that it
  plugs directly into the joint hypothesis of
  `randDist_tendstoInProb_cdf` in `Randomization/Asymptotics`.

**Bibliographic comments.** The permutation test for the two-sample problem is due to
R. A. Fisher (*The Design of Experiments*, Oliver & Boyd, Edinburgh, 1935) and
E. J. G. Pitman ("Significance tests which may be applied to samples from any
populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130); exactness under the
group formulation is E. L. Lehmann and C. Stein ("On the theory of some non-parametric
hypotheses," *Ann. Math. Statist.* **20** (1949), 28–45), and the sampled-group variant is
M. Dwass ("Modified randomization tests for nonparametric hypotheses," *Ann. Math.
Statist.* **28** (1957), 181–187). The large-sample theory of permutation statistics is
W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192). That the unstudentized two-sample
permutation test can fail asymptotically under unequal variances was established by
J. P. Romano ("On the behavior of randomization tests without a group invariance
assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692; see also "Bootstrap and
randomization tests of some nonparametric hypotheses," *Ann. Statist.* **17** (1989),
141–159), with the general theory in E. Chung and J. P. Romano ("Exact and asymptotically
robust permutation tests," *Ann. Statist.* **41** (2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The permutation group acting on pooled data -/

/-- Coordinate relabelling: `Equiv.Perm (Fin N)` acts on data vectors `Fin N → ℝ` by
`(σ • x) i = x (σ⁻¹ i)`. Mathlib supplies this action as a definition (`arrowAction`)
rather than an instance; it is registered here, scoped to this area. -/
scoped instance permCoordAction (N : ℕ) : MulAction (Equiv.Perm (Fin N)) (Fin N → ℝ) :=
  arrowAction

/-- The permutation action, written out. -/
lemma perm_smul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) (i : Fin N) :
    (σ • x) i = x (σ⁻¹ i) := rfl

/-! ### The two-sample model and statistic -/

/-- The **pooled two-sample law** on `Fin (m + n) → ℝ`: the first `m` coordinates are
i.i.d. `P_Y`, the last `n` are i.i.d. `P_Z`, and the two blocks are independent. -/
noncomputable def twoSampleLaw (m n : ℕ) (PY PZ : Measure ℝ) :
    Measure (Fin (m + n) → ℝ) :=
  Measure.pi (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ))

/-- The **scaled difference of sample means** `T_{m,n} = √m (Ȳ_m − Z̄_n)`, read off the
pooled data vector. Total: an empty sample contributes mean `0` (junk), a corner the
theorems never reach. -/
noncomputable def twoSampleMeanDiff (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  Real.sqrt (m : ℝ) * ((m : ℝ)⁻¹ * ∑ i : Fin m, x (Fin.castAdd n i)
    - (n : ℝ)⁻¹ * ∑ j : Fin n, x (Fin.natAdd m j))

/-! ### Measurability and probability-measure bricks -/

/-- The difference-of-means statistic is measurable: a fixed linear combination of coordinate
projections. -/
private lemma measurable_twoSampleMeanDiff (m n : ℕ) :
    Measurable (twoSampleMeanDiff m n) := by
  unfold twoSampleMeanDiff
  fun_prop

/-- The permutation action `σ • x = x ∘ σ⁻¹` is measurable in `x` (coordinate relabelling). -/
private lemma measurable_perm_smul (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Measurable (fun x : Fin N → ℝ => σ • x) := by
  have hfun : (fun x : Fin N → ℝ => σ • x) = fun x i => x (σ⁻¹ i) := by
    ext x i; exact perm_smul_apply σ x i
  rw [hfun]
  exact measurable_pi_lambda _ fun i => measurable_pi_apply _

/-- The pooled two-sample law is a probability measure. -/
instance isProbabilityMeasure_twoSampleLaw (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] :
    IsProbabilityMeasure (twoSampleLaw m n PY PZ) := by
  unfold twoSampleLaw
  haveI : ∀ i, IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · first
        | infer_instance
        | · simp only [Fin.addCases_left]; infer_instance
    · first
        | infer_instance
        | · simp only [Fin.addCases_right]; infer_instance
  infer_instance

/-! ### Gaussian c.d.f. helpers -/

/-- The c.d.f. of an atomless probability measure on `ℝ` is continuous. -/
private lemma continuousAt_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NoAtoms μ] (t : ℝ) : ContinuousAt (cdf μ) t := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (cdf μ) t = cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (cdf μ) t ≤ cdf μ t := hmono.leftLim_le le_rfl
  have hge : cdf μ t ≤ Function.leftLim (cdf μ) t := by
    have h0 := (cdf μ).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

/-- Gaussian scaling of the c.d.f.: `cdf (N(0,τ²)) t = cdf (N(0,1)) (t/τ)` for `τ > 0`. -/
private lemma cdf_gaussianReal_scale {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    cdf (gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩) t = cdf (gaussianReal 0 1) (t / τ) := by
  have hmap : gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0)
      = (gaussianReal 0 1).map (fun x => τ * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · rw [mul_zero]
    · rw [mul_one]
  have hset : (fun x : ℝ => τ * x) ⁻¹' Set.Iic t = Set.Iic (t / τ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hτ, mul_comm τ x]
  rw [cdf_eq_real, cdf_eq_real, hmap, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, hset]

/-! ### The permutation limit -/

/-- **Two-sample permutation central limit theorem.** With `m/n → λ ∈ (0, ∞)`, finite
nonzero variances and equal means, the statistic evaluated at two independent uniform
random permutations converges jointly in law to a bivariate normal with **independent,
identically distributed** marginals `N(0, τ²)`, where
$$ \tau^2 = \lambda\,\sigma^2(P_Y) + \sigma^2(P_Z) . $$
This is exactly the joint hypothesis consumed by the general asymptotic randomization
theorem. -/
theorem weakConverges_randPairLaw_twoSample (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ τ μ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: the sample sizes are balanced in the limit, `m/n → λ`
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam))
    -- USER-INPUT: a nondegenerate limiting ratio
    (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: the two populations have the same mean; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    -- USER-INPUT: both variances are nonzero
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: `τ` names the positive square root of the permutation variance, so the
    -- limit can be written as a Gaussian with an `ℝ≥0` variance parameter
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) :
    WeakConverges
      (fun k => randPairLaw (Equiv.Perm (Fin (m k + n k)))
        (twoSampleMeanDiff (m k) (n k)) (twoSampleLaw (m k) (n k) PY PZ))
      ((gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩).prod
        (gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩)) := by
  -- TODO (deep, deferred): the two-sample permutation bivariate CLT (Thm 17.3.1).
  -- Route: conditionally on the two independent uniform permutations, `Tₘₙ(π X)` is a weighted
  -- sum of the independent pooled observations, the weights being sampling-without-replacement
  -- indicators; the Cramér–Wold device reduces the bivariate `randPairLaw` claim to a scalar
  -- linear combination, and the weighted i.i.d. CLT `weighted_iid_clt` supplies the scalar
  -- limit. The weight moments — `Var` of the weight average and the cross-permutation
  -- covariance giving asymptotic independence — are `HypergeometricMoments.var_mean_linear_le`
  -- and `HypergeometricMoments.cov_weight`.
  -- BLOCKED: there is no conditional-on-weights CLT assembly nor a Cramér–Wold device at the
  -- `randPairLaw`/`WeakConverges` level (the same bivariate-CLT gap as the still-open scalar
  -- `weakConverges_randPairLaw_signChange` in `Randomization/SignChange`); `weighted_iid_clt`
  -- delivers only a single scalar marginal as `TendstoInDistribution`, and the joint /
  -- test-function bridge is missing.
  sorry

/-- **Consequence: the randomization distribution converges to `Φ(·/τ)`.** -/
theorem randDist_twoSample_tendstoInProb (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ τ μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: positive square root of the permutation variance
    (hτpos : 0 < τ) (hτ : τ ^ 2 = lam * varY + varZ) (t : ℝ) :
    TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (twoSampleMeanDiff (m k) (n k)) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  -- Feed the permutation bivariate CLT into the forward engine `randDist_tendstoInProb_cdf`,
  -- discharging action measurability with `measurable_perm_smul` and continuity of the
  -- Gaussian c.d.f. with `continuousAt_cdf_of_noAtoms`, then rescale via `cdf_gaussianReal_scale`.
  have hjoint := weakConverges_randPairLaw_twoSample PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hτpos hτ
  have hvne : (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) ≠ 0 :=
    NNReal.coe_ne_zero.mp (by rw [NNReal.coe_mk]; positivity)
  haveI : NoAtoms (gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0)) := noAtoms_gaussianReal hvne
  have hcont : ContinuousAt (cdf (gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0))) t :=
    continuousAt_cdf_of_noAtoms _ t
  have hmain := randDist_tendstoInProb_cdf (G := fun k => Equiv.Perm (Fin (m k + n k)))
    (fun k => twoSampleLaw (m k) (n k) PY PZ) (fun k => twoSampleMeanDiff (m k) (n k))
    (gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0))
    (fun k => measurable_twoSampleMeanDiff (m k) (n k))
    (fun k g => measurable_perm_smul _ g) hjoint hcont
  rwa [cdf_gaussianReal_scale hτpos t] at hmain

/-! ### The unconditional limit, for contrast -/

/-- **Unconditional two-sample central limit theorem.** Under the same assumptions the
*true* sampling distribution of the statistic is asymptotically `N(0, s²)` with
$$ s^2 = \sigma^2(P_Y) + \lambda\,\sigma^2(P_Z) , $$
the mirror image of the permutation variance `τ² = λσ²(P_Y) + σ²(P_Z)`. The two agree if
and only if `λ = 1` or `σ²(P_Y) = σ²(P_Z)`; otherwise the permutation test calibrated on
this unstudentized statistic does not have asymptotic level `α` for testing equality of
means. -/
theorem weakConverges_twoSampleMeanDiff (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ s μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- LEAN-ONLY: positive square root of the unconditional variance
    (hspos : 0 < s) (hs : s ^ 2 = varY + lam * varZ) :
    WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k)))
      (gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩) := by
  -- TODO (self-contained, substantial): the ordinary (unconditional) two-sample CLT.
  -- Write `Tₘₙ = m^{-1/2} ∑ᵢ (Yᵢ − μ) − √(m/n) · n^{-1/2} ∑ⱼ (Zⱼ − μ)` (equal means). The two
  -- blocks are independent under `twoSampleLaw`, each block obeys the i.i.d. CLT, and
  -- `√(m/n) → √λ`, so the sum is asymptotically `N(0, varY + λ·varZ) = N(0, s²)` by Slutsky.
  -- NOT upstream-blocked: reducible to `weighted_iid_clt` (or `lindeberg_clt`) applied per
  -- block plus the `TendstoInDistribution → WeakConverges` test-function bridge (cf.
  -- `ParametricFamily/ScoreCLT`). Deferred here only for length: it needs the joint two-block
  -- independent-sum construction and the distribution-to-WeakConverges translation assembled in
  -- full, which is a self-standing ~150-line development rather than a reuse of an existing
  -- bivariate-CLT brick.
  sorry

end StatLean.HypothesisTesting
