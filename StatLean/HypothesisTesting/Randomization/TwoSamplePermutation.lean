import StatLean.HypothesisTesting.Randomization.Asymptotics
import StatLean.HypothesisTesting.Randomization.PairCLT
import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
import StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments
import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.CharacteristicFunction

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
  -- STATUS (re-derived this session, wave 4; verdict unchanged, but now *isolated*).
  -- Re-checked against the repository and Mathlib v4.29.1: there is no combinatorial central
  -- limit theorem, no Stein/exchangeable-pairs machinery, and `ForMathlib/HypergeometricMoments`
  -- stops at the first two moments (`expect_weight`, `expect_weight_pair`, `cov_weight`,
  -- `var_linear`, `var_mean_linear_le`) — exactly the inputs Hoeffding's condition consumes, but
  -- not the theorem itself. The sign-change engine provably does not cover this case: what makes
  -- `charFun_randPairLaw_signSum` exact at every finite `n` is that averaging `exp(i(sa+s'b))`
  -- over the four sign pairs factorizes across coordinates; the permutation weights are
  -- sampling-**without**-replacement indicators, so the coordinates are dependent and the
  -- characteristic function does not become an `n`-th power.
  -- What changed this session: this is now the *only* open statement in the two-sample
  -- studentized chain. `Studentized.weakConverges_studentizedTwoSample` is closed axiom-clean
  -- (over `weakConverges_twoSampleMeanDiff` below, the new `tendsto_pi_real_lln`, and the
  -- varying-base Slutsky transfer), and `Studentized.randDist_studentized_tendstoInProb` and
  -- `Studentized.studentizedPermTest_asymptotic_level` reduce to this one theorem plus bounded,
  -- self-contained hypergeometric work spelled out in the note there. The two varying-exponent
  -- bricks written for the unconditional companion (`tendsto_one_add_pow_of_tendsto_nat_mul`,
  -- `tendsto_charFun_pow`) remain exactly the shape a Lindeberg-style proof of the conditional
  -- characteristic function would need, so they are reusable here rather than one-off.
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

/-! ### Varying-exponent power limits

The unconditional two-sample limit needs `(1 + gₖ)^{Nₖ} → exp z` with the exponent `Nₖ` an
*arbitrary* sequence tending to infinity (the second sample size `n k`), whereas Mathlib's
`Complex.tendsto_one_add_pow_exp_of_tendsto` forces the exponent to be the index itself.
That, together with a varying characteristic-function argument, is supplied here. -/

/-- **Varying-exponent form of `Complex.tendsto_one_add_pow_exp_of_tendsto`.** If the
exponents `N k` tend to infinity and `N k · g k → z`, then `(1 + g k) ^ (N k) → exp z`. -/
private lemma tendsto_one_add_pow_of_tendsto_nat_mul {N : ℕ → ℕ} {g : ℕ → ℂ} {z : ℂ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hg : Tendsto (fun k => (N k : ℂ) * g k) atTop (𝓝 z)) :
    Tendsto (fun k => (1 + g k) ^ (N k)) atTop (𝓝 (Complex.exp z)) := by
  have hNne : ∀ᶠ k in atTop, (N k : ℂ) ≠ 0 := by
    filter_upwards [hN.eventually_gt_atTop 0] with k hk
    have hk0 : N k ≠ 0 := by
      intro h
      rw [h] at hk
      simp at hk
    exact_mod_cast Nat.cast_ne_zero.2 hk0
  have hinv : Tendsto (fun k => ((N k : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ((N k : ℝ))⁻¹) atTop (𝓝 0) := hN.inv_tendsto_atTop
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    simp only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] at h2
    exact h2
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have h := hinv.mul hg
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [hNne] with k hk
    exact inv_mul_cancel_left₀ hk (g k)
  have hgn : Tendsto (fun k => ‖g k‖) atTop (𝓝 0) := by simpa using hg0.norm
  have hsmall : ∀ᶠ k in atTop, ‖g k‖ < 1 / 2 :=
    hgn.eventually (eventually_lt_nhds (by norm_num))
  have hdiff : Tendsto (fun k => (N k : ℂ) * (Complex.log (1 + g k) - g k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun k => ‖(N k : ℂ) * g k‖ * ‖g k‖) ?_ ?_
    · filter_upwards [hsmall] with k hk
      have hk1 : ‖g k‖ < 1 := hk.trans (by norm_num)
      have hbd := Complex.norm_log_one_add_sub_self_le hk1
      have hinv2 : (1 - ‖g k‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hstep : ‖Complex.log (1 + g k) - g k‖ ≤ ‖g k‖ ^ 2 := by
        refine hbd.trans ?_
        nlinarith [sq_nonneg ‖g k‖, norm_nonneg (g k)]
      calc ‖(N k : ℂ) * (Complex.log (1 + g k) - g k)‖
          = (N k : ℝ) * ‖Complex.log (1 + g k) - g k‖ := by
            rw [norm_mul]; simp
        _ ≤ (N k : ℝ) * ‖g k‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
        _ = ‖(N k : ℂ) * g k‖ * ‖g k‖ := by rw [norm_mul]; simp; ring
    · have h := hg.norm.mul hgn
      simpa using h
  have hlog : Tendsto (fun k => (N k : ℂ) * Complex.log (1 + g k)) atTop (𝓝 z) := by
    have h := hg.add hdiff
    rw [add_zero] at h
    exact h.congr fun k => by ring
  have hexp := (Complex.continuous_exp.tendsto z).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hsmall] with k hk
  have h1 : (1 : ℂ) + g k ≠ 0 := by
    intro h
    have hgk : g k = -1 := by linear_combination h
    rw [hgk] at hk
    norm_num at hk
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log h1]

/-- **Characteristic-function powers with varying exponent and varying argument.** For a
centred law `Q` with second moment `v > 0`, exponents `N k → ∞` and arguments with
`N k · (s k)² → c`, one has `(charFun Q (s k)) ^ (N k) → exp(−v c / 2)`. Both the exponent
and the argument move with `k`, which is what the two-sample statistic requires. -/
private lemma tendsto_charFun_pow {Q : Measure ℝ} [IsProbabilityMeasure Q] {v c : ℝ}
    (hQ0 : ∫ y, y ∂Q = 0) (hQ2 : ∫ y, y ^ 2 ∂Q = v) (hv : 0 < v)
    {N : ℕ → ℕ} (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    {s : ℕ → ℝ} (hs : Tendsto (fun k => (N k : ℝ) * s k ^ 2) atTop (𝓝 c)) :
    Tendsto (fun k => charFun Q (s k) ^ (N k)) atTop
      (𝓝 (Complex.exp (-((v * c : ℝ) : ℂ) / 2))) := by
  obtain ⟨σ, hσpos, hσsq⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = v :=
    ⟨Real.sqrt v, Real.sqrt_pos.2 hv, Real.sq_sqrt hv.le⟩
  -- Standardise: `X y = y / σ` has mean `0` and variance `1` under `Q`.
  have hXm : Measurable (fun y : ℝ => y / σ) := by fun_prop
  have h0 : ∫ y, (fun y : ℝ => y / σ) y ∂Q = 0 := by
    simp only [integral_div, hQ0, zero_div]
  have h1 : ∫ y, ((fun y : ℝ => y / σ) ^ 2) y ∂Q = 1 := by
    simp only [Pi.pow_apply, div_pow, integral_div, hQ2, hσsq]
    exact div_self hv.ne'
  have hR : ∀ w : ℝ, charFun Q w = charFun (Q.map (fun y : ℝ => y / σ)) (σ * w) := by
    intro w
    have h := charFun_map_mul_comp (μ := Q) (f := fun y : ℝ => y / σ) hXm.aemeasurable σ w
    have hid : (fun y : ℝ => σ * (y / σ)) = id := by
      funext y
      change σ * (y / σ) = y
      field_simp
    rw [hid, Measure.map_id] at h
    exact h
  -- The arguments tend to `0`.
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hsq : Tendsto (fun k => s k ^ 2) atTop (𝓝 0) := by
      have h := hs.mul hN.inv_tendsto_atTop
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [hN.eventually_gt_atTop 0] with k hk
      simp only [Pi.inv_apply]
      field_simp
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using h
  have hw0 : Tendsto (fun k => σ * s k) atTop (𝓝 0) := by
    simpa using hs0.const_mul σ
  have hNw : Tendsto (fun k => (N k : ℝ) * (σ * s k) ^ 2) atTop (𝓝 (v * c)) := by
    have h : Tendsto (fun k => σ ^ 2 * ((N k : ℝ) * s k ^ 2)) atTop (𝓝 (σ ^ 2 * c)) :=
      hs.const_mul _
    rw [hσsq] at h
    refine h.congr fun k => ?_
    rw [← hσsq]
    ring
  -- Second-order Taylor expansion of the characteristic function at the moving argument.
  have hlittle := (taylor_charFun_two (P := Q) (X := fun y : ℝ => y / σ)
    hXm.aemeasurable h0 h1).comp_tendsto hw0
  -- The rescaled remainder is negligible against the exponent.
  have hB : Tendsto (fun k => (N k : ℂ) * (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
      (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2))) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hMpos : (0 : ℝ) < |v * c| + 1 := by positivity
    have hbound := hlittle.def (show (0 : ℝ) < ε / (2 * (|v * c| + 1)) by positivity)
    have hAle : ∀ᶠ k in atTop, (N k : ℝ) * (σ * s k) ^ 2 ≤ |v * c| + 1 := by
      have hlt : v * c < |v * c| + 1 := lt_of_le_of_lt (le_abs_self _) (by linarith)
      filter_upwards [hNw.eventually (eventually_lt_nhds hlt)] with k hk using hk.le
    filter_upwards [hbound, hAle] with k hk hkA
    have hnn : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
    have hkey : (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
        (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖
        ≤ ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hk hnn
      calc (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
              (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖
          ≤ (N k : ℝ) * (ε / (2 * (|v * c| + 1)) * ‖(σ * s k) ^ 2‖) := this
        _ = ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (σ * s k))]; ring
    have hfin : ε / (2 * (|v * c| + 1)) * ((N k : ℝ) * (σ * s k) ^ 2) < ε := by
      have hcpos : (0 : ℝ) < ε / (2 * (|v * c| + 1)) := by positivity
      have := mul_le_mul_of_nonneg_left hkA hcpos.le
      have hhalf : ε / (2 * (|v * c| + 1)) * (|v * c| + 1) = ε / 2 := by
        field_simp
      rw [hhalf] at this
      linarith
    calc ‖(N k : ℂ) * (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
            (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2))‖
        = (N k : ℝ) * ‖charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) -
            (1 - ((σ * s k : ℝ) : ℂ) ^ 2 / 2)‖ := by rw [norm_mul]; simp
      _ ≤ _ := hkey
      _ < ε := hfin
  -- The quadratic term supplies the exponent.
  have hA : Tendsto (fun k => (N k : ℂ) * (-(((σ * s k : ℝ) : ℂ) ^ 2) / 2)) atTop
      (𝓝 (-((v * c : ℝ) : ℂ) / 2)) := by
    have hreal : Tendsto (fun k => -((N k : ℝ) * (σ * s k) ^ 2) / 2) atTop (𝓝 (-(v * c) / 2)) :=
      hNw.neg.div_const 2
    have h := (Complex.continuous_ofReal.tendsto (-(v * c) / 2)).comp hreal
    simp only [Function.comp_def] at h
    push_cast at h ⊢
    exact h.congr fun k => by ring
  have hgz : Tendsto (fun k => (N k : ℂ) *
      (charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) - 1)) atTop
      (𝓝 (-((v * c : ℝ) : ℂ) / 2)) := by
    have h := hA.add hB
    rw [add_zero] at h
    exact h.congr fun k => by ring
  have hbrick := tendsto_one_add_pow_of_tendsto_nat_mul (N := N)
    (g := fun k => charFun (Q.map (fun y : ℝ => y / σ)) (σ * s k) - 1) hN hgz
  refine hbrick.congr fun k => ?_
  rw [hR (s k)]
  congr 1
  ring

/-! ### Linear form of the statistic and the product characteristic function -/

/-- The linear coefficients of the difference-of-means statistic on the pooled data:
`√m/m` on the first block and `−√m/n` on the second. -/
private noncomputable def twoSampleCoef (m n : ℕ) : Fin (m + n) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) (fun _ => Real.sqrt m * (m : ℝ)⁻¹)
    (fun _ => -(Real.sqrt m * (n : ℝ)⁻¹))

/-- The statistic is the linear form with those coefficients. -/
private lemma twoSampleMeanDiff_eq_sum (m n : ℕ) (x : Fin (m + n) → ℝ) :
    twoSampleMeanDiff m n x = ∑ l, twoSampleCoef m n l * x l := by
  rw [Fin.sum_univ_add]
  simp only [twoSampleCoef, Fin.addCases_left, Fin.addCases_right, twoSampleMeanDiff]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The characteristic function of a linear form of independent coordinates factorizes. -/
private lemma charFun_map_sum_pi {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (c : Fin N → ℝ) (t : ℝ) :
    charFun ((Measure.pi ν).map (fun x => ∑ i, c i * x i)) t = ∏ i, charFun (ν i) (c i * t) := by
  have hmeas : ∀ i : Fin N, AEMeasurable (fun x : Fin N → ℝ => c i * x i) (Measure.pi ν) :=
    fun i => Measurable.aemeasurable (by fun_prop)
  have hindep : iIndepFun (fun (i : Fin N) (x : Fin N → ℝ) => c i * x i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun (i : Fin N) (y : ℝ) => c i * y) (fun i => by fun_prop)
  rw [hindep.charFun_map_fun_sum_eq_prod hmeas, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFun_map_mul_comp (measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval ν i).map_eq]

/-- Each coordinate of the pooled family is a probability measure. -/
private lemma isProbabilityMeasure_addCases (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (i : Fin (m + n)) :
    IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
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

/-- **The exact finite-sample characteristic function of the two-sample statistic.** -/
private lemma charFun_map_twoSampleMeanDiff (m n : ℕ) (PY PZ : Measure ℝ)
    [IsProbabilityMeasure PY] [IsProbabilityMeasure PZ] (t : ℝ) :
    charFun ((twoSampleLaw m n PY PZ).map (twoSampleMeanDiff m n)) t
      = charFun PY (Real.sqrt m * (m : ℝ)⁻¹ * t) ^ m
        * charFun PZ (-(Real.sqrt m * (n : ℝ)⁻¹) * t) ^ n := by
  haveI hfam := isProbabilityMeasure_addCases m n PY PZ
  have hsum : twoSampleMeanDiff m n = fun x => ∑ l, twoSampleCoef m n l * x l :=
    funext fun x => twoSampleMeanDiff_eq_sum m n x
  rw [twoSampleLaw, hsum, charFun_map_sum_pi, Fin.prod_univ_add]
  simp only [twoSampleCoef, Fin.addCases_left, Fin.addCases_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

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
  -- Reduce to characteristic functions, factorize exactly at each finite `k` into the two
  -- per-block powers, recentre both populations at the common mean `μ` (the phase factors
  -- cancel because `mα + nβ = 0`), and apply the varying-exponent power limit to each block.
  classical
  set QY := PY.map (fun y : ℝ => y + (-μ)) with hQYdef
  set QZ := PZ.map (fun y : ℝ => y + (-μ)) with hQZdef
  haveI : IsProbabilityMeasure QY := by
    rw [hQYdef]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure QZ := by
    rw [hQZdef]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hIY : Integrable (fun y : ℝ => y) PY := by simpa using hYL2.integrable (by norm_num)
  have hIZ : Integrable (fun y : ℝ => y) PZ := by simpa using hZL2.integrable (by norm_num)
  -- The centred laws have mean `0` and the two population variances.
  have hQY0 : ∫ y, y ∂QY = 0 := by
    rw [hQYdef, integral_map (by fun_prop) (by fun_prop),
      integral_add hIY (integrable_const _), hmeanY]
    simp
  have hQZ0 : ∫ y, y ∂QZ = 0 := by
    rw [hQZdef, integral_map (by fun_prop) (by fun_prop),
      integral_add hIZ (integrable_const _), hmeanZ]
    simp
  have hQY2 : ∫ y, y ^ 2 ∂QY = varY := by
    rw [hQYdef, integral_map (by fun_prop) (by fun_prop)]
    simp only [← sub_eq_add_neg]
    exact hvarY
  have hQZ2 : ∫ y, y ^ 2 ∂QZ = varZ := by
    rw [hQZdef, integral_map (by fun_prop) (by fun_prop)]
    simp only [← sub_eq_add_neg]
    exact hvarZ
  -- Recentring only multiplies the characteristic function by a phase.
  have hPYchar : ∀ w : ℝ,
      charFun PY w = charFun QY w * Complex.exp ((μ : ℂ) * (w : ℂ) * Complex.I) := by
    intro w
    have hinner : (inner ℝ (-μ) w : ℝ) = -(μ * w) := by
      have h0 : (inner ℝ (-μ) w : ℝ) = w * (-μ) := rfl
      rw [h0]; ring
    have h := charFun_map_add_const (μ := PY) (-μ) w
    rw [hinner, ← hQYdef] at h
    rw [h, mul_assoc, ← Complex.exp_add]
    have hz : ((-(μ * w) : ℝ) : ℂ) * Complex.I + (μ : ℂ) * (w : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [hz, Complex.exp_zero, mul_one]
  have hPZchar : ∀ w : ℝ,
      charFun PZ w = charFun QZ w * Complex.exp ((μ : ℂ) * (w : ℂ) * Complex.I) := by
    intro w
    have hinner : (inner ℝ (-μ) w : ℝ) = -(μ * w) := by
      have h0 : (inner ℝ (-μ) w : ℝ) = w * (-μ) := rfl
      rw [h0]; ring
    have h := charFun_map_add_const (μ := PZ) (-μ) w
    rw [hinner, ← hQZdef] at h
    rw [h, mul_assoc, ← Complex.exp_add]
    have hz : ((-(μ * w) : ℝ) : ℂ) * Complex.I + (μ : ℂ) * (w : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [hz, Complex.exp_zero, mul_one]
  have hmR : Tendsto (fun k => (m k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  haveI hprob : ∀ k, IsProbabilityMeasure
      ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))) := fun k =>
    Measure.isProbabilityMeasure_map (measurable_twoSampleMeanDiff _ _).aemeasurable
  refine weakConverges_of_tendsto_charFun (fun t => ?_)
  -- The two exponent-times-argument-squared limits: `m α² t² → t²` and `n β² t² → λ t²`.
  have hsY : Tendsto (fun k => (m k : ℝ) * (Real.sqrt (m k) * (m k : ℝ)⁻¹ * t) ^ 2) atTop
      (𝓝 (t ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hk
    have hmk : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hk
    have hne : (m k : ℝ) ≠ 0 := hmk.ne'
    have hsq : Real.sqrt (m k) ^ 2 = (m k : ℝ) := Real.sq_sqrt hmk.le
    have hexp : (Real.sqrt (m k) * (m k : ℝ)⁻¹ * t) ^ 2
        = Real.sqrt (m k) ^ 2 * ((m k : ℝ)⁻¹) ^ 2 * t ^ 2 := by ring
    rw [hexp, hsq]
    field_simp
  have hsZ : Tendsto (fun k => (n k : ℝ) * (-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t) ^ 2) atTop
      (𝓝 (lam * t ^ 2)) := by
    refine (hratio.mul_const (t ^ 2)).congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0] with k hmk hnk
    have hmk' : (0 : ℝ) < (m k : ℝ) := by exact_mod_cast hmk
    have hnk' : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hnk
    have hne : (n k : ℝ) ≠ 0 := hnk'.ne'
    have hsq : Real.sqrt (m k) ^ 2 = (m k : ℝ) := Real.sq_sqrt hmk'.le
    have hexp : (-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t) ^ 2
        = Real.sqrt (m k) ^ 2 * ((n k : ℝ)⁻¹) ^ 2 * t ^ 2 := by ring
    rw [hexp, hsq]
    field_simp
  have hY := tendsto_charFun_pow hQY0 hQY2 hvarYpos hmR hsY
  have hZ := tendsto_charFun_pow hQZ0 hQZ2 hvarZpos hnR hsZ
  have hprod := hY.mul hZ
  -- The limit is the characteristic function of `N(0, s²)`.
  have htarget : charFun (gaussianReal 0 (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0)) t
      = Complex.exp (-((varY * t ^ 2 : ℝ) : ℂ) / 2) *
        Complex.exp (-((varZ * (lam * t ^ 2) : ℝ) : ℂ) / 2) := by
    have hsC : ((s : ℂ)) ^ 2 = (varY : ℂ) + (lam : ℂ) * (varZ : ℂ) := by
      exact_mod_cast congrArg (Complex.ofReal) hs
    rw [charFun_gaussianReal, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hsC]
    ring
  rw [htarget]
  refine hprod.congr' ?_
  filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0] with k hmk hnk
  have hmC : ((m k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hmk.ne'
  have hnC : ((n k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hnk.ne'
  -- The two phase factors cancel: `m α + n β = 0`.
  have hcancel :
      Complex.exp ((μ : ℂ) * ((Real.sqrt (m k) * (m k : ℝ)⁻¹ * t : ℝ) : ℂ) * Complex.I) ^ (m k)
        * Complex.exp ((μ : ℂ) *
            ((-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t : ℝ) : ℂ) * Complex.I) ^ (n k) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hz : ((m k : ℕ) : ℂ) *
          ((μ : ℂ) * ((Real.sqrt (m k) * (m k : ℝ)⁻¹ * t : ℝ) : ℂ) * Complex.I)
        + ((n k : ℕ) : ℂ) *
          ((μ : ℂ) * ((-(Real.sqrt (m k) * (n k : ℝ)⁻¹) * t : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast
      field_simp
      ring
    rw [hz, Complex.exp_zero]
  rw [charFun_map_twoSampleMeanDiff, hPYchar, hPZchar, mul_pow, mul_pow, mul_mul_mul_comm,
    hcancel, mul_one]

/-! ### A reusable `L¹` law of large numbers on `Measure.pi`

The randomization limits in this directory are all statements about product measures
`Measure.pi (fun _ : Fin n => P)` whose summands are only `L¹` — sample second moments of an
`L²` observation, for instance — so Chebyshev's inequality is unavailable and the honest
route is Kolmogorov's strong law. The following brick packages that route once: it lifts the
`Fin n` product to the Kolmogorov extension `Measure.infinitePi` on `ℕ → Ω`, applies
`ProbabilityTheory.strong_law_ae_real`, converts a.e. convergence to convergence in measure,
and pulls the resulting sets back along
`AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate`.

It is stated in the `Measure.real` form the randomization `hrem` hypotheses consume, and is
used by `Randomization/MultivariateQuadratic` (consistency of the uncentred second-moment
matrix) and by `Randomization/Studentized` (consistency of the studentizing scale). -/

/-- **`L¹` weak law of large numbers on a finite product measure.** For an integrable `f`,
the empirical mean of `f` along the coordinates converges to `∫ f ∂P` in
`Measure.pi (fun _ : Fin n => P)`-probability as `n → ∞`.

Note the two-parameter structure: the *measure* and the *statistic* both depend on `n`, so
this is a triangular-array statement rather than a limit along a single probability space;
that is exactly why it goes through the Kolmogorov extension rather than through
`ProbabilityTheory.strong_law_ae_real` directly. -/
lemma tendsto_pi_real_lln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    -- USER-INPUT: the summand has a finite first moment; the classical hypothesis
    (f : Ω → ℝ) (hf : Integrable f P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).real
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|})
      atTop (𝓝 0) := by
  classical
  set μ_inf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hμ_inf
  have hf_aesm : AEStronglyMeasurable f P := hf.aestronglyMeasurable
  set f' : Ω → ℝ := hf_aesm.mk f with hf'_def
  have hf'_meas : Measurable f' := hf_aesm.measurable_mk
  have hff' : f =ᵐ[P] f' := hf_aesm.ae_eq_mk
  have hf'_int : Integrable f' P := hf.congr hff'
  have hf_integral : ∫ ω, f' ω ∂P = ∫ ω, f ω ∂P := integral_congr_ae hff'.symm
  set Y : ℕ → (ℕ → Ω) → ℝ := fun i ω => f' (ω i) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hf'_meas.comp (measurable_pi_apply i)
  have hMP : ∀ i : ℕ, MeasurePreserving (Function.eval i : (ℕ → Ω) → Ω) μ_inf P :=
    fun i => measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  have hY0_int : Integrable (Y 0) μ_inf := by
    have := (hMP 0).integrable_comp hf'_meas.aestronglyMeasurable
    simpa [Y, Function.eval] using this.mpr hf'_int
  have h_iIndep : ProbabilityTheory.iIndepFun Y μ_inf := by
    simpa [Y, Function.eval] using
      (ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Ω)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f') (fun _ => hf'_meas))
  have h_pair :
      Pairwise (Function.onFun
        (fun X₁ X₂ : (ℕ → Ω) → ℝ => ProbabilityTheory.IndepFun X₁ X₂ μ_inf) Y) :=
    fun i j hij => h_iIndep.indepFun hij
  have hY_map : ∀ i, Measure.map (Y i) μ_inf = Measure.map f' P := by
    intro i
    have h_comp : Y i = f' ∘ (Function.eval i : (ℕ → Ω) → Ω) := by funext ω; rfl
    rw [h_comp, ← Measure.map_map hf'_meas (measurable_pi_apply i), (hMP i).map_eq]
  have h_ident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ_inf μ_inf := fun i =>
    { aemeasurable_fst := (hY_meas i).aemeasurable
      aemeasurable_snd := (hY_meas 0).aemeasurable
      map_eq := by rw [hY_map i, hY_map 0] }
  have h_mean : ∫ ω, Y 0 ω ∂μ_inf = ∫ ω, f ω ∂P := by
    have h_int : ∫ ω, f' ω ∂P = ∫ ω, Y 0 ω ∂μ_inf := by
      have hP_eq : P = Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := (hMP 0).map_eq.symm
      calc ∫ ω, f' ω ∂P
          = ∫ ω, f' ω ∂Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := by rw [← hP_eq]
        _ = ∫ ω, f' ((Function.eval 0 : (ℕ → Ω) → Ω) ω) ∂μ_inf := by
            refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
            exact hf'_meas.aestronglyMeasurable
        _ = ∫ ω, Y 0 ω ∂μ_inf := by rfl
    rw [← h_int, hf_integral]
  have h_sllN : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n) atTop (𝓝 (∫ ω, Y 0 ω ∂μ_inf)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int h_pair h_ident
  have h_ae_eq : ∀ᵐ ω ∂μ_inf, ∀ i : ℕ, f (ω i) = f' (ω i) := by
    rw [ae_all_iff]
    intro i
    exact ((hMP i).quasiMeasurePreserving).ae_eq hff'
  have h_target_ae : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) atTop (𝓝 (∫ ω, f ω ∂P)) := by
    filter_upwards [h_sllN, h_ae_eq] with ω h_lim h_eq_all
    have h_seq_eq : ∀ n : ℕ,
        (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) = (∑ i ∈ Finset.range n, Y i ω) / n := by
      intro n
      have h_sum : (∑ i : Fin n, f (ω i)) = ∑ i ∈ Finset.range n, Y i ω := by
        rw [← Fin.sum_univ_eq_sum_range fun i => Y i ω]
        exact Finset.sum_congr rfl fun i _ => h_eq_all i.val
      rw [h_sum]; ring
    rw [funext h_seq_eq, ← h_mean]
    exact h_lim
  have hF_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω : ℕ → Ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) μ_inf := by
    intro n
    refine AEStronglyMeasurable.const_mul ?_ _
    refine Finset.aestronglyMeasurable_fun_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ω => f (ω i.val)) (μ := μ_inf) (fun i _ => ?_)
    exact hf_aesm.comp_measurePreserving (hMP i.val)
  have h_in_meas : MeasureTheory.TendstoInMeasure μ_inf
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) atTop (fun _ => ∫ ω, f ω ∂P) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas h_target_ae
  have h_norm := (MeasureTheory.tendstoInMeasure_iff_norm (μ := μ_inf) (l := atTop)
      (f := fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
      (g := fun _ => ∫ ω, f ω ∂P)).mp h_in_meas
  have h_inf := h_norm ε hε
  have h_set_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
      = μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
    intro n
    have h_pi_ae : (fun (x : Fin n → Ω) i => f (x i)) =ᵐ[Measure.pi (fun _ : Fin n => P)]
        fun (x : Fin n → Ω) i => f' (x i) :=
      MeasureTheory.Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ => f) (f' := fun _ => f') (fun _ => hff')
    have h_pi_set_eq :
        (Measure.pi (fun _ : Fin n => P))
          {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
        = (Measure.pi (fun _ : Fin n => P))
          {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_pi_ae] with x hx
      have h_sum_eq : (∑ i : Fin n, f (x i)) = (∑ i : Fin n, f' (x i)) :=
        Finset.sum_congr rfl fun i _ => congrFun hx i
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|) =
             (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|)
      rw [h_sum_eq]
    have hms_f' : MeasurableSet
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|} := by
      refine measurableSet_le measurable_const ?_
      refine (Measurable.sub ?_ measurable_const).abs
      exact (Finset.measurable_sum _ fun i _ => hf'_meas.comp (measurable_pi_apply i)).const_mul _
    have hbridge_f' :=
      AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate (ν := P) n hms_f'
    have h_inf_set_eq :
        μ_inf {ω : ℕ → Ω | (fun i : Fin n => ω i.val) ∈
              {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (x i)) - ∫ ω, f ω ∂P|}}
          = μ_inf {ω : ℕ → Ω |
            ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_ae_eq] with ω hω
      have h_sum_eq : (∑ i : Fin n, f' (ω i.val)) = (∑ i : Fin n, f (ω i)) :=
        Finset.sum_congr rfl fun i _ => (hω i.val).symm
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (ω i.val)) - ∫ ω, f ω ∂P|) =
             (ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖)
      rw [Real.norm_eq_abs, h_sum_eq]
    rw [h_pi_set_eq, hbridge_f', h_inf_set_eq]
  have hreal : ∀ n : ℕ, (Measure.pi (fun _ : Fin n => P)).real
        {x : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (x i)) - ∫ ω, f ω ∂P|}
      = (μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖}).toReal := by
    intro n; rw [Measure.real, h_set_eq n]
  simp_rw [hreal]
  have := (ENNReal.tendsto_toReal (by simp)).comp h_inf
  simpa using this

end StatLean.HypothesisTesting
