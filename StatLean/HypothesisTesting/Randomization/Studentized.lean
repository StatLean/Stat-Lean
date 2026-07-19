import StatLean.HypothesisTesting.Randomization.TwoSamplePermutation
import StatLean.HypothesisTesting.Randomization.SlutskyRandomization

/-!
# The studentized two-sample permutation test

The unstudentized two-sample permutation test compares a statistic whose permutation
variance $\lambda\sigma^2(P_Y) + \sigma^2(P_Z)$ differs from its true sampling variance
$\sigma^2(P_Y) + \lambda\sigma^2(P_Z)$ whenever the variances differ and the sample sizes
are unbalanced, so its asymptotic rejection probability need not equal $\alpha$ for testing
equality of *means*. Studentizing repairs this. Put
$$ \tilde T_{m,n} = \frac{T_{m,n}}{D_{m,n}}, \qquad
   D_{m,n}^2 = S_Y^2 + \frac{m}{n} S_Z^2 , $$
with $S_Y^2 = m^{-1}\sum_i (Y_i - \bar Y_m)^2$ and
$S_Z^2 = n^{-1}\sum_j (Z_j - \bar Z_n)^2$. Then

* the randomization distribution of $\tilde T_{m,n}$ converges in probability to the
  standard normal c.d.f., $\hat R^{\tilde T}_{m,n}(t) \xrightarrow{P} \Phi(t)$;
* the unconditional law also converges, $\tilde T_{m,n} \xrightarrow{d} N(0,1)$;

so the two match and the permutation test based on $\tilde T_{m,n}$ is asymptotically
level $\alpha$ — pointwise consistent in level — **even when the two populations have
different variances and the sample sizes are unbalanced**. When the populations are
identical the randomization hypothesis holds and the test is additionally *exact* at every
finite sample size, so studentization costs nothing.

**Reference.** Classical randomization/permutation testing; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* *The exact studentization.* The scale is the one displayed above, $D^2 = S_Y^2 +
  (m/n)S_Z^2$, with both sample variances normalized by the sample size (not by
  $m-1$, $n-1$); this is the divisor the statement is proved with, and it is what makes
  $\tilde T_{m,n}$ pivotal.
* *Relation to the two-sample $t$-statistic.* Dividing numerator and denominator by
  $\sqrt m$ turns $\tilde T_{m,n}$ into
  $(\bar Y_m - \bar Z_n)/\sqrt{S_Y^2/m + S_Z^2/n}$, i.e. the two-sample $t$-statistic with
  **unpooled (Welch) standardization**; `studentizedTwoSample_eq_welch` records this
  algebraic identity. So the level statement below applies verbatim to that statistic
  without any equal-variance assumption. This is a different claim from the classical
  remark that the *pooled* two-sample $t$-test is asymptotically equivalent to the
  unstudentized permutation test — that comparison does require equal variances (or
  $\lambda = 1$), and is not asserted here.
* *Route.* Combining the two-sample permutation limit for the numerator with the Slutsky
  transfer for randomization distributions reduces the claim to showing that the
  studentizing scale, evaluated at a random permutation of the pooled data, converges in
  probability to the permutation scale $\tau$. That is a statement about the first two
  moments of a random sample drawn without replacement from the pooled data, and it is why
  the scale is *not* assumed group-invariant anywhere: it is not, and the Slutsky transfer
  is stated exactly to accommodate that.
* *Degenerate corners.* `twoSampleScale` can vanish (constant data), in which case
  `studentizedTwoSample` returns the junk value `x / 0 = 0`; the statistic is total. Under
  the standing hypotheses (nonzero population variances, sample sizes tending to infinity)
  the scale is eventually positive with probability tending to one, so the corner is
  asymptotically negligible rather than excluded by fiat.
* *No equal-variance hypothesis appears in any statement below* — that absence is the
  content of the theorem.

**Bibliographic comments.** That studentization restores asymptotic validity of the
two-sample permutation test under unequal variances is due to A. Janssen ("Studentized
permutation tests for non-i.i.d. hypotheses and the generalized Behrens–Fisher problem,"
*Statist. Probab. Lett.* **36** (1997), 9–21); the general principle — construct test
statistics whose limiting distribution is free of unknown parameters — was developed by
E. Chung and J. P. Romano ("Exact and asymptotically robust permutation tests," *Ann.
Statist.* **41** (2013), 484–507). The failure it repairs was identified by J. P. Romano
("On the behavior of randomization tests without a group invariance assumption," *J. Amer.
Statist. Assoc.* **85** (1990), 686–692; see also "Bootstrap and randomization tests of
some nonparametric hypotheses," *Ann. Statist.* **17** (1989), 141–159). The underlying
permutation limit theory is W. Hoeffding ("The large-sample power of tests based on
permutations of observations," *Ann. Math. Statist.* **23** (1952), 169–192), and the
exact finite-sample theory R. A. Fisher (*The Design of Experiments*, Oliver & Boyd,
Edinburgh, 1935), E. J. G. Pitman ("Significance tests which may be applied to samples
from any populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130) and
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45); sampling the group rather than enumerating it is
M. Dwass ("Modified randomization tests for nonparametric hypotheses," *Ann. Math.
Statist.* **28** (1957), 181–187).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The studentized statistic -/

/-- Sample mean of the first block (the `Y` sample) of the pooled data. -/
noncomputable def twoSampleMeanY (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, x (Fin.castAdd n i)

/-- Sample mean of the second block (the `Z` sample) of the pooled data. -/
noncomputable def twoSampleMeanZ (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j : Fin n, x (Fin.natAdd m j)

/-- The difference-of-means statistic in terms of the two block means. -/
lemma twoSampleMeanDiff_eq (m n : ℕ) (x : Fin (m + n) → ℝ) :
    twoSampleMeanDiff m n x =
      Real.sqrt (m : ℝ) * (twoSampleMeanY m n x - twoSampleMeanZ m n x) := rfl

/-- Sample variance of the `Y` block, normalized by `m`. -/
noncomputable def twoSampleVarY (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, (x (Fin.castAdd n i) - twoSampleMeanY m n x) ^ 2

/-- Sample variance of the `Z` block, normalized by `n`. -/
noncomputable def twoSampleVarZ (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j : Fin n, (x (Fin.natAdd m j) - twoSampleMeanZ m n x) ^ 2

/-- The **studentizing scale** `D_{m,n} = √(S²_Y + (m/n) S²_Z)`. -/
noncomputable def twoSampleScale (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  Real.sqrt (twoSampleVarY m n x + (m : ℝ) / n * twoSampleVarZ m n x)

/-- The **studentized two-sample statistic** `T̃_{m,n} = T_{m,n} / D_{m,n}`. Total: a
vanishing scale gives the junk value `0`. -/
noncomputable def studentizedTwoSample (m n : ℕ) (x : Fin (m + n) → ℝ) : ℝ :=
  twoSampleMeanDiff m n x / twoSampleScale m n x

/-- **The studentized permutation statistic is the unpooled (Welch) two-sample
`t`-statistic.** Dividing through by `√m`,
$$ \tilde T_{m,n} = \frac{\bar Y_m - \bar Z_n}{\sqrt{S_Y^2/m + S_Z^2/n}} , $$
an algebraic identity requiring no distributional assumption. Consequently every
asymptotic-level statement below is a statement about that `t`-statistic as well — with no
equal-variance assumption anywhere. -/
theorem studentizedTwoSample_eq_welch {m n : ℕ}
    -- USER-INPUT: both samples are nonempty, so the sample means are genuine averages
    (hm : 0 < m) (hn : 0 < n) (x : Fin (m + n) → ℝ) :
    studentizedTwoSample m n x =
      (twoSampleMeanY m n x - twoSampleMeanZ m n x) /
        Real.sqrt (twoSampleVarY m n x / m + twoSampleVarZ m n x / n) := by
  sorry

/-! ### Asymptotic validity under unequal variances -/

/-- **The studentized randomization distribution converges to the standard normal.**
Under equal means, finite nonzero (and possibly **different**) population variances, and
`m/n → λ ∈ (0, ∞)`,
$$ \hat R^{\tilde T}_{m,n}(t) \;\xrightarrow{P}\; \Phi(t) . $$
The limit carries no unknown parameter — that is what studentization buys. -/
theorem randDist_studentized_tendstoInProb (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ : ℝ}
    -- USER-INPUT: both sample sizes grow; the asymptotic regime
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: the two populations have the same mean; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances; note they are **not** assumed equal
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    -- USER-INPUT: both variances are nonzero
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ) (t : ℝ) :
    TendstoInProbTriangular (fun k => twoSampleLaw (m k) (n k) PY PZ)
      (fun k x => randDist (Equiv.Perm (Fin (m k + n k)))
        (studentizedTwoSample (m k) (n k)) x t)
      (cdf (gaussianReal 0 1) t) := by
  sorry

/-- **The unconditional law of the studentized statistic is asymptotically standard
normal.** Together with the previous statement, the randomization distribution and the
true sampling distribution have the *same* limit — the matching that the unstudentized
statistic fails to achieve. -/
theorem weakConverges_studentizedTwoSample (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, not assumed equal, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ) :
    WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map (studentizedTwoSample (m k) (n k)))
      (gaussianReal 0 1) := by
  sorry

/-- **The studentized permutation test is pointwise consistent in level.** Its rejection
probability tends to the nominal level,
$$ E_{P_Y^m \times P_Z^n}\bigl[\phi_{m,n}\bigr] \;\longrightarrow\; \alpha , $$
for testing equality of means, with no equal-variance and no balanced-sample-size
assumption. (If the two populations coincide, the randomization hypothesis holds and the
test is exactly level `α` at every finite sample size.) -/
theorem studentizedPermTest_asymptotic_level (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ α : ℝ}
    -- USER-INPUT: both sample sizes grow
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    -- USER-INPUT: `m/n → λ`, with a nondegenerate limit
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam)) (hlam : 0 < lam)
    -- USER-INPUT: finite second moments of both populations
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    -- USER-INPUT: equal means; the null hypothesis under test
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    -- USER-INPUT: the population variances, not assumed equal, both nonzero
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hvarYpos : 0 < varY) (hvarZpos : 0 < varZ)
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    Tendsto (fun k => powerAgainst (twoSampleLaw (m k) (n k) PY PZ)
        (randTest (Equiv.Perm (Fin (m k + n k))) (studentizedTwoSample (m k) (n k)) α))
      atTop (𝓝 α) := by
  sorry

end StatLean.HypothesisTesting
