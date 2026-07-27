import StatLean.HypothesisTesting.Randomization.TwoSamplePermutation
import StatLean.HypothesisTesting.Randomization.SlutskyRandomization
import StatLean.AsymptoticStatistics.ForMathlib.Slutsky

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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.3 (asymptotic
validity of the studentized two-sample permutation test). (`TSH4 §17.3 Thm 17.3.3`.)

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
open scoped ENNReal NNReal

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
  rw [studentizedTwoSample, twoSampleScale, twoSampleMeanDiff_eq]
  set a := twoSampleVarY m n x with ha
  set b := twoSampleVarZ m n x with hb
  set D := twoSampleMeanY m n x - twoSampleMeanZ m n x with hD
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkey : Real.sqrt (a + (m : ℝ) / n * b) =
      Real.sqrt m * Real.sqrt (a / m + b / n) := by
    rw [← Real.sqrt_mul hmR.le]
    congr 1
    field_simp
  rw [hkey, mul_div_mul_left _ _ (Real.sqrt_ne_zero'.2 hmR)]

/-! ### A small calculus for convergence in probability along a triangular array

The studentizing scale is built from the sample moments by four operations — sum, product
with a deterministic factor, square root, reciprocal — and the argument needs each of them to
pass to the limit *in probability*, on a space that changes with `n`. Mathlib's continuous
mapping theorems are for a fixed space, so the three closure properties are recorded here in
the `TendstoInProbTriangular`-style `Measure.real` form used throughout this directory. -/

/-- **Continuous mapping in probability.** Composing with a map continuous at the limit
preserves convergence in probability. -/
private lemma tendstoInProb_comp {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f : ∀ n, 𝓧 n → ℝ} {a : ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousAt φ a)
    (h : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ),
      Tendsto (fun n => (P n).real {x | ε ≤ |φ (f n x) - φ a|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hφ ε hε
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) (h ρ hρpos)
  refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hx ⊢
  by_contra hcon
  push Not at hcon
  have hd : dist (f n x) a < ρ := by rwa [Real.dist_eq]
  have := hρ hd
  rw [Real.dist_eq] at this
  linarith

/-- **Sums pass to the limit in probability.** -/
private lemma tendstoInProb_add {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f g : ∀ n, 𝓧 n → ℝ} {a b : ℝ}
    (hf : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0))
    (hg : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |g n x - b|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real
      {x | ε ≤ |(f n x + g n x) - (a + b)|}) atTop (𝓝 0) := by
  intro ε hε
  have hbound : ∀ n : ℕ, (P n).real {x | ε ≤ |(f n x + g n x) - (a + b)|}
      ≤ (P n).real {x | ε / 2 ≤ |f n x - a|} + (P n).real {x | ε / 2 ≤ |g n x - b|} := by
    intro n
    have hincl : {x : 𝓧 n | ε ≤ |(f n x + g n x) - (a + b)|}
        ⊆ {x | ε / 2 ≤ |f n x - a|} ∪ {x | ε / 2 ≤ |g n x - b|} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri := abs_add_le (f n x - a) (g n x - b)
      have heq : (f n x + g n x) - (a + b) = (f n x - a) + (g n x - b) := by ring
      rw [heq] at hx
      linarith
    exact (measureReal_mono hincl (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  refine squeeze_zero (fun n => measureReal_nonneg) hbound ?_
  simpa using (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))

/-- **Multiplication by a deterministic convergent factor.** This is where the sample-size
ratio `m/n → λ` enters the studentizing scale. -/
private lemma tendstoInProb_const_mul {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {P : ∀ n, Measure (𝓧 n)} [∀ n, IsProbabilityMeasure (P n)]
    {f : ∀ n, 𝓧 n → ℝ} {c : ℕ → ℝ} {a cl : ℝ}
    (hc : Tendsto c atTop (𝓝 cl))
    (hf : ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - a|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real
      {x | ε ≤ |c n * f n x - cl * a|}) atTop (𝓝 0) := by
  intro ε hε
  have hpos : (0 : ℝ) < |cl| + 1 := by positivity
  set ρ : ℝ := ε / (2 * (|cl| + 1)) with hρdef
  have hρpos : 0 < ρ := by positivity
  have hev1 : ∀ᶠ n in atTop, |c n| ≤ |cl| + 1 := by
    have := hc.abs.eventually (eventually_lt_nhds (show |cl| < |cl| + 1 by linarith))
    exact this.mono fun n hn => hn.le
  have hev2 : ∀ᶠ n in atTop, |c n - cl| * |a| < ε / 2 := by
    have hlim : Tendsto (fun n => |c n - cl| * |a|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => c n - cl) atTop (𝓝 0) := by
        simpa using hc.sub_const cl
      simpa using (h0.abs).mul_const |a|
    exact hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hbound : ∀ᶠ n in atTop, (P n).real {x | ε ≤ |c n * f n x - cl * a|}
      ≤ (P n).real {x | ρ ≤ |f n x - a|} := by
    filter_upwards [hev1, hev2] with n hn1 hn2
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hcon
    push Not at hcon
    have hsplit : c n * f n x - cl * a = c n * (f n x - a) + (c n - cl) * a := by ring
    have h1 : |c n * (f n x - a)| ≤ (|cl| + 1) * ρ := by
      rw [abs_mul]
      exact mul_le_mul hn1 hcon.le (abs_nonneg _) (by positivity)
    have h2 : (|cl| + 1) * ρ = ε / 2 := by rw [hρdef]; field_simp
    have h3 : |(c n - cl) * a| < ε / 2 := by rw [abs_mul]; exact hn2
    have htri := abs_add_le (c n * (f n x - a)) ((c n - cl) * a)
    rw [hsplit] at hx
    linarith
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) hbound ?_
  exact hf ρ hρpos

/-! ### The two blocks of the pooled law -/

/-- The `Y`-block coordinates of the pooled sample are an i.i.d. `P_Y` sample: the block
projection pushes the pooled law forward onto the `Y`-product. -/
private lemma map_projY (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] :
    (twoSampleLaw m n PY PZ).map
        (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i))
      = Measure.pi (fun _ : Fin m => PY) := by
  classical
  haveI hfam : ∀ i : Fin (m + n), IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (inferInstance : IsProbabilityMeasure PY)
    · simpa only [Fin.addCases_right] using (inferInstance : IsProbabilityMeasure PZ)
  have hmeas : Measurable (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine (Measure.pi_eq (μ := fun _ : Fin m => PY) (fun s hs => ?_)).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : Fin (m + n) → ℝ => fun i : Fin m => x (Fin.castAdd n i)) ⁻¹'
      (Set.univ.pi s)
      = Set.univ.pi (Fin.addCases (motive := fun _ => Set ℝ) s (fun _ => Set.univ)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h l
      refine Fin.addCases (m := m) (n := n)
        (motive := fun l => x l ∈ Fin.addCases (motive := fun _ => Set ℝ) s
          (fun _ => Set.univ) l) (fun i => ?_) (fun j => ?_) l
      · simpa only [Fin.addCases_left] using h i
      · simp only [Fin.addCases_right]; exact Set.mem_univ _
    · intro h i
      simpa only [Fin.addCases_left] using h (Fin.castAdd n i)
  rw [hpre, twoSampleLaw, Measure.pi_pi, Fin.prod_univ_add]
  simp

/-- The `Z`-block twin of `map_projY`. -/
private lemma map_projZ (m n : ℕ) (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] :
    (twoSampleLaw m n PY PZ).map
        (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j))
      = Measure.pi (fun _ : Fin n => PZ) := by
  classical
  haveI hfam : ∀ i : Fin (m + n), IsProbabilityMeasure
      (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i) := by
    intro i
    refine Fin.addCases (m := m) (n := n)
      (motive := fun i => IsProbabilityMeasure
        (Fin.addCases (motive := fun _ => Measure ℝ) (fun _ => PY) (fun _ => PZ) i))
      (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (inferInstance : IsProbabilityMeasure PY)
    · simpa only [Fin.addCases_right] using (inferInstance : IsProbabilityMeasure PZ)
  have hmeas : Measurable (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine (Measure.pi_eq (μ := fun _ : Fin n => PZ) (fun s hs => ?_)).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : Fin (m + n) → ℝ => fun j : Fin n => x (Fin.natAdd m j)) ⁻¹'
      (Set.univ.pi s)
      = Set.univ.pi (Fin.addCases (motive := fun _ => Set ℝ) (fun _ => Set.univ) s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h l
      refine Fin.addCases (m := m) (n := n)
        (motive := fun l => x l ∈ Fin.addCases (motive := fun _ => Set ℝ)
          (fun _ => Set.univ) s l) (fun i => ?_) (fun j => ?_) l
      · simp only [Fin.addCases_left]; exact Set.mem_univ _
      · simpa only [Fin.addCases_right] using h j
    · intro h j
      simpa only [Fin.addCases_right] using h (Fin.natAdd m j)
  rw [hpre, twoSampleLaw, Measure.pi_pi, Fin.prod_univ_add]
  simp

/-- **The `L¹` law of large numbers on the `Y` block.** The block coordinates are i.i.d.
`P_Y`, so the generic product-measure law of large numbers transports along the projection. -/
private lemma tendsto_lln_blockY (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hf : Integrable f PY) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | ε ≤ |((m k : ℝ))⁻¹ *
          (∑ i : Fin (m k), f (x (Fin.castAdd (n k) i))) - ∫ t, f t ∂PY|})
      atTop (𝓝 0) := by
  have hbase := (tendsto_pi_real_lln (P := PY) f hf hε).comp hm
  refine hbase.congr fun k => ?_
  have hmeas : Measurable
      (fun x : Fin (m k + n k) → ℝ => fun i : Fin (m k) => x (Fin.castAdd (n k) i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hms : MeasurableSet {y : Fin (m k) → ℝ |
      ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (y i)) - ∫ t, f t ∂PY|} := by
    refine measurableSet_le measurable_const ((Measurable.sub ?_ measurable_const).abs)
    exact (Finset.measurable_sum _ fun i _ => hfm.comp (measurable_pi_apply i)).const_mul _
  have hval : (Measure.pi fun _ : Fin (m k) => PY) {y : Fin (m k) → ℝ |
        ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (y i)) - ∫ t, f t ∂PY|}
      = twoSampleLaw (m k) (n k) PY PZ {x : Fin (m k + n k) → ℝ |
        ε ≤ |((m k : ℝ))⁻¹ * (∑ i : Fin (m k), f (x (Fin.castAdd (n k) i)))
          - ∫ t, f t ∂PY|} := by
    rw [← map_projY (m k) (n k) PY PZ, Measure.map_apply hmeas hms]
    rfl
  simp only [Measure.real, Function.comp_apply, hval]

/-- **The `L¹` law of large numbers on the `Z` block.** -/
private lemma tendsto_lln_blockZ (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (f : ℝ → ℝ) (hfm : Measurable f) (hf : Integrable f PZ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | ε ≤ |((n k : ℝ))⁻¹ *
          (∑ j : Fin (n k), f (x (Fin.natAdd (m k) j))) - ∫ t, f t ∂PZ|})
      atTop (𝓝 0) := by
  have hbase := (tendsto_pi_real_lln (P := PZ) f hf hε).comp hn
  refine hbase.congr fun k => ?_
  have hmeas : Measurable
      (fun x : Fin (m k + n k) → ℝ => fun j : Fin (n k) => x (Fin.natAdd (m k) j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hms : MeasurableSet {y : Fin (n k) → ℝ |
      ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (y j)) - ∫ t, f t ∂PZ|} := by
    refine measurableSet_le measurable_const ((Measurable.sub ?_ measurable_const).abs)
    exact (Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)).const_mul _
  have hval : (Measure.pi fun _ : Fin (n k) => PZ) {y : Fin (n k) → ℝ |
        ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (y j)) - ∫ t, f t ∂PZ|}
      = twoSampleLaw (m k) (n k) PY PZ {x : Fin (m k + n k) → ℝ |
        ε ≤ |((n k : ℝ))⁻¹ * (∑ j : Fin (n k), f (x (Fin.natAdd (m k) j)))
          - ∫ t, f t ∂PZ|} := by
    rw [← map_projZ (m k) (n k) PY PZ, Measure.map_apply hmeas hms]
    rfl
  simp only [Measure.real, Function.comp_apply, hval]

/-! ### Consistency of the studentizing scale -/

/-- The `Y`-block sample variance as (second moment) − (first moment)², the form in which the
law of large numbers reaches it. -/
private lemma twoSampleVarY_eq {m n : ℕ} (hm : 0 < m) (x : Fin (m + n) → ℝ) :
    twoSampleVarY m n x
      = (m : ℝ)⁻¹ * (∑ i : Fin m, (x (Fin.castAdd n i)) ^ 2)
        + -(twoSampleMeanY m n x ^ 2) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : ∑ i : Fin m, x (Fin.castAdd n i) = (m : ℝ) * twoSampleMeanY m n x := by
    rw [twoSampleMeanY, ← mul_assoc, mul_inv_cancel₀ hmR.ne', one_mul]
  have hexp : ∀ i : Fin m, (x (Fin.castAdd n i) - twoSampleMeanY m n x) ^ 2
      = (x (Fin.castAdd n i)) ^ 2
        - 2 * twoSampleMeanY m n x * x (Fin.castAdd n i)
        + twoSampleMeanY m n x ^ 2 := fun i => by ring
  rw [twoSampleVarY]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- The `Z`-block twin of `twoSampleVarY_eq`. -/
private lemma twoSampleVarZ_eq {m n : ℕ} (hn : 0 < n) (x : Fin (m + n) → ℝ) :
    twoSampleVarZ m n x
      = (n : ℝ)⁻¹ * (∑ j : Fin n, (x (Fin.natAdd m j)) ^ 2)
        + -(twoSampleMeanZ m n x ^ 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ j : Fin n, x (Fin.natAdd m j) = (n : ℝ) * twoSampleMeanZ m n x := by
    rw [twoSampleMeanZ, ← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul]
  have hexp : ∀ j : Fin n, (x (Fin.natAdd m j) - twoSampleMeanZ m n x) ^ 2
      = (x (Fin.natAdd m j)) ^ 2
        - 2 * twoSampleMeanZ m n x * x (Fin.natAdd m j)
        + twoSampleMeanZ m n x ^ 2 := fun j => by ring
  rw [twoSampleVarZ]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- The population variance as (second moment) − (mean)². -/
private lemma var_eq_second_sub_sq {Q : Measure ℝ} [IsProbabilityMeasure Q] {μ v : ℝ}
    (hQ2 : MemLp id 2 Q) (hmeanQ : ∫ t, t ∂Q = μ) (hvarQ : ∫ t, (t - μ) ^ 2 ∂Q = v) :
    (∫ t, t ^ 2 ∂Q) + -(μ ^ 2) = v := by
  have hid : Integrable (fun t : ℝ => t) Q := by simpa using hQ2.integrable (by norm_num)
  have hsq : Integrable (fun t : ℝ => t ^ 2) Q := by simpa using hQ2.integrable_sq
  have hlin : Integrable (fun t : ℝ => 2 * μ * t) Q := hid.const_mul _
  have h1 : Integrable (fun t : ℝ => t ^ 2 - 2 * μ * t) Q := hsq.sub hlin
  have hfun : (fun t : ℝ => (t - μ) ^ 2) = fun t => (t ^ 2 - 2 * μ * t) + μ ^ 2 := by
    funext t; ring
  rw [← hvarQ, hfun, integral_add h1 (integrable_const _), integral_sub hsq hlin,
    integral_const_mul, hmeanQ]
  simp
  ring

/-- **The studentizing scale is consistent for `s`.** Both sample variances converge in
probability to the corresponding population variances, and the sample-size ratio converges by
hypothesis; the scale is a continuous function of the three. -/
private lemma tendstoInProb_twoSampleScale (PY PZ : Measure ℝ) [IsProbabilityMeasure PY]
    [IsProbabilityMeasure PZ] (m n : ℕ → ℕ) {lam varY varZ μ s : ℝ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hratio : Tendsto (fun k => (m k : ℝ) / n k) atTop (𝓝 lam))
    (hYL2 : MemLp id 2 PY) (hZL2 : MemLp id 2 PZ)
    (hmeanY : ∫ t, t ∂PY = μ) (hmeanZ : ∫ t, t ∂PZ = μ)
    (hvarY : ∫ t, (t - μ) ^ 2 ∂PY = varY) (hvarZ : ∫ t, (t - μ) ^ 2 ∂PZ = varZ)
    (hs : s ^ 2 = varY + lam * varZ) (hsnn : 0 ≤ s) :
    ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleScale (m k) (n k) x - s|}) atTop (𝓝 0) := by
  classical
  have hidY : Integrable (fun t : ℝ => t) PY := by simpa using hYL2.integrable (by norm_num)
  have hidZ : Integrable (fun t : ℝ => t) PZ := by simpa using hZL2.integrable (by norm_num)
  have hsqY : Integrable (fun t : ℝ => t ^ 2) PY := by simpa using hYL2.integrable_sq
  have hsqZ : Integrable (fun t : ℝ => t ^ 2) PZ := by simpa using hZL2.integrable_sq
  -- The four block averages.
  have hMY : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleMeanY (m k) (n k) x - μ|}) atTop (𝓝 0) := by
    intro ε hε
    have h := tendsto_lln_blockY PY PZ m n hm (fun t : ℝ => t) measurable_id hidY hε
    rw [hmeanY] at h
    exact h
  have hMZ : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleMeanZ (m k) (n k) x - μ|}) atTop (𝓝 0) := by
    intro ε hε
    have h := tendsto_lln_blockZ PY PZ m n hn (fun t : ℝ => t) measurable_id hidZ hε
    rw [hmeanZ] at h
    exact h
  have hQY := fun ε hε => tendsto_lln_blockY PY PZ m n hm (fun t : ℝ => t ^ 2)
    (by fun_prop) hsqY (ε := ε) hε
  have hQZ := fun ε hε => tendsto_lln_blockZ PY PZ m n hn (fun t : ℝ => t ^ 2)
    (by fun_prop) hsqZ (ε := ε) hε
  -- The two sample variances.
  have hnegY := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => -(y ^ 2)) (by fun_prop) hMY
  have hnegZ := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => -(y ^ 2)) (by fun_prop) hMZ
  have haddY := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hQY hnegY
  have haddZ := tendstoInProb_add (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hQZ hnegZ
  have hvarYhat : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleVarY (m k) (n k) x - varY|}) atTop (𝓝 0) := by
    intro ε hε
    refine (haddY ε hε).congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with k hk
    rw [var_eq_second_sub_sq hYL2 hmeanY hvarY]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, twoSampleVarY_eq hk x]
  have hvarZhat : ∀ ε > (0 : ℝ), Tendsto (fun k => (twoSampleLaw (m k) (n k) PY PZ).real
      {x : Fin (m k + n k) → ℝ | ε ≤ |twoSampleVarZ (m k) (n k) x - varZ|}) atTop (𝓝 0) := by
    intro ε hε
    refine (haddZ ε hε).congr' ?_
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    rw [var_eq_second_sub_sq hZL2 hmeanZ hvarZ]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, twoSampleVarZ_eq hk x]
  -- Combine into the squared scale, then take the square root.
  have hratioZ := tendstoInProb_const_mul
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hratio hvarZhat
  have hsqScale := tendstoInProb_add
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ) hvarYhat hratioZ
  have hsqrt := tendstoInProb_comp
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := Real.sqrt) (Real.continuous_sqrt.continuousAt) hsqScale
  intro ε hε
  have hlim : Real.sqrt (varY + lam * varZ) = s := by
    rw [← hs, Real.sqrt_sq hsnn]
  refine (hsqrt ε hε).congr fun k => ?_
  simp only [hlim, twoSampleScale]

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
  -- TODO (deep, deferred): the studentized randomization limit. Since
  -- `studentizedTwoSample = (1/twoSampleScale)·twoSampleMeanDiff + 0`, the Slutsky transfer
  -- `randDist_affine_tendstoInProb` applies with `A = 1/scale → 1/τ`, `B = 0`, and joint law
  -- from `weakConverges_randPairLaw_twoSample`; the limit c.d.f. is
  -- `cdf ((N(0,τ²)).map (·/τ)) = cdf (N(0,1))`.
  -- STATUS (re-derived this session, wave 4): two of the three pieces are settled, the third is
  -- re-scoped, and the statement is blocked on exactly one theorem.
  -- (ii) AVAILABLE, unchanged. `randDist_affine_tendstoInProb` in `SlutskyRandomization` is
  --      closed, in exactly the mixture form this application needs (`A = 1/twoSampleScale` is
  --      *not* permutation invariant). Its measurability side conditions are routine here: the
  --      numerator and the action are handled in `TwoSamplePermutation`, and measurability of
  --      the scale is the `hSmeas` computation used in the sibling theorem below.
  -- (iii) RE-SCOPED — and no longer the "shared missing brick" the wave-3 note described. That
  --      note asked for an `L¹` law of large numbers on `Measure.pi`; the brick now exists
  --      (`TwoSamplePermutation.tendsto_pi_real_lln`) and the *unconditional* scale consistency
  --      is proved (`tendstoInProb_twoSampleScale` above). What is still needed is the
  --      *randomized* scale consistency, a genuinely different statement — and worth recording,
  --      because it is precisely where studentization earns its keep. Under a uniform
  --      permutation of the pooled data each block is a sample **without replacement** from the
  --      pooled `N = m + n` values, so *both* block variances converge to the same pooled
  --      variance
  --          v̄ = (λ σ²(P_Y) + σ²(P_Z)) / (1 + λ) ,
  --      whence
  --          D_{m,n}(π·)² = S²_Y(π·) + (m/n) S²_Z(π·) → (1 + λ) v̄ = λ σ²(P_Y) + σ²(P_Z) = τ² .
  --      So the randomized scale converges to `τ`, whereas the unconditional one converges to
  --      `s² = σ²(P_Y) + λσ²(P_Z)` (that is `tendstoInProb_twoSampleScale`). The two limits
  --      differ exactly when `λ ≠ 1` and the variances differ — the failure of the unstudentized
  --      test — and dividing by the scale sends *both* to `N(0,1)`, which is the content of this
  --      file. The proof is Chebyshev on the group mixture: conditionally on the pooled data the
  --      first two moments of the subsample average are the hypergeometric ones supplied by
  --      `ForMathlib/HypergeometricMoments` (`var_mean_linear_le`, `cov_weight`), and the pooled
  --      empirical moments themselves converge by `tendsto_pi_real_lln`. No missing upstream
  --      brick: this is bounded, self-contained work.
  -- (i) THE BLOCKER, verdict unchanged after re-derivation.
  --      `weakConverges_randPairLaw_twoSample` — Hoeffding's combinatorial CLT, which neither
  --      this repository nor Mathlib v4.29.1 contains, and which the sign-change engine
  --      provably does not cover; see the re-derived note there. Since (iii) is of no use until
  --      (i) lands, it has deliberately been left unwritten.
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
  classical
  -- The unconditional variance, and the numerator's limit.
  have hposs : 0 < varY + lam * varZ := by positivity
  set s : ℝ := Real.sqrt (varY + lam * varZ) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 hposs
  have hs : s ^ 2 = varY + lam * varZ := Real.sq_sqrt hposs.le
  have hTlaw := weakConverges_twoSampleMeanDiff PY PZ m n hm hn hratio hlam hYL2 hZL2
    hmeanY hmeanZ hvarY hvarZ hvarYpos hvarZpos hspos hs
  have hTmeas : ∀ k, Measurable (twoSampleMeanDiff (m k) (n k)) := by
    intro k; unfold twoSampleMeanDiff; fun_prop
  have hSmeas : ∀ k, Measurable (studentizedTwoSample (m k) (n k)) := by
    intro k
    unfold studentizedTwoSample twoSampleScale twoSampleVarY twoSampleVarZ
      twoSampleMeanY twoSampleMeanZ twoSampleMeanDiff
    fun_prop
  haveI hprobT : ∀ k, IsProbabilityMeasure
      ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))) := fun k =>
    Measure.isProbabilityMeasure_map (hTmeas k).aemeasurable
  -- Dividing the numerator's Gaussian limit by `s` gives the standard normal.
  have hgauss : (gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩).map (fun y : ℝ => y / s)
      = gaussianReal 0 1 := by
    have hfun : (fun y : ℝ => y / s) = fun y : ℝ => y * s⁻¹ := by
      funext y; rw [div_eq_mul_inv]
    rw [hfun, gaussianReal_map_mul_const]
    congr 1
    · ring
    · refine NNReal.coe_injective ?_
      simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_mk]
      field_simp
  have hXlaw : WeakConverges
      (fun k => (twoSampleLaw (m k) (n k) PY PZ).map
        (fun x => twoSampleMeanDiff (m k) (n k) x / s)) (gaussianReal 0 1) := by
    have hmapped := hTlaw.map (f := fun y : ℝ => y / s) (by fun_prop) (by fun_prop)
    rw [hgauss] at hmapped
    have heq : ∀ k, ((twoSampleLaw (m k) (n k) PY PZ).map
          (twoSampleMeanDiff (m k) (n k))).map (fun y : ℝ => y / s)
        = (twoSampleLaw (m k) (n k) PY PZ).map
          (fun x => twoSampleMeanDiff (m k) (n k) x / s) := fun k =>
      Measure.map_map (by fun_prop) (hTmeas k)
    simpa only [heq] using hmapped
  -- The scale is consistent, hence so is its reciprocal.
  have hscale := tendstoInProb_twoSampleScale PY PZ m n hm hn hratio hYL2 hZL2 hmeanY hmeanZ
    hvarY hvarZ hs hspos.le
  have hinv := tendstoInProb_comp (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (φ := fun y : ℝ => y⁻¹) (continuousAt_inv₀ hspos.ne') hscale
  -- Slutsky: the studentized statistic differs from `T/s` by a vanishing remainder.
  refine AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
    (P := fun k => twoSampleLaw (m k) (n k) PY PZ)
    (X := fun k x => twoSampleMeanDiff (m k) (n k) x / s)
    (Y := fun k => studentizedTwoSample (m k) (n k))
    (fun k => ((hTmeas k).div_const s).aemeasurable)
    (fun k => (hSmeas k).aemeasurable) hXlaw ?_
  intro δ hδ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hMpos, hMev⟩ :=
    exists_tight_bound_of_weakConverges hTlaw (show (0 : ℝ) < ε / 2 by positivity)
  have hinvev := (hinv (δ / M) (by positivity)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hMev, hinvev] with k hk0 hk1
  have hmeasM : MeasurableSet {y : ℝ | M ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hTval : ((twoSampleLaw (m k) (n k) PY PZ).map (twoSampleMeanDiff (m k) (n k))).real
        {y : ℝ | M ≤ |y|}
      = (twoSampleLaw (m k) (n k) PY PZ).real
        {x : Fin (m k + n k) → ℝ | M ≤ |twoSampleMeanDiff (m k) (n k) x|} := by
    rw [Measure.real, Measure.map_apply (hTmeas k) hmeasM]
    rfl
  rw [hTval] at hk0
  have hincl : {x : Fin (m k + n k) → ℝ |
        δ ≤ dist (twoSampleMeanDiff (m k) (n k) x / s) (studentizedTwoSample (m k) (n k) x)}
      ⊆ {x : Fin (m k + n k) → ℝ | M ≤ |twoSampleMeanDiff (m k) (n k) x|}
        ∪ {x : Fin (m k + n k) → ℝ |
            δ / M ≤ |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹|} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Real.dist_eq] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have heq : twoSampleMeanDiff (m k) (n k) x / s - studentizedTwoSample (m k) (n k) x
        = twoSampleMeanDiff (m k) (n k) x * ((twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹) * (-1) := by
      unfold studentizedTwoSample
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [heq, abs_mul, abs_mul] at hx
    have hlt : |twoSampleMeanDiff (m k) (n k) x|
        * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹| < δ := by
      calc |twoSampleMeanDiff (m k) (n k) x| * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹|
          ≤ M * |(twoSampleScale (m k) (n k) x)⁻¹ - s⁻¹| :=
            mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
        _ < M * (δ / M) := mul_lt_mul_of_pos_left h2 hMpos
        _ = δ := by field_simp
    simp only [abs_neg, abs_one, mul_one] at hx
    linarith
  have hbound := (measureReal_mono (μ := twoSampleLaw (m k) (n k) PY PZ) hincl
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  linarith

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
  -- TODO (deep, deferred): pointwise consistency in level. Assembles the two limits above —
  -- the studentized randomization distribution `→P Φ` (`randDist_studentized_tendstoInProb`)
  -- and the unconditional law `⇝ N(0,1)` (`weakConverges_studentizedTwoSample`) — through the
  -- randomized critical value `randQuantile → z_{1-α}` (`randQuantile_tendstoInProb`) and a
  -- portmanteau evaluation of `powerAgainst` at the limiting rejection region, whose frontier
  -- is `N(0,1)`-null.
  -- STATUS (re-derived this session, wave 4): ONE prerequisite instead of two. The unconditional
  -- half `weakConverges_studentizedTwoSample` is now CLOSED (0-sorry, axiom-clean), so the only
  -- missing input is `randDist_studentized_tendstoInProb` above — which is in turn blocked on
  -- the single permutation CLT, `TwoSamplePermutation.weakConverges_randPairLaw_twoSample`.
  -- Everything downstream of the two limits remains in place: `Randomization/Asymptotics`
  -- supplies both halves of the equivalence (`randDist_tendstoInProb_cdf`,
  -- `randQuantile_tendstoInProb`, and the converse
  -- `weakConverges_randPairLaw_of_randDist_tendstoInProb`), so the only thing left to write once
  -- the prerequisite lands is the portmanteau evaluation of `powerAgainst` at the limiting
  -- rejection region.
  sorry

end StatLean.HypothesisTesting
