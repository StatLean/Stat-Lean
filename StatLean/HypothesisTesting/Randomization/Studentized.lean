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
  -- STATUS (re-derived this session): TWO of the three pieces are available; the assembly is
  -- blocked on the remaining two, in this order of difficulty.
  -- (ii) AVAILABLE. `randDist_affine_tendstoInProb` in `SlutskyRandomization` is CLOSED (0-sorry),
  --      in exactly the mixture form this application needs (`A = 1/twoSampleScale` is *not*
  --      permutation invariant). Its tightness brick is
  --      `Randomization/PairCLT.exists_tight_bound_of_weakConverges`. It carries measurability of
  --      `T`, `A`, `B` and of the action — all four are routine here
  --      (`measurable_twoSampleMeanDiff`, `measurable_perm_smul`, and `twoSampleScale` is a
  --      composition of `Real.sqrt` with a polynomial in the coordinates).
  -- Still open, and these are the only two:
  -- (i) `weakConverges_randPairLaw_twoSample` — the permutation (combinatorial) CLT, still open;
  --     see the status note there. This is the hard blocker: it is Hoeffding's combinatorial CLT,
  --     which the repository does not contain, and which the sign-change engine provably does not
  --     cover (the permutation weights do not factorize across coordinates).
  -- (iii) the scale consistency `twoSampleScale (π X) → τ` in `TendstoInProbRandomized`, a
  --      first-two-moments statement about sampling without replacement from the pooled data.
  --      `ForMathlib/HypergeometricMoments` supplies the moments of the sampling indicators
  --      (`var_mean_linear_le`, `cov_weight`), so this is a Chebyshev argument on the mixture, but
  --      it also needs the *unconditional* sample-variance consistency of (ii) in the sibling
  --      theorem below, i.e. an `L¹` weak law of large numbers on `Measure.pi`: the summands
  --      `(Yᵢ − μ)²` are only `L¹` under `MemLp id 2`, so Chebyshev is unavailable and the honest
  --      route is Kolmogorov's strong law on `Measure.infinitePi` pulled back along
  --      `AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate`
  --      (`AsymptoticStatistics/ForMathlib/IIdJointLaw`, public). That brick is shared with
  --      `Randomization/MultivariateQuadratic` — see the status note there.
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
  -- TODO (deep, deferred): unconditional law of the studentized statistic. Numerator
  -- `twoSampleMeanDiff ⇝ N(0, s²)` and denominator `twoSampleScale → s` in probability (the
  -- unconditional variance is exactly `s²` here), so the ratio `⇝ N(0,1)` by Slutsky at the level
  -- of laws.
  -- STATUS (re-derived this session): the numerator is NO LONGER a blocker —
  -- `TwoSamplePermutation.weakConverges_twoSampleMeanDiff` is now CLOSED (0-sorry, axiom-clean).
  -- Exactly two things remain:
  --  (a) the unconditional scale consistency `twoSampleScale → s` in probability. Expanding
  --      `S²_Y = m⁻¹∑(Yᵢ − Ȳ)² = m⁻¹∑Yᵢ² − Ȳ²`, this is a weak law of large numbers for `Yᵢ²`
  --      under `twoSampleLaw`, i.e. under a `Measure.pi`. The summands are only `L¹` (the
  --      hypothesis is `MemLp id 2`, so `Y²` has one moment, not two), hence Chebyshev does not
  --      apply; the honest route is Kolmogorov's strong law on `Measure.infinitePi` pulled back
  --      along `AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate`
  --      (`AsymptoticStatistics/ForMathlib/IIdJointLaw`, public), replicating the *private*
  --      `Asymptotics/Discharge/OneStep.iid_lln_in_prob_l1`. This is the same missing brick as in
  --      `Randomization/MultivariateQuadratic`, and it is the single highest-value thing to write
  --      next in this area.
  --  (b) a measure-level Slutsky-ratio lemma: if `Pₖ.map Tₖ ⇝ ν` and `Dₖ → s > 0` in
  --      `Pₖ`-probability, then `Pₖ.map (Tₖ/Dₖ) ⇝ ν.map (·/s)`. The `WeakConverges` API offers
  --      `.map` for a *fixed* continuous map only, and the underlying spaces `𝓧ₖ` vary with `k`,
  --      so Mathlib's fixed-space Slutsky lemmas do not apply either. The proof is the
  --      characteristic-function argument already used in `PairCLT` for the randomized version
  --      (`weakConverges_randPairLaw_of_tendstoInProb_avg`), specialised to a single (rather than
  --      group-averaged) law — i.e. the same `‖e^{iα} − e^{iβ}‖ ≤ min 2 (2|α−β|)` estimate.
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
  -- TODO (deep, deferred): pointwise consistency in level. Assembles the two limits above —
  -- the studentized randomization distribution `→P Φ` (`randDist_studentized_tendstoInProb`)
  -- and the unconditional law `⇝ N(0,1)` (`weakConverges_studentizedTwoSample`) — through the
  -- randomized critical value `randQuantile → z_{1-α}` (`randQuantile_tendstoInProb`) and a
  -- portmanteau evaluation of `powerAgainst` at the limiting rejection region, whose frontier
  -- is `N(0,1)`-null.
  -- STATUS (re-derived this session): still blocked on both prerequisite theorems above (both
  -- `sorry`), and nothing here is closer than they are. On the positive side, everything *after*
  -- them is in place: `Randomization/Asymptotics` supplies both halves of the equivalence
  -- (`randDist_tendstoInProb_cdf`, `randQuantile_tendstoInProb`, and the converse
  -- `weakConverges_randPairLaw_of_randDist_tendstoInProb`), so the only thing left to write once
  -- the two prerequisites land is the portmanteau evaluation of `powerAgainst` at the limiting
  -- rejection region, whose frontier is `N(0,1)`-null.
  sorry

end StatLean.HypothesisTesting
