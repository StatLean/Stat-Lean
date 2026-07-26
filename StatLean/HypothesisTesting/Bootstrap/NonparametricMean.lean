import StatLean.HypothesisTesting.Bootstrap.Consistency
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.HasLaw
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CDF

/-!
# The nonparametric bootstrap for a mean

The archetypal application of the sequence-class criterion: the parameter is the mean of a law
on the line, the root is the centred and scaled sample mean, and the estimated law is the
empirical measure of the sample. The class of sequences that makes the criterion work is
explicit here — weak convergence together with convergence of means and of variances — and the
almost sure membership of the empirical sequence is exactly the Glivenko–Cantelli theorem plus
the strong law of large numbers.

This file contains:

* `meanSeqClass` — the sequence class `C_F` for the mean problem;
* `meanRootCDF`, `sampleVariance`, `studentizedRootCDF` — the sampling distribution functions
  of the centred and of the studentized sample mean;
* `mean_root_cdf_tendsto` — convergence of the sampling distribution along the class;
* `empirical_mem_meanSeqClass` — almost sure membership of the empirical sequence in the class;
* `bootstrap_mean_consistent`, `bootstrap_mean_coverage` — the headline consistency and
  coverage statements for the mean;
* `studentized_root_cdf_tendsto`, `bootstrap_t_consistent` — the studentized versions.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.3 (§18.3.2, The
Nonparametric Mean), Theorem 18.3.4 (the studentized bootstrap-`t`) and Lemma 18.3.1 (the
first-absolute-moment convergence tool). (`TSH4 §18.3 Thm 18.3.3, Thm 18.3.4, Lem 18.3.1`.)

**Proof formalization notes.**
* Convergence of the sampling distribution along the class is a Lindeberg central limit theorem
  for a triangular array whose `n`-th row is drawn from the `n`-th law of the sequence; the
  Lindeberg condition is verified from convergence of the second moments plus the continuous
  mapping theorem. The array central limit theorem itself is the sibling
  `ForMathlib/LindebergCLT` brick of this area.
* Almost sure membership of the empirical sequence uses the Glivenko–Cantelli theorem for the
  weak-convergence clause and `ProbabilityTheory.strong_law_ae` for the convergence of the
  empirical means and of the empirical second moments (hence of the empirical variances).
* The studentized statement adds one step: the sample variance converges in probability to the
  limiting variance along the class, which is the triangular-array weak law
  `tendstoInMeasure_rowMean_triangular` applied to the entries and to their squares.
* The class is stated with the `n = 0` entry unconstrained (`0 < n` guard on the
  probability-measure clause): the empirical measure of an empty sample is the zero measure,
  and every convergence in the class is a statement along `atTop`, so the degenerate entry is
  never seen.
* Division by a vanishing sample standard deviation returns `0` by the junk convention; this is
  reached only on the null event where the sample is constant, which the nondegeneracy
  hypothesis on the limiting variance makes asymptotically negligible.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Consistency of the bootstrap for a mean
under a finite nonzero variance, and its failure without one, is due to P. J. Bickel and
D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.* **9** (1981),
1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap," *Ann. Statist.* **9**
(1981), 1187–1195); the class-of-sequences packaging follows R. Beran ("Bootstrap methods in
statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30) and D. N. Politis,
J. P. Romano and M. Wolf, *Subsampling*, Springer, 1999. The superiority of the studentized
(bootstrap-t) root is analysed in P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer,
1992.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The mean-bootstrap sequence class and the roots -/

/-- The **sequence class for the mean problem**, `C_F`: sequences of laws on the line that are
square-integrable, converge weakly to `Q` (their distribution functions converge at every
continuity point of the limit distribution function), and whose means and variances converge to
the mean and variance of `Q`. The `n = 0` entry is left unconstrained; see the file's proof
formalization notes. -/
def meanSeqClass (Q : Measure ℝ) : Set (ℕ → Measure ℝ) :=
  {F | (∀ n : ℕ, 0 < n → IsProbabilityMeasure (F n)) ∧
    (∀ n : ℕ, MemLp (fun t : ℝ => t) 2 (F n)) ∧
    (∀ x : ℝ, ContinuousAt (fun t => (Q (Set.Iic t)).toReal) x →
      Tendsto (fun n => ((F n) (Set.Iic x)).toReal) atTop (𝓝 ((Q (Set.Iic x)).toReal))) ∧
    Tendsto (fun n => ∫ t, t ∂(F n)) atTop (𝓝 (∫ t, t ∂Q)) ∧
    Tendsto (fun n => Var[fun t : ℝ => t; F n]) atTop (𝓝 Var[fun t : ℝ => t; Q])}

/-- The **sampling distribution function of the centred and scaled sample mean** under `n`
independent draws from `F`: `x ↦ F^n{ n^{1/2}(X̄ₙ − E_F X) ≤ x }`. -/
noncomputable def meanRootCDF (F : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin n => F)
    {y : Fin n → ℝ | Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) ≤ x}).toReal

/-- The **sample variance** in the plug-in (divide-by-`n`) form: the variance of the empirical
measure of the sample. Returns `0` for an empty sample. -/
noncomputable def sampleVariance {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (y i - (n : ℝ)⁻¹ * (∑ j, y j)) ^ 2

/-- The **sampling distribution function of the studentized sample mean** under `n` independent
draws from `F`: `x ↦ F^n{ n^{1/2}(X̄ₙ − E_F X)/σ̂ₙ ≤ x }`, with `σ̂ₙ` the plug-in sample standard
deviation. A vanishing `σ̂ₙ` makes the quotient `0` by the junk convention. -/
noncomputable def studentizedRootCDF (F : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin n => F)
    {y : Fin n → ℝ |
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) /
        Real.sqrt (sampleVariance y) ≤ x}).toReal

/-! ## Distribution-function and continuity infrastructure -/

/-- The `toReal` of the `Iic`-measure of a probability law on the line is a distribution
function: this is exactly `ProbabilityTheory.cdf`, dressed as `IsCDF`. -/
private lemma isCDF_toReal_measure_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsCDF (fun x => (ν (Set.Iic x)).toReal) := by
  have heq : (fun x => (ν (Set.Iic x)).toReal) = fun x => (ProbabilityTheory.cdf ν) x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  rw [heq]
  exact
    { mono := (ProbabilityTheory.cdf ν).mono
      right_continuous := fun x => (ProbabilityTheory.cdf ν).right_continuous x
      tendsto_atBot := ProbabilityTheory.tendsto_cdf_atBot ν
      tendsto_atTop := ProbabilityTheory.tendsto_cdf_atTop ν }

/-- The distribution function of a probability law with no atoms is continuous. -/
private lemma continuous_toReal_measure_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NoAtoms ν] : Continuous (fun x => (ν (Set.Iic x)).toReal) := by
  have heq : (fun x => (ν (Set.Iic x)).toReal) = fun x => (ProbabilityTheory.cdf ν) x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  rw [heq]
  set f := ProbabilityTheory.cdf ν with hf
  refine continuous_iff_continuousAt.2 (fun x => ?_)
  have hleft : Function.leftLim f x = f x := by
    have hsing : f.measure {x} = 0 := by rw [ProbabilityTheory.measure_cdf]; exact measure_singleton x
    have hval := f.measure_singleton x
    rw [hsing] at hval
    have hle : Function.leftLim f x ≤ f x := f.mono.leftLim_le le_rfl
    have h0 : f x - Function.leftLim f x ≤ 0 := by
      by_contra h
      push_neg at h
      exact (ENNReal.ofReal_pos.mpr h).ne' hval.symm
    linarith
  have hright : Function.rightLim f x = f x := (f.right_continuous x).rightLim_eq
  exact (f.mono.continuousAt_iff_leftLim_eq_rightLim).2 (hleft.trans hright.symm)

/-- `normalCDF m v` is a distribution function. -/
private lemma isCDF_normalCDF (m : ℝ) (v : ℝ≥0) : IsCDF (normalCDF m v) :=
  isCDF_toReal_measure_Iic (gaussianReal m v)

/-- `stdNormalCDF` is a distribution function. -/
private lemma isCDF_stdNormalCDF : IsCDF stdNormalCDF := isCDF_normalCDF 0 1

/-- A nondegenerate normal distribution function is continuous. -/
private lemma continuous_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Continuous (normalCDF m v) :=
  haveI : NoAtoms (gaussianReal m v) := noAtoms_gaussianReal hv
  continuous_toReal_measure_Iic (gaussianReal m v)

/-- The standard normal distribution function is continuous. -/
private lemma continuous_stdNormalCDF : Continuous stdNormalCDF := continuous_normalCDF 0 one_ne_zero

/-- A nondegenerate normal distribution function is strictly increasing. -/
private lemma strictMono_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : StrictMono (normalCDF m v) := by
  intro y z hyz
  have hpos : 0 < gaussianReal m v (Set.Ioc y z) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hvol := (gaussianReal_absolutelyContinuous' m hv) h0
    rw [Real.volume_Ioc] at hvol
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hvol
  have hdisj : gaussianReal m v (Set.Iic z)
      = gaussianReal m v (Set.Iic y) + gaussianReal m v (Set.Ioc y z) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hyz.le]
  have hfin : gaussianReal m v (Set.Iic y) ≠ ⊤ := measure_ne_top _ _
  unfold normalCDF
  rw [hdisj, ENNReal.toReal_add hfin (measure_ne_top _ _)]
  have hp2 : 0 < (gaussianReal m v (Set.Ioc y z)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

/-- The `1 − α` quantile of a nondegenerate normal distribution function is a point of strict
increase. -/
private lemma strictIncAt_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x₀ : ℝ) :
    StrictIncAt (normalCDF m v) x₀ :=
  ⟨fun y hy => strictMono_normalCDF m hv hy, fun z hz => strictMono_normalCDF m hv hz⟩

/-- The empirical measure of a nonempty sample is a probability measure. -/
private lemma isProbabilityMeasure_empiricalMeasure {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]

/-- The sampling distribution function of the centred sample mean is a distribution function
(whenever the underlying `n`-fold product is a probability measure). -/
private lemma isCDF_meanRootCDF (F : Measure ℝ) (n : ℕ)
    [IsProbabilityMeasure (Measure.pi fun _ : Fin n => F)] :
    IsCDF (meanRootCDF F n) := by
  have hSmeas : Measurable (fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F)) := by fun_prop
  haveI : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F))) :=
    Measure.isProbabilityMeasure_map hSmeas.aemeasurable
  have heq : meanRootCDF F n = fun x =>
      (((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F)))
        (Set.Iic x)).toReal := by
    funext x
    rw [Measure.map_apply hSmeas measurableSet_Iic]
    rfl
  rw [heq]
  exact isCDF_toReal_measure_Iic _

/-- The sampling distribution function of the studentized sample mean is a distribution function
(whenever the underlying `n`-fold product is a probability measure). -/
private lemma isCDF_studentizedRootCDF (F : Measure ℝ) (n : ℕ)
    [IsProbabilityMeasure (Measure.pi fun _ : Fin n => F)] :
    IsCDF (studentizedRootCDF F n) := by
  have hSmeas : Measurable (fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y)) := by
    unfold sampleVariance; fun_prop
  haveI : IsProbabilityMeasure
      ((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ =>
          Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y))) :=
    Measure.isProbabilityMeasure_map hSmeas.aemeasurable
  have heq : studentizedRootCDF F n = fun x =>
      (((Measure.pi fun _ : Fin n => F).map
        (fun y : Fin n → ℝ =>
          Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - ∫ t, t ∂F) / Real.sqrt (sampleVariance y)))
        (Set.Iic x)).toReal := by
    funext x
    rw [Measure.map_apply hSmeas measurableSet_Iic]
    rfl
  rw [heq]
  exact isCDF_toReal_measure_Iic _

/-- The `n`-fold product of a probability law is a probability measure. -/
private lemma isProbabilityMeasure_pi_const (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (Measure.pi fun _ : Fin n => F) := by
  haveI : ∀ _ : Fin n, IsProbabilityMeasure F := fun _ => ‹_›
  infer_instance

/-- The `n`-fold product of the empirical measure of a sample is a probability measure (for the
empty sample it is the point mass on the empty tuple). -/
private lemma isProbabilityMeasure_pi_empirical (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => empiricalMeasure fun i : Fin n => X i ω) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Measure.pi_of_empty]
    infer_instance
  · haveI := isProbabilityMeasure_empiricalMeasure hn (fun i : Fin n => X i ω)
    exact isProbabilityMeasure_pi_const n _

/-- The constant sequence at a square-integrable probability law belongs to its own mean class. -/
private lemma const_mem_meanSeqClass (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) : (fun _ => Q) ∈ meanSeqClass Q :=
  ⟨fun _ _ => inferInstance, fun _ => hQ2, fun _ _ => tendsto_const_nhds,
    tendsto_const_nhds, tendsto_const_nhds⟩

/-! ## Convergence along the class, and membership of the empirical sequence -/

section MeanBootstrap

variable {Q : Measure ℝ} {F : ℕ → Measure ℝ} {Pr : Measure Ω} {X : ℕ → Ω → ℝ} {α : ℝ}

/-- **Convergence of the sampling distribution of the mean along the class.**

Along every sequence of the mean class, the sampling distribution function of the centred and
scaled sample mean converges to the normal distribution function with mean zero and the limiting
variance. -/
theorem mean_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable, so its mean and variance exist
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    -- USER-INPUT: the limiting variance is nonzero; the bootstrap for a mean is inconsistent
    -- without a finite nonzero variance
    (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: the sequence of laws belongs to the mean class
    (hF : F ∈ meanSeqClass Q) (x : ℝ) :
    Tendsto (fun n => meanRootCDF (F n) n x) atTop
      (𝓝 (normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) x)) := by
  sorry

/-- **The empirical sequence belongs to the mean class, almost surely.**

For an independent identically distributed sample from a square-integrable law, the sequence of
empirical measures satisfies the three defining convergences of the mean class with probability
one. -/
theorem empirical_mem_meanSeqClass [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are independent
    (hindep : iIndepFun X Pr)
    -- USER-INPUT: the observations are identically distributed with law `Q`
    (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: the sampling law is square-integrable, so means and variances converge
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) :
    ∀ᵐ ω ∂Pr, (fun n => empiricalMeasure fun i : Fin n => X i ω) ∈ meanSeqClass Q := by
  sorry

/-- **Consistency of the nonparametric bootstrap for a mean.**

The bootstrap sampling distribution — the sampling distribution of the root computed at the
empirical measure — is uniformly close to the true sampling distribution, almost surely. -/
theorem bootstrap_mean_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q]) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (meanRootCDF Q n)
      (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
  set Jlim := normalCDF 0 (Real.toNNReal Var[fun t : ℝ => t; Q]) with hJlim
  have hvne : Real.toNNReal Var[fun t : ℝ => t; Q] ≠ 0 := (Real.toNNReal_pos.mpr hQvar).ne'
  have hcont : Continuous Jlim := continuous_normalCDF 0 hvne
  have hcdflim : IsCDF Jlim := isCDF_normalCDF 0 _
  have hQcdf : ∀ n, IsCDF (meanRootCDF Q n) := fun n => by
    haveI := isProbabilityMeasure_pi_const n Q; exact isCDF_meanRootCDF Q n
  have hQconv : ∀ x, Tendsto (fun n => meanRootCDF Q n x) atTop (𝓝 (Jlim x)) := fun x =>
    mean_root_cdf_tendsto hQ2 hQvar (const_mem_meanSeqClass Q hQ2) x
  filter_upwards [empirical_mem_meanSeqClass hmeas hindep hlaw hident hQ2] with ω hω
  have hEcdf : ∀ n, IsCDF (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n) := fun n => by
    haveI := isProbabilityMeasure_pi_empirical n X ω; exact isCDF_meanRootCDF _ n
  have hEconv : ∀ x, Tendsto
      (fun n => meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n x) atTop (𝓝 (Jlim x)) :=
    fun x => mean_root_cdf_tendsto hQ2 hQvar hω x
  have hA : Tendsto (fun n => supCDFDist (meanRootCDF Q n) Jlim) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero hQcdf hcont hcdflim hQconv
  have hB : Tendsto (fun n =>
      supCDFDist Jlim (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero hEcdf hcont hcdflim hEconv
    simpa only [supCDFDist_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (meanRootCDF Q n) Jlim
      + supCDFDist Jlim (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hQcdf n) (hEcdf n)
  · exact supCDFDist_triangle_of_isCDF (hQcdf n) hcdflim (hEcdf n)

/-- **Asymptotic coverage of the bootstrap confidence bound for a mean.**

The one-sided bootstrap confidence set for the mean, obtained by comparing the root to the
`1 − α` quantile of the bootstrap sampling distribution, has asymptotic coverage `1 − α`. -/
theorem bootstrap_mean_coverage [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => (Pr {ω |
        Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)
          ≤ cdfPseudoInverse (meanRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)
              (1 - α)}).toReal)
      atTop (𝓝 (1 - α)) := by
  sorry

/-! ## The studentized root and the bootstrap-t -/

/-- **Convergence of the studentized sampling distribution along the class.**

Along every sequence of the mean class the sampling distribution function of the studentized
sample mean converges to the standard normal distribution function — the studentized root is an
asymptotic pivot. -/
theorem studentized_root_cdf_tendsto [IsProbabilityMeasure Q]
    -- USER-INPUT: the limit law is square-integrable
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q)
    -- USER-INPUT: the limiting variance is nonzero
    (hQvar : 0 < Var[fun t : ℝ => t; Q])
    -- USER-INPUT: the sequence of laws belongs to the mean class
    (hF : F ∈ meanSeqClass Q) (x : ℝ) :
    Tendsto (fun n => studentizedRootCDF (F n) n x) atTop (𝓝 (stdNormalCDF x)) := by
  sorry

/-- **Consistency of the bootstrap-t.**

The bootstrap sampling distribution of the studentized root, computed at the empirical measure,
is uniformly close to the true one, almost surely. -/
theorem bootstrap_t_consistent [IsProbabilityMeasure Pr] [IsProbabilityMeasure Q]
    -- LEAN-ONLY: the observations are measurable
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent identically distributed observations with law `Q`
    (hindep : iIndepFun X Pr) (hlaw : HasLaw (X 0) Q Pr)
    -- USER-INPUT: the observations are identically distributed
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr)
    -- USER-INPUT: square-integrable sampling law with nonzero variance
    (hQ2 : MemLp (fun t : ℝ => t) 2 Q) (hQvar : 0 < Var[fun t : ℝ => t; Q]) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (studentizedRootCDF Q n)
      (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n)) atTop (𝓝 0) := by
  have hcont : Continuous stdNormalCDF := continuous_stdNormalCDF
  have hcdflim : IsCDF stdNormalCDF := isCDF_stdNormalCDF
  have hQcdf : ∀ n, IsCDF (studentizedRootCDF Q n) := fun n => by
    haveI := isProbabilityMeasure_pi_const n Q; exact isCDF_studentizedRootCDF Q n
  have hQconv : ∀ x, Tendsto (fun n => studentizedRootCDF Q n x) atTop (𝓝 (stdNormalCDF x)) :=
    fun x => studentized_root_cdf_tendsto hQ2 hQvar (const_mem_meanSeqClass Q hQ2) x
  filter_upwards [empirical_mem_meanSeqClass hmeas hindep hlaw hident hQ2] with ω hω
  have hEcdf : ∀ n, IsCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n) :=
    fun n => by haveI := isProbabilityMeasure_pi_empirical n X ω; exact isCDF_studentizedRootCDF _ n
  have hEconv : ∀ x, Tendsto
      (fun n => studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n x) atTop
      (𝓝 (stdNormalCDF x)) := fun x => studentized_root_cdf_tendsto hQ2 hQvar hω x
  have hA : Tendsto (fun n => supCDFDist (studentizedRootCDF Q n) stdNormalCDF) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero hQcdf hcont hcdflim hQconv
  have hB : Tendsto (fun n =>
      supCDFDist stdNormalCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
      atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero hEcdf hcont hcdflim hEconv
    simpa only [supCDFDist_comm] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (studentizedRootCDF Q n) stdNormalCDF
      + supCDFDist stdNormalCDF (studentizedRootCDF (empiricalMeasure fun i : Fin n => X i ω) n))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hQcdf n) (hEcdf n)
  · exact supCDFDist_triangle_of_isCDF (hQcdf n) hcdflim (hEcdf n)

end MeanBootstrap

end StatLean.HypothesisTesting
