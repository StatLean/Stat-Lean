import StatLean.HypothesisTesting.Bootstrap.Consistency
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.HasLaw
import Mathlib.Probability.StrongLaw

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

**Reference.** Classical nonparametric bootstrap theory for a mean; original sources in the
bibliographic comments below.

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
  sorry

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
    Tendsto (fun n => (Pr {ω |
        Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i : Fin n, X i ω) - ∫ t, t ∂Q)
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
  sorry

end MeanBootstrap

end StatLean.HypothesisTesting
