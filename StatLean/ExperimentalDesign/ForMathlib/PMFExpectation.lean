import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Expectation, variance and covariance of a real statistic under a finite PMF

Design-based inference (randomization theory of experiments, design-based survey
sampling) computes moments of real statistics under a *finite* randomization
distribution: a `PMF Ω` with `Ω` a `Fintype`.  This file provides the elementary
sum-based moment calculus for that setting:
$$\mathbb E_D[f] = \sum_{\omega} D(\omega)\, f(\omega), \qquad
  \operatorname{Var}_D(f) = \mathbb E_D[(f - \mathbb E_D f)^2], \qquad
  \operatorname{Cov}_D(f,g) = \mathbb E_D[(f - \mathbb E_D f)(g - \mathbb E_D g)],$$
together with linearity, monotonicity, the pushforward identity
$\mathbb E_{g_* D}[f] = \mathbb E_D[f \circ g]$, the uniform-law counting formulas, and
the bilinear expansion $\operatorname{Var}(\sum_i f_i) = \sum_{i,j}\operatorname{Cov}(f_i,f_j)$.

Everything is a finite sum in `ℝ`; no integration theory enters.  This keeps every
downstream design computation (assignment probabilities, Horvitz–Thompson moments,
ANOVA expectations) inside elementary algebra, mirroring the treatment of
randomization moments in `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments`
(which works with a bespoke uniform average; the present file is the general-`PMF`
version needed once non-uniform designs appear).

## Main results

* `pmfExpect`, `pmfVar`, `pmfCov` — the finite moment functionals.
* `sum_pmf_toReal`, `pmfExpect_const`, `pmfExpect_add`, `pmfExpect_smul`,
  `pmfExpect_sum`, `pmfExpect_nonneg`, `pmfExpect_mono` — expectation calculus.
* `pmfExpect_map` — expectation under a pushforward design.
* `pmfExpect_uniformOfFinset`, `pmfExpect_uniformOfFintype` — counting formulas.
* `pmfVar_eq_expect_sq_sub_sq`, `pmfCov_eq_expect_mul_sub_mul` — computational forms.
* `pmfVar_sum` — variance of a sum as a double sum of covariances.
* `pmfVar_smul`, `pmfVar_add_const`, `pmfCov_smul_smul` — scaling rules.

**Reference.** These are the standard first- and second-moment manipulations of the
finite randomization model; see R. Mead, *The Design of Experiments: Statistical
Principles for Practical Applications*, Cambridge University Press, 1988
(ISBN 0-521-24512-5), §9.4 (randomisation theory of the analysis of experimental
data), where they are used throughout.  (`Mead §9.4`.)

**Proof formalization notes.**
* `pmfExpect` is a plain `Finset.univ` sum with weights `(D ω).toReal`; the weights sum
  to `1` (`sum_pmf_toReal`) because a `PMF` has total mass one and every value is
  finite (`PMF.apply_ne_top`), so `ENNReal.toReal` is additive on it.
* No `Nonempty Ω` assumptions appear: `PMF Ω` itself forces `Ω` nonempty when needed,
  and statements are phrased to be true degenerately otherwise.
* `pmfVar`/`pmfCov` are defined in centered form; the computational
  (`E[f²] − (E f)²`) forms are derived, not taken as definitions, so that
  nonnegativity of the variance is immediate from `pmfExpect_nonneg`.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {Ω : Type*} [Fintype Ω]

/-- The **expectation** of a real statistic `f` under a probability mass function `D`
on a finite type: `∑ ω, D(ω) · f(ω)`, with the `ℝ≥0∞`-valued mass converted by
`toReal`.  This is the design expectation of design-based inference (`Mead §9.4`). -/
noncomputable def pmfExpect (D : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, (D ω).toReal * f ω

/-- The **variance** of a real statistic under a finite PMF, in centered form
`E[(f − E f)²]`.  Degenerate inputs need no side conditions: this is a finite sum of
nonnegative terms. -/
noncomputable def pmfVar (D : PMF Ω) (f : Ω → ℝ) : ℝ :=
  pmfExpect D fun ω => (f ω - pmfExpect D f) ^ 2

/-- The **covariance** of two real statistics under a finite PMF, in centered form
`E[(f − E f)(g − E g)]`. -/
noncomputable def pmfCov (D : PMF Ω) (f g : Ω → ℝ) : ℝ :=
  pmfExpect D fun ω => (f ω - pmfExpect D f) * (g ω - pmfExpect D g)

/-- The real-valued masses of a finite PMF sum to `1`. -/
theorem sum_pmf_toReal (D : PMF Ω) : ∑ ω, (D ω).toReal = 1 := by
  sorry

/-- Expectation of a constant statistic. -/
theorem pmfExpect_const (D : PMF Ω) (c : ℝ) :
    pmfExpect D (fun _ => c) = c := by
  sorry

/-- Additivity of the design expectation. -/
theorem pmfExpect_add (D : PMF Ω) (f g : Ω → ℝ) :
    pmfExpect D (fun ω => f ω + g ω) = pmfExpect D f + pmfExpect D g := by
  sorry

/-- Homogeneity of the design expectation. -/
theorem pmfExpect_smul (D : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    pmfExpect D (fun ω => c * f ω) = c * pmfExpect D f := by
  sorry

/-- Subtraction rule for the design expectation. -/
theorem pmfExpect_sub (D : PMF Ω) (f g : Ω → ℝ) :
    pmfExpect D (fun ω => f ω - g ω) = pmfExpect D f - pmfExpect D g := by
  sorry

/-- The design expectation commutes with finite sums of statistics. -/
theorem pmfExpect_sum (D : PMF Ω) {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    pmfExpect D (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, pmfExpect D (f i) := by
  sorry

/-- The design expectation of a pointwise-nonnegative statistic is nonnegative. -/
theorem pmfExpect_nonneg (D : PMF Ω) {f : Ω → ℝ}
    -- LEAN-ONLY: pointwise nonnegativity; positivity transport, no scope change
    (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ pmfExpect D f := by
  sorry

/-- Monotonicity of the design expectation. -/
theorem pmfExpect_mono (D : PMF Ω) {f g : Ω → ℝ}
    -- LEAN-ONLY: pointwise domination; monotonicity transport, no scope change
    (h : ∀ ω, f ω ≤ g ω) :
    pmfExpect D f ≤ pmfExpect D g := by
  sorry

/-- **Pushforward identity**: the expectation of `f` under the image design `D.map g`
is the expectation of `f ∘ g` under `D`.  This is the workhorse that transfers moment
computations along design reductions (e.g. from a randomization design to the induced
sampling design of one treatment arm). -/
theorem pmfExpect_map {Ω' : Type*} [Fintype Ω'] (D : PMF Ω) (g : Ω → Ω') (f : Ω' → ℝ) :
    pmfExpect (D.map g) f = pmfExpect D (fun ω => f (g ω)) := by
  sorry

/-- Counting formula for the expectation under the uniform law on a finite set of
outcomes: the average of `f` over the set. -/
theorem pmfExpect_uniformOfFinset (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℝ) :
    pmfExpect (PMF.uniformOfFinset s hs) f = (s.card : ℝ)⁻¹ * ∑ ω ∈ s, f ω := by
  sorry

/-- Counting formula for the expectation under the uniform law on a finite type. -/
theorem pmfExpect_uniformOfFintype [Nonempty Ω] (f : Ω → ℝ) :
    pmfExpect (PMF.uniformOfFintype Ω) f = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω := by
  sorry

/-- Computational form of the variance: `Var f = E[f²] − (E f)²`. -/
theorem pmfVar_eq_expect_sq_sub_sq (D : PMF Ω) (f : Ω → ℝ) :
    pmfVar D f = pmfExpect D (fun ω => f ω ^ 2) - (pmfExpect D f) ^ 2 := by
  sorry

/-- Computational form of the covariance: `Cov(f,g) = E[fg] − (E f)(E g)`. -/
theorem pmfCov_eq_expect_mul_sub_mul (D : PMF Ω) (f g : Ω → ℝ) :
    pmfCov D f g = pmfExpect D (fun ω => f ω * g ω) - pmfExpect D f * pmfExpect D g := by
  sorry

/-- The covariance of a statistic with itself is its variance. -/
theorem pmfCov_self (D : PMF Ω) (f : Ω → ℝ) : pmfCov D f f = pmfVar D f := by
  sorry

/-- Symmetry of the covariance. -/
theorem pmfCov_comm (D : PMF Ω) (f g : Ω → ℝ) : pmfCov D f g = pmfCov D g f := by
  sorry

/-- The design variance is nonnegative. -/
theorem pmfVar_nonneg (D : PMF Ω) (f : Ω → ℝ) : 0 ≤ pmfVar D f := by
  sorry

/-- The variance of a constant statistic vanishes. -/
theorem pmfVar_const (D : PMF Ω) (c : ℝ) : pmfVar D (fun _ => c) = 0 := by
  sorry

/-- Quadratic scaling of the variance. -/
theorem pmfVar_smul (D : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    pmfVar D (fun ω => c * f ω) = c ^ 2 * pmfVar D f := by
  sorry

/-- Translation invariance of the variance. -/
theorem pmfVar_add_const (D : PMF Ω) (f : Ω → ℝ) (c : ℝ) :
    pmfVar D (fun ω => f ω + c) = pmfVar D f := by
  sorry

/-- Bilinear scaling of the covariance. -/
theorem pmfCov_smul_smul (D : PMF Ω) (a b : ℝ) (f g : Ω → ℝ) :
    pmfCov D (fun ω => a * f ω) (fun ω => b * g ω) = a * b * pmfCov D f g := by
  sorry

/-- **Variance of a sum** as the double sum of covariances:
`Var(∑ i, fᵢ) = ∑ i, ∑ j, Cov(fᵢ, fⱼ)`.  The single identity behind every exact design
variance in the library (Horvitz–Thompson, arm means, stratified estimators). -/
theorem pmfVar_sum (D : PMF Ω) {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    pmfVar D (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, ∑ j ∈ s, pmfCov D (f i) (f j) := by
  sorry

end StatLean.ExperimentalDesign
