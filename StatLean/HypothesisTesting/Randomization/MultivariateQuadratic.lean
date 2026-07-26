import StatLean.HypothesisTesting.Randomization.SignChange
import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Randomization tests for a multivariate mean: quadratic-form limits

Testing $\mu(P) = 0$ for i.i.d. random vectors in $\mathbb{R}^p$ is classically done with
Hotelling's $T^2$ statistic, whose exact critical values require multivariate normality. A
randomization test using the **sign-change group** — replacing $X_i$ by $-X_i$ for an
arbitrary subset of indices — is exact for *every* law with $X_i$ and $-X_i$ identically
distributed, and this file establishes that it is asymptotically level $\alpha$ far beyond
that class, under second moments alone.

All three results below use the **sign-change group**, not the permutation group: the
permutation group belongs to the two-sample problem, whereas the one-sample multivariate
mean is invariant under sign changes. Writing $\varepsilon, \varepsilon'$ for two
independent uniform sign patterns:

* the **vector** building block — $n^{-1/2}\bigl(\sum_i \varepsilon_i X_i,
  \sum_i \varepsilon_i' X_i\bigr) \xrightarrow{d} (Z_1, Z_2)$ with $Z_1, Z_2$ i.i.d.
  $N(0, \Sigma)$;
* the **modified** $T^2$ statistic $\tilde T_n = n \bar X_n^\top \tilde\Sigma_n^{-1}
  \bar X_n$, built from the uncentred second-moment matrix
  $\tilde\Sigma_n = n^{-1}\sum_i X_iX_i^\top$ — which is itself *invariant* under sign
  changes — has randomized pair converging to
  $(Z_1^\top\Sigma^{-1}Z_1, Z_2^\top\Sigma^{-1}Z_2)$, a product of two independent
  $\chi^2_p$ laws;
* Hotelling's $T^2$ statistic $T_n = n\bar X_n^\top \hat\Sigma_n^{-1}\bar X_n$, built from
  the centred sample covariance with divisor $n - 1$, has the same limit.

Since the unconditional limit of $T_n$ is also $\chi^2_p$, the randomization test based on
either statistic has rejection probability tending to the nominal level under any $P$ with
mean $0$ and finite second moments — and retains *exact* level whenever $X_i$ and $-X_i$
are identically distributed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.4 (Further Examples), Lemmas 17.4.1–17.4.3 (the quadratic-form
building block, joint convergence under two independent assignments, and the independent
chi-squared pair limit). (`TSH4 §17.4 Lem 17.4.1–17.4.3`.)

**Proof formalization notes.**
* *Group.* The acting group is `Fin n → ℤˣ` (i.e. `{±1}ⁿ`) acting componentwise on
  `Fin n → EuclideanSpace ℝ (Fin p)`, the same Mathlib-supplied action as in
  `Randomization/SignChange`, now with vector-valued coordinates.
* *Vector-valued randomized pairs.* `randPairLaw` is used at the target
  `EuclideanSpace ℝ (Fin p)` for the first result and at `ℝ` for the two quadratic-form
  results; that is the reason it is stated for a general measurable target.
* *Matrices and `EuclideanSpace`.* Data vectors live in `EuclideanSpace ℝ (Fin p)` (needed
  by `multivariateGaussian`), while sample covariance matrices are plain
  `Matrix (Fin p) (Fin p) ℝ`; the bridge is `.ofLp` together with `⬝ᵥ` and `Matrix.mulVec`,
  the convention already used elsewhere in the library. Matrix inversion is Mathlib's
  total `Matrix.inv`, which returns `0` on singular input — so all statistics here are
  total, with junk values exactly on the null set where the sample covariance degenerates.
* *Why the modified statistic is separated out.* $\tilde\Sigma_n$ is unchanged when any
  $X_i$ is replaced by $-X_i$, so recomputing $\tilde T_n$ over the group only moves
  $\bar X_n$; that is what makes its randomization analysis immediate from the vector
  building block plus the continuous mapping theorem. Hotelling's $\hat\Sigma_n$ is not
  invariant, and its treatment goes through the consistency
  $\hat\Sigma_n(\varepsilon_1X_1, \dots, \varepsilon_nX_n) \to \Sigma$ in probability,
  which is where mean-zero is used a second time.
* *Mean-zero and the second-moment variant.* The results are stated with $\mu(P) = 0$, as
  in the classical formulation, and `S` is then simultaneously the covariance and the
  second-moment matrix. The vector limit in fact holds verbatim without mean-zero provided
  `S` is read as the second-moment matrix $E[X_jX_k]$ — which is how the covariance
  hypothesis is phrased here, so that generalization needs no restatement.
* *Nondegeneracy.* Positive definiteness of `S` is genuine input: it is what makes
  `S⁻¹` meaningful and the quadratic form a $\chi^2_p$ rather than a degenerate law.
  `[NeZero p]` records that there is at least one degree of freedom.
* The identification of the limiting quadratic form with `chiSquared p` is isolated as
  `map_quadraticForm_multivariateGaussian_eq_chiSquared`, the one genuinely
  distributional step; the rest is the Cramér–Wold device plus the central limit theorem
  of the sibling brick `StatLean.HypothesisTesting.ForMathlib.LindebergCLT`, applied to the
  i.i.d. vectors `(εᵢXᵢ, ε'ᵢXᵢ)`, whose cross-covariance vanishes because
  `E[εᵢ]E[ε'ᵢ] = 0`.

**Bibliographic comments.** Sign-change randomization tests originate with R. A. Fisher
(*The Design of Experiments*, Oliver & Boyd, Edinburgh, 1935) and E. J. G. Pitman
("Significance tests which may be applied to samples from any populations," *J. R.
Statist. Soc. Suppl.* **4** (1937), 119–130); their exactness under a group hypothesis is
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45), and the sampled-group variant M. Dwass ("Modified
randomization tests for nonparametric hypotheses," *Ann. Math. Statist.* **28** (1957),
181–187). Large-sample theory for permutation and randomization statistics is
W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192); the asymptotic robustness of such tests
when the group hypothesis fails is J. P. Romano ("Bootstrap and randomization tests of some
nonparametric hypotheses," *Ann. Statist.* **17** (1989), 141–159; "On the behavior of
randomization tests without a group invariance assumption," *J. Amer. Statist. Assoc.*
**85** (1990), 686–692), with the studentization principle behind the modified statistic
due to A. Janssen ("Studentized permutation tests for non-i.i.d. hypotheses and the
generalized Behrens–Fisher problem," *Statist. Probab. Lett.* **36** (1997), 9–21) and the
general framework to E. Chung and J. P. Romano ("Exact and asymptotically robust
permutation tests," *Ann. Statist.* **41** (2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace Matrix

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {p : ℕ}

/-! ### Sample functionals -/

/-- Sample mean of a vector-valued sample. -/
noncomputable def sampleMeanVec {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- The **uncentred second-moment matrix** `Σ̃ₙ = n⁻¹ ∑ᵢ XᵢXᵢᵀ`. Unchanged when any `Xᵢ`
is replaced by `−Xᵢ`, hence invariant under the sign-change group. -/
noncomputable def modifiedCovMatrix {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => (n : ℝ)⁻¹ * ∑ i, (x i).ofLp j * (x i).ofLp k

/-- The **sample covariance matrix** `Σ̂ₙ = (n−1)⁻¹ ∑ᵢ (Xᵢ − X̄ₙ)(Xᵢ − X̄ₙ)ᵀ`. Not
invariant under sign changes. -/
noncomputable def sampleCovMatrix {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => ((n : ℝ) - 1)⁻¹ *
    ∑ i, ((x i).ofLp j - (sampleMeanVec x).ofLp j) *
      ((x i).ofLp k - (sampleMeanVec x).ofLp k)

/-- **Hotelling's `T²` statistic** `Tₙ = n X̄ₙᵀ Σ̂ₙ⁻¹ X̄ₙ`. Total: a singular sample
covariance gives Mathlib's junk inverse `0`, hence the value `0`. -/
noncomputable def hotellingTSq {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (n : ℝ) *
    ((sampleMeanVec x).ofLp ⬝ᵥ (sampleCovMatrix x)⁻¹.mulVec (sampleMeanVec x).ofLp)

/-- The **modified `T²` statistic** `T̃ₙ = n X̄ₙᵀ Σ̃ₙ⁻¹ X̄ₙ`, built from the uncentred
second-moment matrix (divisor `n` rather than `n − 1`). -/
noncomputable def modifiedTSq {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (n : ℝ) *
    ((sampleMeanVec x).ofLp ⬝ᵥ (modifiedCovMatrix x)⁻¹.mulVec (sampleMeanVec x).ofLp)

/-! ### The distributional bridge -/

/-- **The quadratic form of a nondegenerate centred Gaussian is chi-squared**:
if `Z ∼ N(0, S)` with `S` positive definite, then `ZᵀS⁻¹Z ∼ χ²_p`. -/
theorem map_quadraticForm_multivariateGaussian_eq_chiSquared [NeZero p]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance, so `S⁻¹` is a genuine inverse
    (hpd : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (fun z => z.ofLp ⬝ᵥ S⁻¹.mulVec z.ofLp) = chiSquared p := by
  -- The quadratic-form spelling `z.ofLp ⬝ᵥ S⁻¹ *ᵥ z.ofLp` is `Matrix.inner_toEuclideanCLM`
  -- of the inner-product spelling `⟪z, toEuclideanCLM S⁻¹ z⟫`, whose pushforward is the
  -- whitening bridge `multivariateGaussian_map_inner_inv_eq_chiSquared`.
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hfun : (fun z : EuclideanSpace ℝ (Fin p) => z.ofLp ⬝ᵥ S⁻¹.mulVec z.ofLp)
      = fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫ := by
    funext z
    exact (Matrix.inner_toEuclideanCLM S⁻¹ z z).symm
  rw [hfun]
  exact multivariateGaussian_map_inner_inv_eq_chiSquared hp hpd

/-! ### The vector building block -/

/-- **Sign-change randomization: the vector limit.** For i.i.d. vectors with mean `0` and
second-moment matrix `S`, the normalized sign-flipped sums at two independent uniform sign
patterns converge jointly in law to a pair of **independent, identically distributed**
centred Gaussians with covariance `S`:
$$ n^{-1/2}\Bigl(\sum_i \varepsilon_i X_i,\; \sum_i \varepsilon_i' X_i\Bigr)
   \;\xrightarrow{d}\; (Z_1, Z_2), \qquad Z_1, Z_2 \text{ i.i.d. } N(0, S). $$
Asymptotic independence comes from `E[εᵢ]E[ε'ᵢ] = 0`. -/
theorem weakConverges_randPairLaw_signChange_sum
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance, since the mean
    -- vanishes); stating it this way is what makes the result hold verbatim for a
    -- nonzero mean with `S` read as the second-moment matrix
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => P))
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S)) := by
  sorry

/-! ### Quadratic-form limits -/

/-- **Sign-change randomization for the modified `T²` statistic.** The randomized pair
converges in law to `(Z₁ᵀS⁻¹Z₁, Z₂ᵀS⁻¹Z₂)`, i.e. to a product of two **independent**
chi-squared laws with `p` degrees of freedom. The second-moment matrix used here is
invariant under sign changes, so only the sample mean moves along the group. -/
theorem weakConverges_randPairLaw_signChange_modifiedTSq [NeZero p]
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance here)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (modifiedTSq (p := p) (n := n))
        (Measure.pi fun _ : Fin n => P))
      ((chiSquared p).prod (chiSquared p)) := by
  sorry

/-- **Sign-change randomization for Hotelling's `T²` statistic.** Same limit as for the
modified statistic — a product of two independent `χ²_p` laws — obtained by showing that
the centred sample covariance recomputed at a random sign pattern is still consistent for
`S`. Since the unconditional limit of the statistic is also `χ²_p`, the randomization test
based on `Tₙ` has rejection probability tending to the nominal level under any law with
mean `0` and finite second moments, while remaining exact whenever `Xᵢ` and `−Xᵢ` are
identically distributed. -/
theorem weakConverges_randPairLaw_signChange_hotellingTSq [NeZero p]
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance here)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (hotellingTSq (p := p) (n := n))
        (Measure.pi fun _ : Fin n => P))
      ((chiSquared p).prod (chiSquared p)) := by
  sorry

end StatLean.HypothesisTesting
