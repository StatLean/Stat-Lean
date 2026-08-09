import StatLean.CausalInference.Randomized.DifferenceInMeans

/-!
# Neyman's theorem — unbiasedness and the exact randomization variance

The first two parts of the flagship finite-population result. Under complete randomization
with `n₁` treated and `n₀` control units,

$$\mathbb E[\hat\tau]=\tau,\qquad
  \operatorname{Var}(\hat\tau)=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}{n},$$

where `S²(1)`, `S²(0)`, `S²(τ)` are the finite-population variances of the treated
potential outcomes, the control potential outcomes and the individual effects. The
variance-estimator half of Ding's Theorem 4.1 is in `Randomized.VarianceEstimator`.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 4.1(1)–(2) (§4.2, pp. 44–45) and its
supporting Lemma 4.1 (§4.1, p. 44: `2S(1,0) = S²(1) + S²(0) - S²(τ)`), under the
completely randomized experiment of Definition 3.1. (`Ding Theorem 4.1; Lemma 4.1`.) The
same repeated-sampling analysis is in G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015, ch. 6.
(`IR ch. 6`.)

**Proof formalization notes.** Both parts go through the linearization
`diffInMeans_eq_affine`: unbiasedness from `completeDesign_expect_ind` (`E[Zᵢ] = n₁/n`),
and the variance from `completeDesign_var_linear` (the sampling-without-replacement
variance of a linear statistic) followed by the algebraic identity of Lemma 4.1. The
constant `n₁n₀/(n(n-1))` multiplying `∑(cᵢ - c̄)²` with `cᵢ = Yᵢ(1)/n₁ + Yᵢ(0)/n₀`
rearranges into the three-term form; that rearrangement is where Lemma 4.1 enters.

**Bibliographic comments.** J. Neyman, "On the application of probability theory to
agricultural experiments. Essay on principles. Section 9" (1923), translated by
D. M. Dabrowska and T. P. Speed, *Statist. Sci.* **5** (1990), 465–472.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-- **Lemma 4.1** (Ding §4.1, p. 44): the finite-population variance identity
`2S(1,0) = S²(1) + S²(0) - S²(τ)` linking the covariance of the potential outcomes to the
variance of the individual effects. -/
theorem two_mul_popCov_eq (S : ScienceTable n) :
    2 * popCov S.y1 S.y0 = popVar S.y1 + popVar S.y0 - popVar S.unitEffect := by
  sorry

/-- **Neyman's theorem, part 1** (Ding Theorem 4.1(1)): under complete randomization the
difference in means is unbiased for the finite-population average causal effect. -/
theorem differenceInMeans_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty, as in the CRE of Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (diffInMeans S) = S.finiteATE := by
  sorry

/-- **Neyman's theorem, part 2** (Ding Theorem 4.1(2), eqs. (4.1)–(4.2)): the exact
randomization variance of the difference in means. The third term `-S²(τ)/n` is the
finite-population correction; it is the term that cannot be estimated from the data. -/
theorem differenceInMeans_variance (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty, as in the CRE of Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀)
    -- LEAN-ONLY: at least two units, else the divisor `n - 1` in `popVar` vanishes
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) - popVar S.unitEffect / (n : ℝ) := by
  sorry

/-- Under a constant treatment effect the finite-population correction vanishes, so the
randomization variance is the familiar two-term expression (Ding §4.2). -/
theorem differenceInMeans_variance_of_constantEffect (S : ScienceTable n) {τ : ℝ}
    -- USER-INPUT: the additive constant-effect model; Ding §4.2
    (hconst : S.ConstantEffect τ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁) (h0 : 0 < n₀)
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) := by
  sorry

end StatLean.CausalInference
