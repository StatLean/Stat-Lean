import StatLean.CausalInference.Randomized.Neyman

/-!
# Neyman's variance estimator — unbiasedness of the arm variances and conservativeness

The third part of Neyman's theorem. The arm sample variances are unbiased for the
corresponding finite-population variances, so

$$\mathbb E[\hat V]=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}
  \quad\Longrightarrow\quad
  \mathbb E[\hat V]-\operatorname{Var}(\hat\tau)=\frac{S^2(\tau)}{n}\ \ge 0 :$$

the estimator `V̂` overestimates the true randomization variance by exactly the
unidentifiable finite-population correction, and is *exactly* unbiased precisely when the
treatment effect is constant.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Theorem 4.1(3) (§4.2, pp. 44–45), with the
unbiasedness of the arm sample variances from Lemma C.3 (§C.1, p. 434: sample variances
of a simple random sample are unbiased). (`Ding Theorem 4.1(3); Lemma C.3`.) Compare
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 6. (`IR ch. 6`.)

**Proof formalization notes.** `armVar_true_unbiased` is Lemma C.3 for the treated arm and
is the only genuinely new computation: expand
`ŝ²(1) = (n₁-1)⁻¹(∑_{i:Zᵢ=1}Yᵢ(1)² - n₁Ȳ₁²)`, take expectations with
`completeDesign_expect_ind` on the first term and `E[Ȳ₁²] = Var(Ȳ₁) + (ȳ(1))²` on the
second, and substitute `Var(Ȳ₁) = n₀S²(1)/(n·n₁)` from `completeDesign_var_linear`. Each
arm needs at least two units for its sample variance to be defined (divisor `card - 1`),
which is Ding's standing `n₁, n₀ ≥ 2` for this part.

**Bibliographic comments.** The conservativeness of `V̂` and its exactness under a
constant effect are already in Neyman (1923); the point that the excess `S²(τ)/n` is
unidentifiable from a single experiment is discussed at length in ch. 4 of the reference.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-- **Unbiasedness of the treated arm sample variance** (Ding Lemma C.3): under complete
randomization, `E[ŝ²(1)] = S²(1)`. -/
theorem armVar_true_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: at least two treated units, so that `ŝ²(1)` is defined; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁)
    -- USER-INPUT: a nonempty control arm; Ding Definition 3.1
    (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armVar S z true) = popVar S.y1 := by
  sorry

/-- **Unbiasedness of the control arm sample variance** (Ding Lemma C.3):
`E[ŝ²(0)] = S²(0)`. -/
theorem armVar_false_unbiased (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: a nonempty treated arm; Ding Definition 3.1
    (h1 : 0 < n₁)
    -- USER-INPUT: at least two control units, so that `ŝ²(0)` is defined; Ding Theorem 4.1(3)
    (h0 : 2 ≤ n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armVar S z false) = popVar S.y0 := by
  sorry

/-- **The expectation of Neyman's variance estimator** (Ding Theorem 4.1(3)):
`E[V̂] = S²(1)/n₁ + S²(0)/n₀`. -/
theorem neymanVarEst_expectation (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms have at least two units; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
      = popVar S.y1 / (n₁ : ℝ) + popVar S.y0 / (n₀ : ℝ) := by
  sorry

/-- **The exact bias of Neyman's variance estimator** (Ding Theorem 4.1(3)): the estimator
exceeds the true randomization variance by exactly `S²(τ)/n`. -/
theorem neymanVarEst_bias (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms have at least two units; Ding Theorem 4.1(3)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀)
    -- LEAN-ONLY: at least two units, else the divisor `n - 1` in `popVar` vanishes
    (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
        - (completeDesign n n₁ (by omega)).var (diffInMeans S)
      = popVar S.unitEffect / (n : ℝ) := by
  sorry

/-- **Conservativeness** (Ding Theorem 4.1(3)): Neyman's variance estimator is unbiased
*upward* — its expectation never underestimates the true randomization variance. Hence
the associated confidence intervals are conservative. -/
theorem neymanVarEst_conservative (S : ScienceTable n) (hsum : n₁ + n₀ = n)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).var (diffInMeans S)
      ≤ (completeDesign n n₁ (by omega)).expect (neymanVarEst S) := by
  sorry

/-- **Exactness under a constant effect** (Ding Theorem 4.1(3)): the bias `S²(τ)/n`
vanishes exactly when the individual effects are constant, and then `V̂` is unbiased. -/
theorem neymanVarEst_unbiased_of_constantEffect (S : ScienceTable n) {τ : ℝ}
    -- USER-INPUT: the additive constant-effect model; Ding Theorem 4.1(3)
    (hconst : S.ConstantEffect τ) (hsum : n₁ + n₀ = n)
    (h1 : 2 ≤ n₁) (h0 : 2 ≤ n₀) (hn : 2 ≤ n) :
    (completeDesign n n₁ (by omega)).expect (neymanVarEst S)
      = (completeDesign n n₁ (by omega)).var (diffInMeans S) := by
  sorry

end StatLean.CausalInference
