import StatLean.CausalInference.Core.FiniteDefs
import StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments

/-!
# Complete randomization — the assignment moments

Under complete randomization the treatment vector is a uniform draw from the assignment
vectors with exactly `n₁` ones, i.e. a simple random sample of `n₁` of the `n` units. This
file bridges `completeDesign` to the sampling-without-replacement moments already
formalized in `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments` and records
the three classical identities

$$\mathbb E[Z_i]=\frac{n_1}{n},\qquad
  \operatorname{Var}(Z_i)=\frac{n_1n_0}{n^2},\qquad
  \operatorname{Cov}(Z_i,Z_j)=-\frac{n_1n_0}{n^2(n-1)}\ (i\neq j).$$

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 3.1 (the completely randomized
experiment) and Lemma C.1 (§C.1, p. 433: the first two moments of the inclusion
indicators of a simple random sample), applied to the CRE via Definition C.1.
(`Ding Definition 3.1; Lemma C.1`.) The corresponding design in G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, is the completely randomized assignment mechanism of
Part II. (`IR Part II`.)

**Proof formalization notes.**

* The bridge `expect_completeDesign_eq` transports an expectation over
  `completeSupport n n₁` to one over `SubsetsOfCard n n₁` along
  `z ↦ {i | zᵢ = 1}` / `s ↦ (i ↦ i ∈ s)`, which is a bijection. Every moment identity is
  then a restatement of `expect_weight`, `expect_weight_pair` and `cov_weight`.
* This is a **cross-area import of another area's `ForMathlib/` layer**, which the project
  layering rules permit (`CLAUDE.md` §3): `HypergeometricMoments` is Mathlib-only and
  theorem-agnostic. Nothing from the `HypothesisTesting` concept layer is used.
-/

namespace StatLean.CausalInference

open StatLean.HypothesisTesting

variable {n n₁ : ℕ}

/-- The map from an `n₁`-subset of units to the assignment vector treating exactly that
subset. -/
def ofSubset (s : SubsetsOfCard n n₁) : Assignment n := fun i => decide (i ∈ s.val)

/-- Assignments in the complete-randomization support are exactly the images of
`n₁`-subsets: `ofSubset` is a bijection onto `completeSupport n n₁`. -/
theorem ofSubset_mem_completeSupport (s : SubsetsOfCard n n₁) :
    ofSubset s ∈ completeSupport n n₁ := by
  sorry

/-- The treated set of `ofSubset s` is `s`. -/
theorem armIdx_ofSubset_true (s : SubsetsOfCard n n₁) : armIdx (ofSubset s) true = s.val := by
  sorry

/-- The inclusion weight of `HypergeometricMoments` is the treatment indicator. -/
theorem ind_ofSubset (i : Fin n) (s : SubsetsOfCard n n₁) :
    ind (ofSubset s i) = weight i s := by
  sorry

/-- **The bridge**: expectations under complete randomization are uniform averages over
`n₁`-subsets. -/
theorem expect_completeDesign_eq (h : n₁ ≤ n) (f : Assignment n → ℝ) :
    (completeDesign n n₁ h).expect f = expect (fun s : SubsetsOfCard n n₁ => f (ofSubset s)) := by
  sorry

/-- The support of complete randomization has `C(n, n₁)` elements
(Ding Definition 3.1). -/
theorem card_completeSupport (h : n₁ ≤ n) : (completeSupport n n₁).card = n.choose n₁ := by
  sorry

/-- Every assignment in the support treats exactly `n₁` units. -/
theorem card_armIdx_true (h : n₁ ≤ n) {z : Assignment n} (hz : z ∈ completeSupport n n₁) :
    (armIdx z true).card = n₁ := by
  sorry

/-- Every assignment in the support leaves exactly `n - n₁` units untreated. -/
theorem card_armIdx_false (h : n₁ ≤ n) {z : Assignment n} (hz : z ∈ completeSupport n n₁) :
    (armIdx z false).card = n - n₁ := by
  sorry

/-- **First moment** (Ding Lemma C.1): `E[Zᵢ] = n₁/n`. -/
theorem completeDesign_expect_ind (h : n₁ ≤ n) (i : Fin n) :
    (completeDesign n n₁ h).expect (fun z => ind (z i)) = (n₁ : ℝ) / (n : ℝ) := by
  sorry

/-- **Second cross moment** (Ding Lemma C.1): `E[ZᵢZⱼ] = n₁(n₁-1)/(n(n-1))` for `i ≠ j`. -/
theorem completeDesign_expect_ind_mul (h : n₁ ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct units; Ding Lemma C.1
    (hij : i ≠ j) :
    (completeDesign n n₁ h).expect (fun z => ind (z i) * ind (z j))
      = ((n₁ : ℝ) * ((n₁ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  sorry

/-- **Variance of an inclusion indicator** (Ding Lemma C.1): `Var(Zᵢ) = n₁n₀/n²`. -/
theorem completeDesign_var_ind (h : n₁ ≤ n) (i : Fin n) :
    (completeDesign n n₁ h).var (fun z => ind (z i))
      = ((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / (n : ℝ) ^ 2 := by
  sorry

/-- **Covariance of two inclusion indicators** (Ding Lemma C.1):
`Cov(Zᵢ, Zⱼ) = -n₁n₀/(n²(n-1))` for `i ≠ j`. The negative sign is the
sampling-without-replacement effect. -/
theorem completeDesign_cov_ind (h : n₁ ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct units; Ding Lemma C.1
    (hij : i ≠ j) :
    (completeDesign n n₁ h).expect (fun z => ind (z i) * ind (z j))
        - (completeDesign n n₁ h).expect (fun z => ind (z i))
          * (completeDesign n n₁ h).expect (fun z => ind (z j))
      = -((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
  sorry

/-- **Variance of a linear statistic in the assignment** (Ding Lemma C.2, in the form of
`HypergeometricMoments.var_linear`): for deterministic coefficients `c`,
`Var(∑ᵢ cᵢZᵢ) = n₁n₀/(n(n-1)) · ∑ᵢ(cᵢ - c̄)²`. This is the engine behind Neyman's
variance formula. -/
theorem completeDesign_var_linear (h : n₁ ≤ n)
    -- USER-INPUT: at least two units (the factor `n - 1` is a denominator); Ding Lemma C.2
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    (completeDesign n n₁ h).var (fun z => ∑ i, c i * ind (z i))
      = ((n₁ : ℝ) * ((n : ℝ) - (n₁ : ℝ))) / ((n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, (c i - popMean c) ^ 2 := by
  sorry

end StatLean.CausalInference
