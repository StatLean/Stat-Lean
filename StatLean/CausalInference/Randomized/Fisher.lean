import StatLean.CausalInference.Core.FinitePopulation

/-!
# The Fisher randomization test — finite-sample validity

Under the sharp null every potential outcome is known once the experiment is run, so the
statistic can be recomputed at every assignment the design could have produced. The
resulting p-value

$$p(z)=\Pr_{Z^\ast}\bigl\{T(Z^\ast)\ge T(z)\bigr\}$$

is **super-uniform** under any design: `Pr(p ≤ α) ≤ α` for every `α ≥ 0`. This is exact in
finite samples and needs no distributional assumption whatsoever — only that the design
draws uniformly from its support.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §3.2: the sharp null hypothesis
`H₀ : Yᵢ(1) = Yᵢ(0)` for all `i`, the randomization p-value eq. (3.2), and the validity
statement eq. (3.3) `Pr(p ≤ u) ≤ u` (stated as a display; the proof is left as Problem
3.1). (`Ding §3.2, eqs. (3.2)–(3.3)`.) The same test is developed in G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*,
Cambridge University Press, 2015, ch. 5. (`IR ch. 5`.)

**Proof formalization notes.**

* Validity is proved for an **arbitrary design** and an arbitrary real-valued function `g`
  of the assignment, which is stronger and simpler than the CRE-only statement: the
  argument is that `{z | p(z) ≤ α}` is an upper set for `g`, so it is contained in
  `{z | g z₀ ≤ g z}` for a `g`-minimal element `z₀` of it, and that set has probability
  exactly `p(z₀) ≤ α`. Stratified and matched-pair designs therefore inherit validity with
  no extra work.
* `0 ≤ α` is genuinely needed: for `α < 0` the event is empty and the claim would read
  `0 ≤ α`.
* The sharp null enters only through `SharpNull.observed_eq`: it makes the observed
  outcome vector — and hence the statistic value function `g` — independent of which
  assignment was realized. That step is isolated in `sharpNull_statistic_eq`.
* StatLean already has a measure-theoretic randomization test for group-invariant laws
  (`StatLean.HypothesisTesting.superUniform_randPValue`, over a `MulAction` of a finite
  group). This file is the *design-based* counterpart on a finite population; it is
  deliberately independent of that concept-layer development.

**Bibliographic comments.** R. A. Fisher, *The Design of Experiments*, Oliver & Boyd,
Edinburgh, 1935 (the lady-tasting-tea experiment). The super-uniformity argument for
discrete randomization distributions is standard; see also E. L. Lehmann and
J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer, 2005, ch. 15.
-/

namespace StatLean.CausalInference

variable {n : ℕ}

/-- The randomization p-value is nonnegative. -/
theorem fisherPValue_nonneg (D : Design n) (g : Assignment n → ℝ) (z : Assignment n) :
    0 ≤ fisherPValue D g z := by
  sorry

/-- The randomization p-value is at most one. -/
theorem fisherPValue_le_one (D : Design n) (g : Assignment n → ℝ) (z : Assignment n) :
    fisherPValue D g z ≤ 1 := by
  sorry

/-- The p-value at an assignment attaining the maximum statistic value is the probability
of the "at least as extreme" set, which always contains that assignment; in particular the
p-value is strictly positive on the support. -/
theorem fisherPValue_pos (D : Design n) (g : Assignment n → ℝ) {z : Assignment n}
    (hz : z ∈ D.support) :
    0 < fisherPValue D g z := by
  sorry

/-- Monotonicity: a larger statistic value gives a smaller p-value. -/
theorem fisherPValue_antitone (D : Design n) (g : Assignment n → ℝ) {z z' : Assignment n}
    (h : g z ≤ g z') :
    fisherPValue D g z' ≤ fisherPValue D g z := by
  sorry

/-- **Validity of the randomization test** (Ding eq. (3.3)): under any design, the
randomization p-value is super-uniform, `Pr(p ≤ α) ≤ α`. Consequently the test that
rejects when `p ≤ α` has size at most `α`, exactly, in finite samples. -/
theorem prob_fisherPValue_le (D : Design n) (g : Assignment n → ℝ) {α : ℝ}
    -- LEAN-ONLY: a nonnegative level (for `α < 0` the event is empty and the claim is false)
    (hα : 0 ≤ α) :
    D.prob {z | fisherPValue D g z ≤ α} ≤ α := by
  sorry

/-- Under the sharp null the statistic recomputed at a hypothetical assignment does not
depend on the realized assignment: the observed outcome vector is the same whatever was
assigned (Ding §3.2). This is what makes the randomization distribution computable. -/
theorem sharpNull_statistic_eq (S : ScienceTable n) (hS : S.SharpNull)
    (T : Assignment n → (Fin n → ℝ) → ℝ) (z z' : Assignment n) :
    T z' (S.observed z) = T z' S.y0 := by
  sorry

/-- **The Fisher randomization test is valid** (Ding §3.2, eqs. (3.2)–(3.3)): under the
sharp null, for any test statistic `T` and any design, the probability that the
randomization p-value falls below the level `α` is at most `α`. -/
theorem sharpNull_prob_fisherPValue_le (D : Design n) (S : ScienceTable n)
    -- USER-INPUT: Fisher's sharp null `Yᵢ(1) = Yᵢ(0)` for every unit; Ding §3.2
    (hS : S.SharpNull)
    -- USER-INPUT: the test statistic, a function of the assignment and the observed vector
    (T : Assignment n → (Fin n → ℝ) → ℝ) {α : ℝ}
    -- LEAN-ONLY: a nonnegative level; no scope change
    (hα : 0 ≤ α) :
    D.prob {z | fisherPValue D (fun z' => T z' (S.observed z')) z ≤ α} ≤ α := by
  sorry

end StatLean.CausalInference
