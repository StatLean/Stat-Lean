import StatLean.CausalInference.Randomized.MatchedPairs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rosenbaum's sensitivity model for matched observational studies

In a matched observational study the assignment within a pair is *not* a fair coin: hidden
confounding can tilt it. Rosenbaum's model bounds the tilt by a single parameter `Γ ≥ 1`,

$$\frac1{1+\Gamma}\ \le\ \pi_i\ \le\ \frac{\Gamma}{1+\Gamma},$$

where `π_i` is the probability that the first unit of pair `i` is the treated one. For a
sign-score statistic `T = ∑_i S_i q_i` with nonnegative scores `q_i`, the worst case over
the whole model is attained at the *extreme* tilt `π_i ≡ Γ/(1+Γ)`; so a p-value computed
under that extreme is valid for every law in the model, and it degrades monotonically as
`Γ` grows. Reporting the `Γ` at which significance is lost is the standard sensitivity
summary.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 19 (*Rosenbaum-Style p-Values for Matched
Observational Studies with Unmeasured Confounding*): **Assumption 19.1** (§19.1, p. 258:
the odds-ratio bound `1/(1+Γ) ≤ π_{i1} ≤ Γ/(1+Γ)`); §19.2 (pp. 258–259: for
`T = ∑ᵢSᵢqᵢ` with `qᵢ ≥ 0`, the largest p-value under Assumption 19.1 is attained at
`Sᵢ` i.i.d. `Bernoulli(Γ/(1+Γ))`, with the stated worst-case moments — this is running
text, with no theorem number). (`Ding Assumption 19.1; §19.2`.) Sensitivity analysis and
bounds are ch. 22 of G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics,
Social, and Biomedical Sciences*, Cambridge University Press, 2015. (`IR ch. 22`.)

**Scope.** The book's §19.2 asserts the worst case *and then* passes to a normal
approximation for the p-value. Formalized here is the exact finite-sample core — the
stochastic-dominance statement that makes the worst case worst — plus the monotonicity of
the resulting bound in `Γ`. The normal approximation is not formalized (it would need a
Lindeberg-type CLT for weighted Bernoulli sums and is an approximation, not an identity).

**Proof formalization notes.** The model is a product measure on sign patterns
`Fin m → Bool` with per-pair success probabilities `π : Fin m → ℝ` (each in `[0,1]`);
`biasedProb π c` is the product weight and `biasedExpect` the induced expectation. The
worst-case claim is stochastic dominance of the score sum under coordinatewise increase of
`π`, proved by a **one-coordinate-at-a-time** exchange argument: changing a single `πⱼ`
upward can only increase `P(T ≥ t)` because, conditionally on the other coordinates, the
statistic is monotone in `Sⱼ` (the score `qⱼ ≥ 0`). Iterating over the `m` coordinates
(`Finset.induction` over the set of coordinates already replaced) gives the full
comparison. This is the same hybrid-argument structure used elsewhere in StatLean for
coordinatewise comparisons.

**Bibliographic comments.** P. R. Rosenbaum, *Observational Studies*, 2nd ed., Springer,
2002, ch. 4; the sign-score family covers the sign test, the paired `t`-statistic and
Wilcoxon's signed-rank statistic.
-/

namespace StatLean.CausalInference

variable {m : ℕ}

/-- The **per-pair treatment probability vector** of a matched observational study: `π j`
is the probability that pair `j`'s first unit is the treated one. -/
def SignProbs (m : ℕ) : Type := Fin m → ℝ

/-- **Rosenbaum's sensitivity model** (Ding Assumption 19.1): every pair's assignment
probability lies within the odds-ratio band determined by `Γ`. -/
def RosenbaumModel (π : Fin m → ℝ) (Γ : ℝ) : Prop :=
  ∀ j, 1 / (1 + Γ) ≤ π j ∧ π j ≤ Γ / (1 + Γ)

/-- The **product weight** of a sign pattern under per-pair probabilities `π`. -/
noncomputable def biasedProb (π : Fin m → ℝ) (c : Fin m → Bool) : ℝ :=
  ∏ j, if c j then π j else 1 - π j

/-- The **expectation** of a statistic under the biased (confounded) assignment law. -/
noncomputable def biasedExpect (π : Fin m → ℝ) (f : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ c : Fin m → Bool, biasedProb π c * f c

/-- The **sign-score statistic** `T = ∑ⱼ Sⱼqⱼ` (Ding §19.2), covering the sign test, the
paired `t` statistic and Wilcoxon's signed-rank statistic by choice of scores `q`. -/
noncomputable def signScore (q : Fin m → ℝ) (c : Fin m → Bool) : ℝ :=
  ∑ j, if c j then q j else 0

/-- The **upper-tail probability** of the sign-score statistic under the biased law. -/
noncomputable def biasedTail (π : Fin m → ℝ) (q : Fin m → ℝ) (t : ℝ) : ℝ :=
  biasedExpect π fun c => if t ≤ signScore q c then 1 else 0

/-- The biased weights are a probability distribution on sign patterns. -/
theorem sum_biasedProb {π : Fin m → ℝ}
    -- USER-INPUT: each coordinate probability is a probability; Ding Assumption 19.1
    (hπ : ∀ j, π j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ c : Fin m → Bool, biasedProb π c = 1 := by
  sorry

/-- The fair-coin case recovers the matched-pair design of `Randomized.MatchedPairs`:
`Γ = 1` gives `π ≡ 1/2` and the biased expectation is the uniform average. -/
theorem biasedExpect_half (f : (Fin m → Bool) → ℝ) :
    biasedExpect (fun _ => (1 : ℝ) / 2) f = pairExpect f := by
  sorry

/-- **The sign-score statistic is monotone in each sign** when the scores are nonnegative:
flipping a pair's sign from `false` to `true` can only increase `T`. This is the
monotonicity that drives the worst-case argument. -/
theorem signScore_le_of_update {q : Fin m → ℝ}
    -- USER-INPUT: nonnegative scores; Ding §19.2
    (hq : ∀ j, 0 ≤ q j) (c : Fin m → Bool) (j : Fin m) :
    signScore q (Function.update c j false) ≤ signScore q (Function.update c j true) := by
  sorry

/-- **One-coordinate stochastic dominance**: raising a single pair's treatment probability
raises the upper-tail probability of the sign-score statistic. -/
theorem biasedTail_mono_single {π π' : Fin m → ℝ} {q : Fin m → ℝ} {t : ℝ} {j : Fin m}
    (hq : ∀ i, 0 ≤ q i)
    (hπ : ∀ i, π i ∈ Set.Icc (0 : ℝ) 1) (hπ' : ∀ i, π' i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the two vectors differ only at `j`, where `π'` is larger
    (heq : ∀ i, i ≠ j → π i = π' i) (hle : π j ≤ π' j) :
    biasedTail π q t ≤ biasedTail π' q t := by
  sorry

/-- **Stochastic dominance under the model** (Ding §19.2): raising every pair's treatment
probability raises the tail probability of the sign-score statistic. Iterating the
one-coordinate comparison. -/
theorem biasedTail_mono {π π' : Fin m → ℝ} {q : Fin m → ℝ} {t : ℝ}
    (hq : ∀ i, 0 ≤ q i)
    (hπ : ∀ i, π i ∈ Set.Icc (0 : ℝ) 1) (hπ' : ∀ i, π' i ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: coordinatewise domination
    (hle : ∀ i, π i ≤ π' i) :
    biasedTail π q t ≤ biasedTail π' q t := by
  sorry

/-- **The worst case is the extreme tilt** (Ding §19.2): under Rosenbaum's model with
parameter `Γ`, the tail probability of any nonnegative sign-score statistic is bounded by
its value at the extreme assignment law `π ≡ Γ/(1+Γ)`. Hence the p-value computed at that
extreme is valid for the whole model. -/
theorem biasedTail_le_extreme {π : Fin m → ℝ} {q : Fin m → ℝ} {t Γ : ℝ}
    -- USER-INPUT: nonnegative scores; Ding §19.2
    (hq : ∀ i, 0 ≤ q i)
    -- USER-INPUT: Rosenbaum's sensitivity model; Ding Assumption 19.1
    (hmodel : RosenbaumModel π Γ)
    -- USER-INPUT: a genuine sensitivity parameter; Ding Assumption 19.1
    (hΓ : 1 ≤ Γ) :
    biasedTail π q t ≤ biasedTail (fun _ => Γ / (1 + Γ)) q t := by
  sorry

/-- **The worst-case bound degrades monotonically in `Γ`** (Ding §19.2): a larger allowance
for hidden bias gives a larger worst-case p-value, which is why one reports the `Γ` at
which significance is lost. -/
theorem biasedTail_extreme_mono {q : Fin m → ℝ} {t Γ Γ' : ℝ} (hq : ∀ i, 0 ≤ q i)
    (hΓ : 1 ≤ Γ) (hle : Γ ≤ Γ') :
    biasedTail (fun _ => Γ / (1 + Γ)) q t ≤ biasedTail (fun _ => Γ' / (1 + Γ')) q t := by
  sorry

/-- **`Γ = 1` is the randomized case**: with no allowance for hidden bias the worst-case law
is the fair coin, so Rosenbaum's procedure reduces to the matched-pair randomization test
of `Randomized.MatchedPairs` (Ding §19.1). -/
theorem rosenbaumModel_one_iff {π : Fin m → ℝ} :
    RosenbaumModel π 1 ↔ ∀ j, π j = 1 / 2 := by
  sorry

end StatLean.CausalInference
