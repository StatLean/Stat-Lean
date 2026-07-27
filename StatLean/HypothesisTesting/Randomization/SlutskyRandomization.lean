import StatLean.HypothesisTesting.Randomization.Asymptotics

/-!
# A Slutsky theorem for randomization distributions

Randomization distributions are usually built from a statistic that is itself a rescaled
and recentred version of a simpler one — studentization being the canonical example. This
file supplies the Slutsky-type transfer: if the base statistic satisfies the joint
asymptotic-independence condition, and the random scaling and shift stabilize at
constants, then the randomization distribution of the affine combination converges to the
law of the correspondingly transformed limit.

Given statistic sequences $T_n$, $A_n$, $B_n$, write
$$ \hat R_n^{AT+B}(t) \;=\; |\mathbf{G}_n|^{-1} \sum_{g \in \mathbf{G}_n}
   \mathbf{1}\bigl\{A_n(gX^n)\,T_n(gX^n) + B_n(gX^n) \le t\bigr\} $$
for the randomization distribution of the transformed statistic. If
$(T_n(G_nX^n), T_n(G_n'X^n)) \xrightarrow{d} (T, T')$ with $T, T'$ independent and
$R$-distributed, and if $A_n(G_nX^n) \xrightarrow{P} a$, $B_n(G_nX^n) \xrightarrow{P} b$,
then
$$ \hat R_n^{AT+B}(t) \;\xrightarrow{P}\; R^{aT+b}(t) $$
at every continuity point of the law $R^{aT+b}$ of $aT + b$.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.2 (a Slutsky theorem
for randomization distributions). (`TSH4 §17.3 Thm 17.3.2`.)

**Proof formalization notes.**
* *The exact requirement on the random scalings.* No invariance of $A_n$ or $B_n$ under
  the group is assumed — this is worth stating plainly, because it is the natural guess
  and it is not what the hypothesis says. What is required is that the scalings converge
  in probability **when evaluated at the randomized data** $G_nX^n$, with $G_n$ uniform on
  the group and independent of $X^n$ — not at $X^n$ itself. Since the group is finite and
  $G_n$ is uniform, that is the mixture statement
  $|\mathbf{G}_n|^{-1}\sum_g P_n\{|A_n(g\cdot x) - a| \ge \varepsilon\} \to 0$, which is
  the definition of `TendstoInProbRandomized`. In the studentized application the scaling
  is a pooled sample variance, which is *not* invariant under the group; what is true, and
  what the hypothesis captures, is that it converges in probability under a random
  relabelling.
* Correspondingly, the randomization distribution being transformed evaluates $A_n$ and
  $B_n$ at $gX^n$ too, matching the display above; the statistic whose randomization
  distribution is taken is the pointwise combination `fun y => A n y * T n y + B n y`.
* The limit law is written as the pushforward `R.map (fun u => a * u + b)`, i.e. the law of
  $aT + b$.
* *A caveat on the inversion formula.* The classical parenthetical
  $R^{aT+b}(t) = R^{T}((t-b)/a)$ "for $a \ne 0$" is correct only for $a > 0$: for $a < 0$
  the affine map reverses order and the identity picks up a reflection,
  $P\{aT + b \le t\} = 1 - P\{T < (t-b)/a\}$, which differs from
  $R^{T}((t-b)/a)$ unless $R^{T}$ is continuous there. `cdf_map_affine` is therefore stated
  for `0 < a` only; that is the case every application needs (scalings are positive).
* The setting is the same triangular array as `Randomization/Asymptotics`, whose
  `TendstoInProbTriangular` and `randPairLaw` are reused verbatim.

**Bibliographic comments.** The transfer principle for randomization distributions under
random rescaling, and its use to justify studentized permutation tests, is due to
A. Janssen ("Studentized permutation tests for non-i.i.d. hypotheses and the generalized
Behrens–Fisher problem," *Statist. Probab. Lett.* **36** (1997), 9–21) and was developed
into a general theory by E. Chung and J. P. Romano ("Exact and asymptotically robust
permutation tests," *Ann. Statist.* **41** (2013), 484–507), building on
J. P. Romano ("Bootstrap and randomization tests of some nonparametric hypotheses," *Ann.
Statist.* **17** (1989), 141–159; "On the behavior of randomization tests without a group
invariance assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692) and on the
large-sample framework of W. Hoeffding ("The large-sample power of tests based on
permutations of observations," *Ann. Math. Statist.* **23** (1952), 169–192).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-- **Convergence in probability at randomized data.** `A n` evaluated at `g • x`, with
`g` uniform on the finite group and independent of the data, converges in probability to
`a`. Written out as the mixture over the group, this is
`|Gₙ|⁻¹ ∑_g Pₙ{|Aₙ(g·x) − a| ≥ ε} → 0` for every `ε > 0`.

Note what this does **not** say: `A n` is not assumed invariant under the group. -/
def TendstoInProbRandomized {𝓨 : ℕ → Type*} [∀ n, MeasurableSpace (𝓨 n)]
    (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓨 n)]
    (P : ∀ n, Measure (𝓨 n)) (A : ∀ n, 𝓨 n → ℝ) (a : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto
    (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | ε ≤ |A n (g • x) - a|}) atTop (𝓝 0)

/-- The c.d.f. of an affine image, for a **positive** scaling:
`R^{aT+b}(t) = R^{T}((t − b)/a)`. See the file notes for why `a < 0` is excluded rather
than folded in. -/
lemma cdf_map_affine (R : Measure ℝ) [IsProbabilityMeasure R] {a : ℝ}
    -- USER-INPUT: positive scaling; the order-preserving case
    (ha : 0 < a) (b t : ℝ) :
    cdf (R.map (fun u => a * u + b)) t = cdf R ((t - b) / a) := by
  have hf : Measurable (fun u : ℝ => a * u + b) := by fun_prop
  have : IsProbabilityMeasure (R.map (fun u => a * u + b)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real,
    Measure.map_apply hf measurableSet_Iic]
  congr 2
  ext u
  simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ ha]
  constructor
  · intro h; linarith
  · intro h; linarith

section Slutsky

variable {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
  {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]

/-- **Slutsky's theorem for randomization distributions.** If the base statistic satisfies
the joint asymptotic-independence condition with limit law `R`, and the random scaling and
shift converge in probability *at the randomized data* to constants `a` and `b`, then the
randomization distribution of `AₙTₙ + Bₙ` converges in probability to the law of `aT + b`
at each of its continuity points. -/
theorem randDist_affine_tendstoInProb (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T A B : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R] {a b t : ℝ}
    -- USER-INPUT: joint weak convergence of the base statistic at two independent uniform
    -- group elements, to a product law (asymptotic independence)
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    -- USER-INPUT: the random scaling converges in probability **at randomized data** to
    -- the constant `a`; no group invariance of `A` is assumed
    (hA : TendstoInProbRandomized G P A a)
    -- USER-INPUT: the random shift converges in probability **at randomized data** to the
    -- constant `b`; no group invariance of `B` is assumed
    (hB : TendstoInProbRandomized G P B b)
    -- USER-INPUT: `t` is a continuity point of the limit law of `aT + b`
    (hcont : ContinuousAt (cdf (R.map (fun u => a * u + b))) t) :
    TendstoInProbTriangular P
      (fun n x => randDist (G n) (fun y => A n y * T n y + B n y) x t)
      (cdf (R.map (fun u => a * u + b)) t) := by
  -- TODO (deferred; route re-derived this session, no false statement involved).
  -- Reduction: `randPairLaw` of the *deterministic* affine image `a·Tₙ + b` is the pushforward
  -- of `randPairLaw (Tₙ)` along `Prod.map (a·+b) (a·+b)`, so `WeakConverges.map` together with
  -- `Measure.map_prod_map` turns `hjoint` into the joint hypothesis for the limit
  -- `R^{aT+b} ⊗ R^{aT+b}`; feeding that into `randDist_tendstoInProb_cdf` gives the claim.
  -- What is genuinely missing is the passage from the deterministic affine image to the random
  -- one. `Randomization/PairCLT.weakConverges_randPairLaw_of_tendstoInProb` is the right
  -- transfer, but two hypotheses of it are not available here:
  --  (a) it assumes the data law is group-invariant, which is deliberately NOT assumed in this
  --      file (`hA`/`hB` are stated as mixtures over the group precisely because no invariance
  --      holds); a mixture-form variant of that lemma is needed — its proof collapses the group
  --      average through `hinv`, and without invariance the group-averaged remainder bound has
  --      to be carried through instead. That is a mechanical variant, not an obstruction.
  --  (b) the remainder is `(Aₙ − a)·Tₙ + (Bₙ − b)`, and `(Aₙ − a)·Tₙ → 0` in probability needs
  --      `Tₙ = O_P(1)` under the randomized law, i.e. **tightness** of the mixture laws — which
  --      follows from `hjoint` (a weakly convergent sequence of probability measures is tight)
  --      but has no packaged form in the repository. This is the real remaining brick.
  -- Also note the frozen signature omits measurability of `T n`, `A n`, `B n` and of the action,
  -- which every step above consumes; those would have to be added (as they were in
  -- `Randomization/Asymptotics`) for the argument to go through.
  sorry

end Slutsky

end StatLean.HypothesisTesting
