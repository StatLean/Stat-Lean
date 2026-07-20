import StatLean.HypothesisTesting.GoodnessOfFit.ChiSquaredMultinomial
import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin

/-!
# Asymptotic maximin optimality of Pearson's chi-squared test

For the multinomial goodness-of-fit problem with simple null `p = π`, the chi-squared test
is *asymptotically maximin* over the shrinking families of alternatives
`p = π + h n^{-1/2}` whose standardized distance
$$ \lambda(h) \;=\; \sum_{j=1}^{k+1} \frac{h_j^2}{\pi_j} $$
from the null is at least `b²`. Two statements:

* `chiSquared_maximin_upper_bound` — no asymptotically level-`α` test sequence can have
  limiting minimum power over that family exceeding `P{χ²_k(b²) > c_{k,1−α}}`;
* `chiSquared_asymptotically_maximin` — Pearson's test attains that value, and therefore
  maximizes the limiting minimum power among all tests of asymptotic level `α`.

The file also carries the analytic lemma about the noncentral tail function
$$ M(k,h) \;=\; P\bigl\{\chi^2_k(h^2) > c_{k,1-\alpha}\bigr\} $$
that explains what happens when the number of cells is allowed to grow: for a *fixed*
noncentrality the power of the chi-squared test decreases in `k` and degenerates to the
level `α`, while power is retained only if the noncentrality grows like `(2k)^{1/2}`.
This is the quantitative reason why the number of cells cannot be increased for free, and
it is the same phenomenon that governs the large-`k` smooth test.

* `noncentralTail` — the function `M(k,h)`;
* `noncentralTail_antitone` — `M(·, h)` is nonincreasing, strictly so for `h ≠ 0`;
* `noncentralTail_tendsto_level` — `M(k, h_k) → α` when `h_k` converges to a finite limit;
* `noncentralTail_tendsto_normal` — `M(k, h_k) → 1 − Φ(z_{1−α} − γ)` when
  `(2k)^{-1/2} h_k² → γ`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.3 (Pearson's Chi-Squared Statistic), Theorem 16.3.2 (the asymptotic maximin property
of the chi-squared test) and Lemma 16.3.1 (the noncentral chi-squared tail function `M(k,h)`).
(`TSH4 §16.3 Thm 16.3.2, Lem 16.3.1`.)

**Proof formalization notes.**
* The local experiments are carried as data: `Q n h` is the law of a sample of size `n`
  drawn with cell probabilities `π + h n^{-1/2}`, and the observations `X n` are attached
  to it by the i.i.d. hypotheses. This is the same triangular-array format as in
  `ChiSquaredMultinomial.lean`, refined by an extra local-parameter index so that a power
  *function* over the local parameter is available.
* The alternative family transcribes all three constraints of the source display: the
  standardized distance `∑ⱼ hⱼ²/πⱼ ≥ b²`, the centring `∑ⱼ hⱼ = 0` (the local shift of a
  probability vector), and the requirement that the perturbed vector still be a
  probability vector — the latter being sample-size dependent, hence a family of
  alternative sets `S n` rather than a single one.
* The upper bound is the multinomial instance of `asymptotic_maximin_upper_bound`, with
  the multinomial information matrix; the attainment half is an argument by contradiction
  along subsequences of local parameters, using that a diverging coordinate forces power
  one (so the infimum is attained in the limit at a bounded shift) and that the noncentral
  chi-squared family has monotone likelihood ratio in the noncentrality parameter (so the
  worst case is `λ = b²` exactly).
* Pearson's test appears as the nonrandomized critical function `1{Qₙ > c}` rather than
  as a rejection probability, so that it is a competitor in the same class as the tests
  quantified over in the optimality statement.
* The critical value is supplied as a real `c` with the defining property
  `χ²_k(c, ∞) = α`, and in the growing-`k` lemma as a family `c : ℕ → ℝ` with that
  property at each `k`; no quantile function is introduced.
* Clauses (ii) and (iii) of the tail lemma consume the large-`k` results of the sibling
  brick `ForMathlib/NoncentralChiSquared.lean` — `tendsto_chiSquared_quantile_standardized`
  for `(c_k − k)/√(2k) → z`, and `weakConverges_noncentralChiSquared_standardized` for
  `(χ²_k(l_k) − k)/√(2k) ⇒ N(γ, 1)` — so they are assembly, not new analysis. Clause (i)
  is independent of both and rests on the monotone likelihood ratio of the family.
* Noncentrality parameters are passed to `noncentralChiSquared` through `Real.toNNReal`,
  that function taking its parameter in `ℝ≥0`; the values used (`b²`, `h²`) are squares,
  so the coercion is the identity on them.

**Bibliographic comments.** The statistic is due to K. Pearson (*Philosophical Magazine*,
Series 5, **50** (1900), 157–175). Its optimality among tests of asymptotic level `α`,
in the maximin sense over shrinking families of local alternatives, follows the
least-favourable mixture program of J. Neyman and E. S. Pearson (*Phil. Trans. R. Soc. A*
**231** (1933), 289–337) and A. Wald (*Ann. of Math.* **46** (1945), 265–280), transported
to the local limit experiment of L. Le Cam (*Univ. California Publ. Statist.* **3** (1960),
37–98). The degeneration of chi-squared power as the number of cells grows was analysed by
H. Mann and A. Wald ("On the choice of the number of class intervals in the application of
the chi square test," *Ann. Math. Statist.* **13** (1942), 306–317) and by
W. G. Cochran ("The χ² test of goodness of fit," *Ann. Math. Statist.* **23** (1952),
315–345).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (chiSquared)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The local alternative family -/

/-- The **local alternative shell** for the multinomial problem at sample size `n`: the
local shifts `h` that are centred (`∑ⱼ hⱼ = 0`), keep the perturbed vector
`π + h n^{-1/2}` a probability vector, and are at standardized distance at least `b` from
the null, `∑ⱼ hⱼ²/πⱼ ≥ b²`. -/
def multinomialShell {k : ℕ} (π : Fin (k + 1) → ℝ) (b : ℝ) (n : ℕ) :
    Set (Fin (k + 1) → ℝ) :=
  {h | (∑ j, h j = 0) ∧ b ^ 2 ≤ multinomialNoncentrality π h ∧
    ∀ j, 0 ≤ π j + h j / Real.sqrt (n : ℝ)}

/-! ### (i) The upper bound -/

/-- **No test beats the chi-squared value.** For any test sequence whose power at the null
tends to `α`, the limiting minimum power over the local shell is at most
`P{χ²_k(b²) > c_{k,1−α}}`.

This is the multinomial instance of `asymptotic_maximin_upper_bound`: the multinomial
information matrix has quadratic form `h ↦ ∑ⱼ hⱼ²/πⱼ` on centred shifts, so the shell of
that lemma is exactly `multinomialShell`. -/
theorem chiSquared_maximin_upper_bound {k : ℕ} {α b c : ℝ} {π : Fin (k + 1) → ℝ}
    {Q : ℕ → (Fin (k + 1) → ℝ) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)} {φ : ℕ → Ω → ℝ}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the shell has positive radius
    (hb : 0 < b)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the cell probabilities are
    -- `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n h, ∀ i, ∀ j,
      ((Measure.map (X n i) (Q n h)) {j}).toReal = π j + h j / Real.sqrt (n : ℝ))
    -- USER-INPUT: the competitors are randomized tests
    (hφ : ∀ n, IsCriticalFn (φ n))
    -- USER-INPUT: the competitors are asymptotically of level `α` at the null
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) '' multinomialShell π b n)) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  sorry

/-! ### (ii) Attainment by Pearson's test -/

/-- **Pearson's test is asymptotically maximin.** The nonrandomized test `1{Qₙ > c}`
attains the bound of `chiSquared_maximin_upper_bound`: its minimum power over the local
shell converges to `P{χ²_k(b²) > c_{k,1−α}}` (first conjunct), and consequently it
maximizes the limiting minimum power among all test sequences of asymptotic level `α`
(second conjunct).

The worst case over the shell is asymptotically attained on its boundary
`∑ⱼ hⱼ²/πⱼ = b²`, since the noncentral chi-squared tail is increasing in the
noncentrality parameter. -/
theorem chiSquared_asymptotically_maximin {k : ℕ} {α b c : ℝ} {π : Fin (k + 1) → ℝ}
    {Q : ℕ → (Fin (k + 1) → ℝ) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)}
    -- USER-INPUT: at least one degree of freedom
    (hk : 0 < k)
    -- USER-INPUT: the shell has positive radius
    (hb : 0 < b)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c` is the `1 − α` quantile of `χ²_k`, i.e. the critical value
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    -- USER-INPUT: the null cell probabilities are an interior point of the simplex
    (hπpos : ∀ j, 0 < π j)
    -- USER-INPUT: the null cell probabilities sum to one
    (hπsum : ∑ j, π j = 1)
    -- USER-INPUT: at every stage and every local parameter each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: under every local parameter the trials are i.i.d.; Pearson 1900
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    -- USER-INPUT: under the local parameter `h` the cell probabilities are
    -- `πⱼ + hⱼ n^{-1/2}`
    (hcell : ∀ n h, ∀ i, ∀ j,
      ((Measure.map (X n i) (Q n h)) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < pearsonQ π (X n) ω then (1 : ℝ) else 0) h)
        '' multinomialShell π b n)) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal))
      ∧ ∀ ψ : ℕ → Ω → ℝ, (∀ n, IsCriticalFn (ψ n)) →
        Tendsto (fun n => power (Q n) (ψ n) 0) atTop (nhds α) →
        limsup (fun n => sInf ((fun h => power (Q n) (ψ n) h)
            '' multinomialShell π b n)) atTop
          ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  sorry

/-! ### The noncentral tail function as the number of cells grows -/

/-- The **noncentral tail function** `M(k,h) = P{χ²_k(h²) > crit}`: the limiting power of
the chi-squared test with `k` degrees of freedom and critical value `crit` against a local
alternative at standardized distance `|h|` from the null. In the intended use `crit` is
the `1 − α` quantile of `χ²_k`, so that `M(k, 0) = α`. -/
noncomputable def noncentralTail (k : ℕ) (crit h : ℝ) : ℝ :=
  ((noncentralChiSquared k (h ^ 2).toNNReal) (Set.Ioi crit)).toReal

/-- **(i) `M(·, h)` is nonincreasing in the number of degrees of freedom**, and strictly
decreasing when `h ≠ 0`. Spending degrees of freedom on directions in which the
alternative does not move costs power. -/
theorem noncentralTail_antitone {α h : ℝ} {c : ℕ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c k` is the `1 − α` quantile of `χ²_k`, for every `k ≥ 1`
    (hc : ∀ k, 0 < k → chiSquared k (Set.Ioi (c k)) = ENNReal.ofReal α) :
    (∀ k₁ k₂ : ℕ, 0 < k₁ → k₁ ≤ k₂ →
        noncentralTail k₂ (c k₂) h ≤ noncentralTail k₁ (c k₁) h)
      ∧ (h ≠ 0 → ∀ k₁ k₂ : ℕ, 0 < k₁ → k₁ < k₂ →
          noncentralTail k₂ (c k₂) h < noncentralTail k₁ (c k₁) h) := by
  sorry

/-- **(ii) A bounded noncentrality is asymptotically invisible.** If `h_k` converges to a
finite limit then `M(k, h_k) → α`: with a fixed amount of signal, the chi-squared test
with growing degrees of freedom degenerates to a test of level `α` and no power. In
particular `M(k, h) → α` for fixed `h`. -/
theorem noncentralTail_tendsto_level {α : ℝ} {c : ℕ → ℝ} {hseq : ℕ → ℝ} {h : ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c k` is the `1 − α` quantile of `χ²_k`, for every `k ≥ 1`
    (hc : ∀ k, 0 < k → chiSquared k (Set.Ioi (c k)) = ENNReal.ofReal α)
    -- USER-INPUT: the noncentralities converge to a finite limit
    (hconv : Tendsto hseq atTop (nhds h)) :
    Tendsto (fun k => noncentralTail k (c k) (hseq k)) atTop (nhds α) := by
  sorry

/-- **(iii) The signal must grow like `(2k)^{1/2}` to be seen.** If
`(2k)^{-1/2} h_k² → γ` then `M(k, h_k) → 1 − Φ(z_{1−α} − γ)`, where `Φ` is the standard
normal c.d.f. and `z_{1−α}` its `1 − α` quantile. The normal approximation
`χ²_k ≈ N(k, 2k)` is what puts the standardized noncentrality `(2k)^{-1/2}h²` in the role
of a normal shift. -/
theorem noncentralTail_tendsto_normal {α γ z : ℝ} {c : ℕ → ℝ} {hseq : ℕ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: `c k` is the `1 − α` quantile of `χ²_k`, for every `k ≥ 1`
    (hc : ∀ k, 0 < k → chiSquared k (Set.Ioi (c k)) = ENNReal.ofReal α)
    -- USER-INPUT: `z` is the `1 − α` quantile of the standard normal law
    (hz : gaussianReal 0 1 (Set.Ioi z) = ENNReal.ofReal α)
    -- USER-INPUT: the noncentralities grow at the critical rate `(2k)^{1/2}`
    (hrate : Tendsto (fun k : ℕ => (hseq k) ^ 2 / Real.sqrt (2 * (k : ℝ))) atTop
      (nhds γ)) :
    Tendsto (fun k => noncentralTail k (c k) (hseq k)) atTop
      (nhds ((gaussianReal 0 1 (Set.Ioi (z - γ))).toReal)) := by
  sorry

end StatLean.HypothesisTesting
