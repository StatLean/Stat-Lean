import StatLean.HypothesisTesting.GoodnessOfFit.ChiSquaredMultinomial
import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin
import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import StatLean.AsymptoticStatistics.ForMathlib.GaussianShift

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
* Clause (i) of the tail lemma (`noncentralTail_antitone`) rests on the *monotone likelihood
  ratio* of `χ²_k(λ)` in `λ`, which stochastic ordering does not give.  That MLR is proved in
  the private `MLR` section of this file, directly from the Gaussian definition and without
  any density formula: the Cameron–Martin ratio `exp(⟪ν, z⟫ − ‖ν‖²/2)` of the shifted Gaussian
  is replaced, by rotation invariance of both the standard Gaussian and the test function
  `f(‖z‖²)`, by its average over the sphere `‖u‖ = ‖ν‖` — realised as the average over the
  direction `‖y‖⁻¹ • y` of an independent Gaussian vector — and the averaged ratio is a
  `cosh`-average, hence a nondecreasing function of `‖z‖`.  The single-crossing step also uses
  the additivity `χ²_{k+1}(λ) = χ²_k(λ) ⋆ χ²₁`, obtained by splitting off one coordinate of
  the product Gaussian with the mean vector placed orthogonally to it.
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
open scoped ENNReal BigOperators NNReal InnerProductSpace

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
    -- REPAIRED HYPOTHESIS (the frozen statement without it is FALSE — counterexample in
    -- the proof note below): the competitors are tests *based on the sample*, i.e. each
    -- `φ n` is a measurable function of `(X n 1, …, X n n)`.  `Q` is abstract data, and
    -- nothing in the remaining hypotheses prevents `Q n h` from encoding `h` in a
    -- coordinate of `Ω` that the observations do not see
    (hφX : ∀ n, ∃ ψ : (Fin n → Fin (k + 1)) → ℝ,
      Measurable ψ ∧ ∀ ω, φ n ω = ψ (fun i => X n i ω))
    -- USER-INPUT: the competitors are asymptotically of level `α` at the null
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) '' multinomialShell π b n)) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  -- TODO (RE-DERIVED, and the STATEMENT WAS FALSE AS FROZEN — repaired above).
  --
  -- COUNTEREXAMPLE to the frozen statement (no `hφX`).  Take `k = 1` (two cells),
  -- `Ω = (ℕ → Fin 2) × ℝ`, `X n i ω = ω.1 i`, and
  --     `Q n h = (i.i.d. multinomial with cell probabilities π + h/√n) ⊗ δ_{h 0}`.
  -- All the frozen hypotheses hold: the `X n i` are measurable, i.i.d. under every `Q n h`
  -- with the prescribed cell probabilities, and each `Q n h` is a probability measure.
  -- Take `φ n ω = if ω.2 = 0 then α else 1`, a critical function with
  -- `power (Q n) (φ n) 0 = α` for every `n`, so `hlevel` holds.  For `k = 1` the constraints
  -- `∑ⱼ hⱼ = 0` and `b² ≤ λ(h)` force `h ≠ 0`, hence `h 0 ≠ 0`, hence `power (Q n) (φ n) h = 1`
  -- for *every* `h ∈ multinomialShell π b n`; that shell is nonempty for all large `n`, so the
  -- left-hand side is `1`.  The right-hand side is `< 1`: by the density representation
  -- `noncentralChiSquared k l = (chiSquared k).withDensity (ENNReal.ofReal ∘ g)` of the MLR
  -- section above, with `g > 0`, and `chiSq_Ioo_pos`/`chiSq_crit_pos`, the complement of
  -- `(c, ∞)` has positive `χ²_k(b²)`-mass.  So the frozen inequality fails.
  --
  -- The defect is exactly that `Q` is abstract: the hypotheses pin down the law of the
  -- *sample* under `Q n h` but say nothing about the rest of `Ω`, so a competitor is free to
  -- read `h` off directly.  Note that `Q n h ≪ Q n 0` does NOT repair it either (replace
  -- `δ_{h 0}` by `Unif[0, δₙ]` for `h ≠ 0` versus `Unif[0,1]` for `h = 0`, with `δₙ → 0`);
  -- what fails is not domination but the absence of any local-asymptotic-normality
  -- structure.  The minimal repair is therefore to restrict the competitors to tests based
  -- on the sample, which is `hφX` and is how the source states the theorem.
  --
  -- WHAT REMAINS for the repaired statement (RE-DERIVED this batch; the picture has changed
  -- substantially, because `asymptotic_maximin_upper_bound` is now CLOSED and was restated in
  -- exactly the shape this consumer needs).  Both obstructions recorded last batch are GONE:
  -- • The shell mismatch is gone: that lemma is now quantified over an arbitrary family `S n`
  --   of alternative sets subject only to `{h | ‖h‖ = b} ⊆ S n` *eventually*, which is
  --   precisely what `multinomialShell π b n` satisfies — the positivity constraint
  --   `πⱼ + hⱼ/√n ≥ 0` holds on the compact least-favourable sphere for all large `n`.
  -- • The abstract-`Q` obstruction is gone as data: the sample space of that lemma may now
  --   vary with `n`, so this consumer transfers along `hφX` to the CANONICAL experiment
  --   `Q'ₙ,h := ⨂_{i<n} multinomial(π + h/√n)` on `Fin n → Fin (k+1)`, where the log-likelihood
  --   field is explicit and `power (Q n) (φ n) h = power (Q'ₙ) (ψₙ) h` by `hφX` + `hcell` +
  --   `hindep` (the law of the sample is pinned down by the frozen hypotheses).
  -- What is left is therefore exactly the MULTINOMIAL LAN, on the canonical experiment:
  --   (a) the whitening reparametrisation `η = Σ^{-1/2} z` of the reduced coordinates
  --       `z = (h₁,…,h_k)`, under which `λ(h) = ∑ⱼ hⱼ²/πⱼ` becomes `‖η‖²`, so that the
  --       standardized form of the transfer lemma applies and `multinomialShell` becomes an
  --       `S n` containing the Euclidean sphere `‖η‖ = b`;
  --   (b) `Zₙ ⇒ N(0, Iₖ)` in the whitened coordinates — available up to the whitening from
  --       `ChiSquaredMultinomial.reducedCount_weakConverges_gaussian`, which gives
  --       `Zₙ ⇒ N(0, Σ)`;
  --   (c) the explicit log-likelihood `L n h ω = ∑_{i<n} log(1 + h_{ω i}/(√n π_{ω i}))`, its
  --       joint measurability (immediate, the sample space being discrete), and the
  --       expansion `L n h = ⟪η, Zₙ⟫ − ‖η‖²/2 + rₙ(h)` with `sup_{‖η‖=b} |rₙ| = o_P(1)` — a
  --       `log(1+u) = u − u²/2 + O(u³)` estimate that is uniform over the compact sphere
  --       because `π` is interior (`hπpos`) and `h` ranges over a bounded set, so
  --       `|h_j|/(√n π_j) → 0` uniformly. This last item is the only genuine analysis left,
  --       and it is a *finite-cell* computation, not a limit-theorem gap.
  -- The mixture–Neyman–Pearson apparatus itself is no longer a debt of this file.
  sorry

/-! ### (ii) Attainment by Pearson's test -/

/-- **The Pearson test attains the maximin value on the local shell** (LIFTED — the deep half
of `chiSquared_asymptotically_maximin`).  The minimum power of `1{Qₙ > c}` over
`multinomialShell π b n` converges to `P{χ²_k(b²) > c_{k,1−α}}`.

TODO (RE-DERIVED this batch).  This half is about Pearson's statistic, a function of the
sample alone, so it is untouched by the abstract-`Q` counterexample recorded at
`chiSquared_maximin_upper_bound`: the frozen hypotheses determine the law of
`pearsonQ π (X n)` under every `Q n h`, hence the whole statement.  It is TRUE and open.

The `limsup ≤` half is routine and needs nothing new: evaluate at a FIXED centred `h` with
`λ(h) = b²`, which lies in `multinomialShell π b n` for every large `n`, and use
`ChiSquaredMultinomial.pearsonQ_local_power_nondegenerate`, which is closed axiom-clean and
gives `power (Q n) 1{Qₙ > c} h → ncχ²_k(λ(h))(c, ∞)` together with `α < value < 1`.

What is genuinely left is the `liminf ≥` half, and it is *not* supplied by the mixture
apparatus closed this batch (`asymptotic_maximin_upper_bound` bounds every competitor from
ABOVE; attainment is a different statement).  The shell is unbounded and moves with `n`, so
the worst case is a *diagonal* sequence `hₙ ∈ multinomialShell π b n` with `λ(hₙ)` possibly
`→ ∞`, and bounding `power_n(hₙ)` from below along such a sequence is a uniform
(Berry–Esseen / tightness-over-the-shell) statement that no per-`h` weak limit supplies.
Two tools now shorten it but do not close it:
* the monotone likelihood ratio of `χ²_k(λ)` in `λ` (`exists_monotone_density`, in the MLR
  section below) pins the worst case at `λ = b²` *once* the family of local powers is known
  to be monotone in `λ` uniformly in `n`;
* `noncentralChiSquared_tail_mono` gives the corresponding limit statement.
The missing brick is a multinomial Berry–Esseen over the ellipsoids `{Qₙ > c}`, uniform in
the local parameter; the project has `ForMathlib/MultivariateBerryEsseen` only for slabs and
balls of a *fixed* law, not for a triangular array of drifting multinomial rows. -/
private lemma chiSquared_shell_minPower_tendsto {k : ℕ} {α b c : ℝ} {π : Fin (k + 1) → ℝ}
    {Q : ℕ → (Fin (k + 1) → ℝ) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → Fin (k + 1)}
    (hk : 0 < k) (hb : 0 < b) (hα : 0 < α) (hα1 : α < 1)
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1)
    (hX : ∀ n, ∀ i, Measurable (X n i))
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    (hcell : ∀ n h, ∀ i, ∀ j,
      ((Measure.map (X n i) (Q n h)) {j}).toReal = π j + h j / Real.sqrt (n : ℝ)) :
    Tendsto (fun n => sInf ((fun h => power (Q n)
          (fun ω => if c < pearsonQ π (X n) ω then (1 : ℝ) else 0) h)
        '' multinomialShell π b n)) atTop
        (nhds (((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal)) := by
  sorry

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
        -- REPAIRED: the competitors range over tests based on the sample; without this the
        -- second conjunct is FALSE, by the counterexample recorded at
        -- `chiSquared_maximin_upper_bound`
        (∀ n, ∃ ρ : (Fin n → Fin (k + 1)) → ℝ,
          Measurable ρ ∧ ∀ ω, ψ n ω = ρ (fun i => X n i ω)) →
        Tendsto (fun n => power (Q n) (ψ n) 0) atTop (nhds α) →
        limsup (fun n => sInf ((fun h => power (Q n) (ψ n) h)
            '' multinomialShell π b n)) atTop
          ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  refine ⟨?_, ?_⟩
  · -- Attainment on the shell: the deep uniform-over-the-shell half (lifted).
    exact chiSquared_shell_minPower_tendsto hk hb hα hα1 hc hπpos hπsum hX hindep hcell
  · -- Optimality: for any level-`α` sample-based test this is exactly the upper bound.
    intro ψ hψ hψX hlvl
    exact chiSquared_maximin_upper_bound hk hb hα hα1 hc hπpos hπsum hX hindep hcell hψ
      hψX hlvl

/-! ### Monotone likelihood ratio of the noncentral chi-squared family

The degrees-of-freedom monotonicity `noncentralTail_antitone` is a single-crossing
argument, and single crossing needs the *monotone likelihood ratio* of `χ²_k(λ)` in `λ`
— strictly more than the stochastic ordering supplied by `noncentralChiSquared_tail_mono`.
The classical routes to that MLR go through the Bessel density or the Poisson mixture
representation, neither of which the repository carries.  The development below obtains it
directly from the Gaussian definition instead: Cameron–Martin gives the likelihood ratio
`exp(⟪ν, z⟫ − ‖ν‖²/2)` of the shifted Gaussian, and — the test function `f(‖z‖²)` and the
standard Gaussian both being rotation invariant — that ratio may be replaced by its average
over the sphere `‖u‖ = ‖ν‖`, realised as the average over the *direction* of an independent
Gaussian vector.  The averaged ratio is a function of `‖z‖` alone and, after the reflection
`y ↦ −y` turns it into an average of `cosh`, is nondecreasing in `‖z‖`. -/

section MLR


/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_eucl_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Cameron–Martin shift for the standard Gaussian on `EuclideanSpace`.**  Shifting the
argument by `v` is the same as tilting by the exponential density
`exp(⟪v, z⟫ − ‖v‖²/2)`.  Transported from the `Measure.pi` form
`gaussianShift_change_of_measure` through `map_pi_eq_stdGaussian`. -/
private lemma integral_stdGaussian_shift {k : ℕ} (v : EuclideanSpace ℝ (Fin k))
    {F : EuclideanSpace ℝ (Fin k) → ℝ} (hF : Measurable F) :
    ∫ z, F (v + z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ z, F z * Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hTmeas : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  -- transport both sides to the `Measure.pi` picture
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinner : ∀ x : Fin k → ℝ,
      ⟪v, (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))⟫_ℝ = ∑ i, a i * x i := by
    intro x
    rw [hsum]
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hL : ∫ z, F (v + z) ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ x, F (v + WithLp.toLp 2 x) ∂π₀ := by
    rw [← hmapT, integral_map hTmeas.aemeasurable]
    exact (hF.comp (measurable_const_add v)).aestronglyMeasurable
  have hR : ∫ z, F z * Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ x, Real.exp ((∑ i, a i * x i) - (∑ i, (a i) ^ 2) / 2)
          * F (WithLp.toLp 2 x) ∂π₀ := by
    rw [← hmapT, integral_map hTmeas.aemeasurable]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [hinner x, hnorm]
      ring
    · exact (hF.mul (by fun_prop)).aestronglyMeasurable
  -- the shifted product Gaussian
  have hshift : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  have hmeasG : Measurable (fun x : Fin k → ℝ => F (WithLp.toLp 2 x)) := hF.comp hTmeas
  have hkey := gaussianShift_change_of_measure a (fun x : Fin k → ℝ => F (WithLp.toLp 2 x))
  rw [← hπ₀] at hkey
  have hstep : ∫ x, F (v + WithLp.toLp 2 x) ∂π₀
      = ∫ X, F (WithLp.toLp 2 X) ∂(Measure.pi fun i => gaussianReal (a i) 1) := by
    rw [← hshift, integral_map
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i))).aemeasurable
      hmeasG.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    congr 1
  rw [hL, hR, hstep, hkey]

/-- **1-D Gaussian Girsanov shift.**  (Same statement as the private
`ProbabilityTheory.gaussianReal_withDensity_exp_shift_1d`; repeated here because the
`Measure`-level form — not only its Bochner-integral consequence — is what the radial
argument below needs.) -/
private lemma gaussianReal_withDensity_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0),
    ← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  ext x
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Product-form Gaussian Girsanov shift** on `ι → ℝ`. -/
private lemma pi_gaussianReal_withDensity_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
        = gaussianReal (a i) 1 :=
    fun i => gaussianReal_withDensity_shift (a i)
  haveI : ∀ i : ι, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  have hdensity : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - (a i) ^ 2 / 2)) := by
    funext y
    rw [show ((∑ i, a i * y i) - (∑ i, (a i) ^ 2) / 2)
          = ∑ i, (a i * y i - (a i) ^ 2 / 2) from by
          rw [Finset.sum_sub_distrib, Finset.sum_div],
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hdensity, pi_withDensity_prod
    (f := fun i (x : ℝ) => ENNReal.ofReal (Real.exp (a i * x - (a i) ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- Transport of a `withDensity` through the (measurable-equivalence) coordinate map
`WithLp.toLp 2`. -/
private lemma map_toLp_withDensity {k : ℕ} (μ : Measure (Fin k → ℝ))
    {w : (Fin k → ℝ) → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k))
      = (μ.map (WithLp.toLp 2)).withDensity (fun z => w z.ofLp) := by
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hw' : Measurable (fun z : EuclideanSpace ℝ (Fin k) => w z.ofLp) :=
    hw.comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))
  ext A hA
  rw [Measure.map_apply hT hA, withDensity_apply _ (hT hA), withDensity_apply _ hA,
    ← lintegral_indicator (hT hA), ← lintegral_indicator hA,
    lintegral_map (hw'.indicator hA) hT]
  classical
  refine lintegral_congr fun x => ?_
  simp only [Set.indicator_apply, Set.mem_preimage]

/-- **Cameron–Martin identity, measure form.**  Translating the standard Gaussian on
`EuclideanSpace ℝ (Fin k)` by `v` is the same as tilting it by `exp(⟪v, ·⟫ − ‖v‖²/2)`. -/
private lemma stdGaussian_map_add_eq_withDensity {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).withDensity
          (fun z => ENNReal.ofReal (Real.exp (⟪v, z⟫_ℝ - ‖v‖ ^ 2 / 2))) := by
  classical
  set a : Fin k → ℝ := fun i => v i with ha
  set π₀ : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1) with hπ₀
  have hT : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  have hmapT : π₀.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
    map_pi_eq_stdGaussian
  have hsum : ∀ u w : EuclideanSpace ℝ (Fin k), ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
    intro u w
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hnorm : ‖v‖ ^ 2 = ∑ i, (a i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
  have hshiftpi : π₀.map (fun x i => a i + x i) = Measure.pi (fun i => gaussianReal (a i) 1) := by
    haveI : ∀ i : Fin k, SigmaFinite ((gaussianReal 0 1).map (fun t : ℝ => a i + t)) := by
      intro i
      rw [gaussianReal_map_const_add]
      infer_instance
    rw [hπ₀, Measure.pi_map_pi (f := fun i (t : ℝ) => a i + t)
      (fun i => (measurable_const_add (a i)).aemeasurable)]
    congr 1
    funext i
    rw [gaussianReal_map_const_add]
    simp
  -- left-hand side, transported to the product picture
  have hLHS : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => v + z)
      = (π₀.map (fun x i => a i + x i)).map (WithLp.toLp 2) := by
    rw [← hmapT, Measure.map_map (by fun_prop) hT,
      Measure.map_map hT
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).const_add (a i)))]
    congr 1
  rw [hLHS, hshiftpi, ← pi_gaussianReal_withDensity_shift a, ← hπ₀,
    map_toLp_withDensity π₀ (by fun_prop), hmapT]
  congr 1
  funext z
  rw [hsum, hnorm]


/-! ### Basic representations of the (non)central chi-squared laws -/

/-- The mean vector has length `√l`. -/
private lemma ncMean_norm {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ‖noncentralMean k l‖ = Real.sqrt (l : ℝ) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have h2 : ‖noncentralMean k l‖ ^ 2 = (l : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hval : ∀ i : Fin k,
        (noncentralMean k l i) ^ 2 = if i = 0 then (l : ℝ) else 0 := by
      intro i
      by_cases hi : i = 0
      · simp only [noncentralMean, hi, Fin.val_zero, if_pos, if_true]
        rw [Real.sq_sqrt l.coe_nonneg]
      · have hi' : (i : ℕ) ≠ 0 := by simpa [Fin.val_eq_zero_iff] using hi
        simp [noncentralMean, hi, hi']
    simp_rw [hval]
    simp [Finset.sum_ite_eq']
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- `multivariateGaussian v 1` is the translate of the standard Gaussian by `v`. -/
private lemma mvGaussian_one_eq_map {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) :
    multivariateGaussian v 1
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => v + x) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply]

/-- The noncentral chi-squared law as the squared-norm image of a shifted standard Gaussian. -/
private lemma ncChiSq_eq_map {k : ℕ} (l : ℝ≥0) :
    noncentralChiSquared k l
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map
          (fun z => ‖noncentralMean k l + z‖ ^ 2) := by
  rw [noncentralChiSquared, mvGaussian_one_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The central chi-squared law as the squared-norm image of the standard Gaussian. -/
private lemma chiSq_eq_map {k : ℕ} (hk : 0 < k) :
    StatLean.MultipleTesting.chiSquared k
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun z => ‖z‖ ^ 2) := by
  rw [← noncentralChiSquared_zero hk, ncChiSq_eq_map]
  congr 1
  funext z
  have hz : noncentralMean k (0 : ℝ≥0) = 0 := by ext i; simp [noncentralMean]
  rw [hz, zero_add]

/-- For `k ≥ 1` the standard Gaussian puts no mass at the origin. -/
private lemma stdGaussian_ne_zero_ae {k : ℕ} (hk : 0 < k) :
    ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ≠ 0 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have hzero : (stdGaussian (EuclideanSpace ℝ (Fin k))) {0} = 0 := by
    rw [← map_pi_eq_stdGaussian,
      Measure.map_apply (WithLp.measurable_toLp 2 (Fin k → ℝ)) (measurableSet_singleton _)]
    refine measure_mono_null (t := (fun x : Fin k → ℝ => x (0 : Fin k)) ⁻¹' {0}) ?_ ?_
    · intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [show x = (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)).ofLp from rfl, hx]
      rfl
    · rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
        Measure.pi_map_eval]
      haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
      simp
  have : ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))), z ∉ ({0} : Set _) := by
    rw [ae_iff]
    simpa using hzero
  filter_upwards [this] with z hz using by simpa using hz


/-! ### The monotone likelihood ratio of the noncentral chi-squared family -/

/-- **Monotone likelihood ratio in the noncentrality parameter.**  For `k ≥ 1` the noncentral
law `χ²_k(l)` has a density with respect to the central law `χ²_k` which is a *nondecreasing*
function of its argument.

The density is produced without any recourse to the Bessel series or to the Poisson mixture
representation: by Cameron–Martin the likelihood ratio of the shifted Gaussian is
`exp(⟪ν, z⟫ − ‖ν‖²/2)`, and, the integrand `f(‖z‖²)` and the standard Gaussian both being
rotation invariant, that ratio may be replaced by its average over the sphere `‖u‖ = ‖ν‖`
— realised here as the average over the *direction* `‖y‖⁻¹ • y` of an independent Gaussian
vector `y`.  The averaged ratio depends on `z` only through `‖z‖` and, after the reflection
`y ↦ −y` turns it into an average of `cosh`, is nondecreasing in `‖z‖`. -/
private lemma exists_monotone_density {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ x, 0 ≤ g x) ∧
      (0 < l → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → g x₁ < g x₂) ∧
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x ∂(noncentralChiSquared k l)
          = ∫⁻ x, f x * ENNReal.ofReal (g x)
              ∂(StatLean.MultipleTesting.chiSquared k) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  set γ : Measure (EuclideanSpace ℝ (Fin k)) := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set s : ℝ := Real.sqrt (l : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single (0 : Fin k) (1 : ℝ) with hedef
  have hene : ‖e‖ = 1 := by rw [hedef, EuclideanSpace.single, PiLp.norm_single, norm_one]
  set t : EuclideanSpace ℝ (Fin k) → ℝ := fun y => ‖y‖⁻¹ * ⟪y, e⟫_ℝ with htdef
  have htmeas : Measurable t := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_norm).inv
    · exact (continuous_id.inner continuous_const).measurable
  have htbd : ∀ y, |t y| ≤ 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [htdef]
    · have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      rw [htdef]
      simp only [abs_mul, abs_inv, abs_norm]
      rw [inv_mul_le_one₀ hy0]
      calc |⟪y, e⟫_ℝ| ≤ ‖y‖ * ‖e‖ := abs_real_inner_le_norm y e
        _ = ‖y‖ := by rw [hene, mul_one]
  -- the (bounded) one-parameter family of integrands
  have hexpmeas : ∀ c : ℝ,
      Measurable (fun y : EuclideanSpace ℝ (Fin k) => Real.exp (c * t y - (l : ℝ) / 2)) :=
    fun c => (Real.continuous_exp.measurable).comp
      ((measurable_const.mul htmeas).sub measurable_const)
  have hint : ∀ c : ℝ, Integrable (fun y => Real.exp (c * t y - (l : ℝ) / 2)) γ := by
    intro c
    refine (integrable_const (Real.exp (|c| - (l : ℝ) / 2))).mono'
      (hexpmeas c).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hbd : c * t y ≤ |c| := by
      calc c * t y ≤ |c * t y| := le_abs_self _
        _ = |c| * |t y| := abs_mul _ _
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left (htbd y) (abs_nonneg c)
        _ = |c| := mul_one _
    linarith
  have hcoshint : ∀ c : ℝ,
      Integrable (fun y => Real.cosh (c * t y) * Real.exp (-((l : ℝ) / 2))) γ := by
    intro c
    refine (integrable_const (Real.cosh |c| * Real.exp (-((l : ℝ) / 2)))).mono'
      (((Real.continuous_cosh.comp (by fun_prop : Continuous fun r : ℝ => c * r)).measurable.comp
        htmeas).mul measurable_const).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    rw [Real.cosh_le_cosh, abs_mul, abs_abs]
    calc |c| * |t y| ≤ |c| * 1 := mul_le_mul_of_nonneg_left (htbd y) (abs_nonneg c)
      _ = |c| := mul_one _
  -- the reflection `y ↦ -y` turns the exponential average into a `cosh` average
  have hneg : γ.map (fun y : EuclideanSpace ℝ (Fin k) => -y) = γ := by
    have h0 := stdGaussian_map
      (LinearIsometryEquiv.neg ℝ :
        EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    rw [hγ]
    convert h0 using 2
  have hcosh : ∀ c : ℝ,
      (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = ∫ y, Real.cosh (c * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ := by
    intro c
    have hty : ∀ y : EuclideanSpace ℝ (Fin k), t (-y) = -(t y) := by
      intro y
      simp only [htdef, norm_neg, inner_neg_left]
      ring
    have hmirror : (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ := by
      calc (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
          = ∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂(γ.map (fun y => -y)) := by rw [hneg]
        _ = ∫ y, Real.exp (c * t (-y) - (l : ℝ) / 2) ∂γ :=
            integral_map measurable_neg.aemeasurable
              (by rw [hneg]; exact (hexpmeas c).aestronglyMeasurable)
        _ = ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only []
            rw [hty y]
            ring_nf
    have hint₂ : Integrable (fun y => Real.exp (-(c * t y) - (l : ℝ) / 2)) γ := by
      have h := hint (-c)
      simpa only [neg_mul] using h
    have havg : (∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
        = (1 / 2) * ((∫ y, Real.exp (c * t y - (l : ℝ) / 2) ∂γ)
            + ∫ y, Real.exp (-(c * t y) - (l : ℝ) / 2) ∂γ) := by
      rw [← hmirror]; ring
    rw [havg, ← integral_add (hint c) hint₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [Real.cosh_eq, sub_eq_add_neg (c * t y), sub_eq_add_neg (-(c * t y)),
      Real.exp_add, Real.exp_add]
    ring
  -- the density
  set g : ℝ → ℝ := fun x => ∫ y, Real.exp (s * Real.sqrt x * t y - (l : ℝ) / 2) ∂γ with hgdef
  have hgmono : Monotone g := by
    intro x₁ x₂ hx
    have hc₁ : 0 ≤ s * Real.sqrt x₁ := by positivity
    have hc₂ : 0 ≤ s * Real.sqrt x₂ := by positivity
    rw [hgdef]
    simp only
    rw [hcosh _, hcosh _]
    refine integral_mono (hcoshint _) (hcoshint _) fun y => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul (s * Real.sqrt x₁), abs_mul (s * Real.sqrt x₂)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg hc₁, abs_of_nonneg hc₂]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) hs0
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    exact integral_nonneg fun y => (Real.exp_nonneg _)
  -- the direction functional is a.e. nonzero
  have htne : ∀ᵐ y ∂γ, t y ≠ 0 := by
    have hzero : γ {y : EuclideanSpace ℝ (Fin k) | ⟪y, e⟫_ℝ = 0} = 0 := by
      rw [hγ, ← map_pi_eq_stdGaussian,
        Measure.map_apply (WithLp.measurable_toLp 2 (Fin k → ℝ))
          (measurableSet_eq_fun (by fun_prop) measurable_const)]
      refine measure_mono_null (t := (fun x : Fin k → ℝ => x (0 : Fin k)) ⁻¹' {0}) ?_ ?_
      · intro x hx
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
        have hxe : ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)), e⟫_ℝ = x 0 := by
          rw [inner_eucl_sum, hedef]
          simp only [EuclideanSpace.single_apply]
          rw [Finset.sum_eq_single (0 : Fin k)]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hb
            exact absurd (Finset.mem_univ (0 : Fin k)) hb
        rw [← hxe]
        exact hx
      · rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
          Measure.pi_map_eval]
        haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
        simp
    have hsub : {y : EuclideanSpace ℝ (Fin k) | t y = 0}
        ⊆ {y : EuclideanSpace ℝ (Fin k) | ⟪y, e⟫_ℝ = 0} := by
      intro y hy
      simp only [Set.mem_setOf_eq, htdef] at hy ⊢
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · have h0 : (‖y‖ : ℝ)⁻¹ ≠ 0 := by
          simp [norm_ne_zero_iff.mpr hy0]
        exact (mul_eq_zero.mp hy).resolve_left h0
    rw [ae_iff]
    refine measure_mono_null ?_ hzero
    intro y hy
    exact hsub (by simpa using hy)
  have hgstrict : 0 < l → ∀ x₁ x₂ : ℝ, 0 ≤ x₁ → x₁ < x₂ → g x₁ < g x₂ := by
    intro hl x₁ x₂ hx₁ hx
    have hspos : 0 < s := by
      rw [hsdef]
      exact Real.sqrt_pos.mpr (by exact_mod_cast hl)
    have hlt : s * Real.sqrt x₁ < s * Real.sqrt x₂ :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hx₁ hx) hspos
    have hc₁ : 0 ≤ s * Real.sqrt x₁ := by positivity
    set F : EuclideanSpace ℝ (Fin k) → ℝ := fun y =>
      Real.cosh (s * Real.sqrt x₂ * t y) * Real.exp (-((l : ℝ) / 2))
        - Real.cosh (s * Real.sqrt x₁ * t y) * Real.exp (-((l : ℝ) / 2)) with hF
    have hFint : Integrable F γ := (hcoshint _).sub (hcoshint _)
    have hFpos : ∀ y, t y ≠ 0 → 0 < F y := by
      intro y hty
      have habs : |s * Real.sqrt x₁ * t y| < |s * Real.sqrt x₂ * t y| := by
        rw [abs_mul (s * Real.sqrt x₁), abs_mul (s * Real.sqrt x₂),
          abs_of_nonneg hc₁, abs_of_nonneg (by positivity : (0:ℝ) ≤ s * Real.sqrt x₂)]
        exact mul_lt_mul_of_pos_right hlt (abs_pos.mpr hty)
      have := Real.cosh_lt_cosh.mpr habs
      rw [hF]
      have hexp : 0 < Real.exp (-((l : ℝ) / 2)) := Real.exp_pos _
      simp only
      nlinarith
    have hFnn : 0 ≤ᵐ[γ] F := by
      filter_upwards [htne] with y hy using (hFpos y hy).le
    have hFne : ¬ (F =ᵐ[γ] 0) := by
      intro hcon
      have hfalse : ∀ᵐ y ∂γ, False := by
        filter_upwards [hcon, htne] with y hy hty
        have h1 : 0 < F y := hFpos y hty
        rw [show F y = (0 : EuclideanSpace ℝ (Fin k) → ℝ) y from hy] at h1
        exact lt_irrefl 0 h1
      haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
      have hz : γ Set.univ = 0 := by
        have h2 := ae_iff.mp hfalse
        simpa using h2
      rw [measure_univ] at hz
      exact one_ne_zero hz
    have hposint : 0 < ∫ y, F y ∂γ := by
      rcases (integral_nonneg_of_ae hFnn).lt_or_eq with hlt' | heq
      · exact hlt'
      · exact absurd ((integral_eq_zero_iff_of_nonneg_ae hFnn hFint).mp heq.symm) hFne
    have hsplit : (∫ y, F y ∂γ)
        = (∫ y, Real.cosh (s * Real.sqrt x₂ * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ)
          - ∫ y, Real.cosh (s * Real.sqrt x₁ * t y) * Real.exp (-((l : ℝ) / 2)) ∂γ :=
      integral_sub (hcoshint _) (hcoshint _)
    rw [hgdef]
    simp only
    rw [hcosh _, hcosh _]
    linarith [hsplit ▸ hposint]
  refine ⟨g, hgmono, hgnn, hgstrict, ?_⟩
  intro f hf
  set ν : EuclideanSpace ℝ (Fin k) := noncentralMean k l with hνdef
  have hνnorm : ‖ν‖ = s := ncMean_norm hk l
  have hνsq : ‖ν‖ ^ 2 = (l : ℝ) := by
    rw [hνnorm, hsdef, Real.sq_sqrt l.coe_nonneg]
  set H : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ := fun z => f (‖z‖ ^ 2) with hHdef
  have hHmeas : Measurable H := hf.comp (by fun_prop)
  -- the tilted integral as a function of the shift
  set J : EuclideanSpace ℝ (Fin k) → ℝ≥0∞ :=
    fun u => ∫⁻ z, H z * ENNReal.ofReal (Real.exp (⟪u, z⟫_ℝ - (l : ℝ) / 2)) ∂γ with hJdef
  have hJmeas : ∀ u : EuclideanSpace ℝ (Fin k),
      Measurable (fun z => H z * ENNReal.ofReal (Real.exp (⟪u, z⟫_ℝ - (l : ℝ) / 2))) := by
    intro u
    exact hHmeas.mul (by fun_prop)
  -- (a)+(b): Cameron–Martin
  have hab : ∫⁻ x, f x ∂(noncentralChiSquared k l) = J ν := by
    rw [ncChiSq_eq_map, lintegral_map hf (by fun_prop)]
    have h1 : ∫⁻ z, f (‖ν + z‖ ^ 2) ∂γ = ∫⁻ z, H z ∂(γ.map (fun z => ν + z)) := by
      rw [lintegral_map hHmeas (by fun_prop)]
    rw [h1, hγ, stdGaussian_map_add_eq_withDensity ν,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hHmeas]
    rw [hJdef]
    refine lintegral_congr fun z => ?_
    simp only [Pi.mul_apply, hνsq]
    ring
  -- rotation invariance of `J` on spheres
  have hrot : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = ‖ν‖ → J u = J ν := by
    intro u hu
    obtain ⟨φ, hφ⟩ : ∃ φ : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
        φ ν = u := ⟨_, Submodule.reflection_sub hu.symm⟩
    have hmapφ : γ.map (⇑φ) = γ := by rw [hγ]; exact stdGaussian_map φ
    rw [hJdef]
    simp only
    conv_lhs => rw [← hmapφ]
    rw [lintegral_map (hJmeas u) φ.continuous.measurable]
    refine lintegral_congr fun z => ?_
    have h1 : H (φ z) = H z := by rw [hHdef]; simp only [LinearIsometryEquiv.norm_map]
    have h2 : ⟪u, φ z⟫_ℝ = ⟪ν, z⟫_ℝ := by rw [← hφ]; exact φ.inner_map_map ν z
    rw [h1, h2]
  -- averaging over the direction of an independent Gaussian vector
  have hdir : ∀ᵐ y ∂γ, J (s • (‖y‖⁻¹ • y)) = J ν := by
    filter_upwards [hγ ▸ stdGaussian_ne_zero_ae hk] with y hy
    refine hrot _ ?_
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hyy : ‖(‖y‖⁻¹ • y : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hy0.ne']
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hyy, mul_one, hνnorm]
  have haverage : J ν = ∫⁻ y, J (s • (‖y‖⁻¹ • y)) ∂γ := by
    rw [lintegral_congr_ae hdir, lintegral_const]
    haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
    rw [measure_univ, mul_one]
  -- the inner average is a function of `‖z‖` alone
  have hinner : ∀ z : EuclideanSpace ℝ (Fin k),
      (∫⁻ y, ENNReal.ofReal
          (Real.exp (⟪s • (‖y‖⁻¹ • y), z⟫_ℝ - (l : ℝ) / 2)) ∂γ)
        = ENNReal.ofReal (g (‖z‖ ^ 2)) := by
    intro z
    have hzz : ‖(‖z‖ • e : EuclideanSpace ℝ (Fin k))‖ = ‖z‖ := by
      rw [norm_smul, hene, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    obtain ⟨φ, hφ⟩ : ∃ φ : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
        φ (‖z‖ • e) = z := ⟨_, Submodule.reflection_sub hzz⟩
    have hmapφ : γ.map (⇑φ) = γ := by rw [hγ]; exact stdGaussian_map φ
    have hmeas0 : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal
        (Real.exp (⟪s • (‖y‖⁻¹ • y), z⟫_ℝ - (l : ℝ) / 2))) := by
      fun_prop
    conv_lhs => rw [← hmapφ]
    rw [lintegral_map hmeas0 φ.continuous.measurable]
    have hpt : ∀ y : EuclideanSpace ℝ (Fin k),
        ⟪s • (‖φ y‖⁻¹ • φ y), z⟫_ℝ = s * Real.sqrt (‖z‖ ^ 2) * t y := by
      intro y
      rw [Real.sqrt_sq (norm_nonneg z)]
      rw [real_inner_smul_left, real_inner_smul_left, LinearIsometryEquiv.norm_map]
      have hin : ⟪φ y, z⟫_ℝ = ‖z‖ * ⟪y, e⟫_ℝ := by
        conv_lhs => rw [← hφ]
        rw [φ.inner_map_map, real_inner_smul_right]
      rw [hin, htdef]
      ring
    simp_rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _)
      (Filter.Eventually.of_forall fun y => Real.exp_nonneg _)]
  -- assemble
  rw [hab, haverage]
  have hswap : (∫⁻ y, J (s • (‖y‖⁻¹ • y)) ∂γ)
      = ∫⁻ z, H z * ENNReal.ofReal (g (‖z‖ ^ 2)) ∂γ := by
    rw [hJdef]
    simp only
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun z => ?_
      rw [lintegral_const_mul _ (by fun_prop), hinner z]
    · refine (Measurable.aemeasurable ?_)
      exact (hHmeas.comp measurable_snd).mul (by fun_prop)
  have hfinal : ∫⁻ x, f x * ENNReal.ofReal (g x) ∂(StatLean.MultipleTesting.chiSquared k)
      = ∫⁻ z, H z * ENNReal.ofReal (g (‖z‖ ^ 2)) ∂γ := by
    rw [chiSq_eq_map hk, ← hγ]
    exact lintegral_map (hf.mul (ENNReal.measurable_ofReal.comp hgmono.measurable))
      (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin k) => ‖z‖ ^ 2)
  rw [hswap, hfinal]


/-! ### Additivity in the degrees of freedom -/

/-- The noncentral chi-squared law in the product picture, for an arbitrary mean vector of
the prescribed length. -/
private lemma ncChiSq_eq_pi_map {k : ℕ} (l : ℝ≥0) {w : Fin k → ℝ}
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (l : ℝ)) :
    noncentralChiSquared k l
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, (w i + x i) ^ 2) := by
  rw [← map_normSq_multivariateGaussian_of_norm_eq k l hw, mvGaussian_one_eq_map,
    ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- `χ²₁` is the law of the square of a standard normal variable. -/
private lemma chiSq_one_eq_map :
    StatLean.MultipleTesting.chiSquared 1 = (gaussianReal 0 1).map (fun u : ℝ => u ^ 2) := by
  have hw0 : ‖(WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) : EuclideanSpace ℝ (Fin 1))‖
      = Real.sqrt (((0 : ℝ≥0) : ℝ)) := by
    have hz : (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) : EuclideanSpace ℝ (Fin 1)) = 0 := by
      ext i; rfl
    rw [hz, norm_zero, NNReal.coe_zero, Real.sqrt_zero]
  have h := ncChiSq_eq_pi_map (k := 1) (l := 0) (w := fun _ => 0) hw0
  rw [noncentralChiSquared_zero one_pos] at h
  rw [h, show (fun x : Fin 1 → ℝ => ∑ i, ((0 : ℝ) + x i) ^ 2)
        = (fun u : ℝ => u ^ 2) ∘ (fun x : Fin 1 → ℝ => x 0) from by funext x; simp,
    ← Measure.map_map (by fun_prop) (by fun_prop), Measure.pi_map_eval]
  simp

/-- **Additivity of the noncentral chi-squared law in the degrees of freedom.**  `χ²_{k+1}(l)`
is the law of the sum of two independent variables, `χ²_k(l)` and `χ²₁`.  Because the
noncentrality is a complete invariant (`map_normSq_multivariateGaussian_of_norm_eq`) the mean
vector may be taken orthogonal to the split-off coordinate, which is what makes the split
carry all of the noncentrality into the `k`-dimensional factor. -/
private lemma ncChiSq_succ_eq_prod_map {k : ℕ} (hk : 0 < k) (l : ℝ≥0) :
    noncentralChiSquared (k + 1) l
      = ((noncentralChiSquared k l).prod (StatLean.MultipleTesting.chiSquared 1)).map
          (fun q : ℝ × ℝ => q.1 + q.2) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  set m : Fin k → ℝ := fun j => (noncentralMean k l) j with hm
  have hmnorm : ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k))‖ = Real.sqrt (l : ℝ) :=
    ncMean_norm hk l
  have hvnorm :
      ‖(WithLp.toLp 2 (Fin.cons (0 : ℝ) m) : EuclideanSpace ℝ (Fin (k + 1)))‖
        = Real.sqrt (l : ℝ) := by
    have h1 : ‖(WithLp.toLp 2 (Fin.cons (0 : ℝ) m) : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2
        = ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      simp
    rw [← Real.sqrt_sq (norm_nonneg _), h1, hmnorm, Real.sqrt_sq (Real.sqrt_nonneg _)]
  set Qk : (Fin k → ℝ) → ℝ := fun y => ∑ j, (m j + y j) ^ 2 with hQk
  have hQkmeas : Measurable Qk := by
    refine Finset.univ.measurable_sum fun j _ => ?_
    exact (((measurable_pi_apply j : Measurable fun y : Fin k → ℝ => y j)).const_add
      (m j)).pow_const 2
  have hsqmeas : Measurable (fun u : ℝ => u ^ 2) := by fun_prop
  -- the split of the product Gaussian at the first coordinate
  have mp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => gaussianReal 0 1) (0 : Fin (k + 1))
  have hsym := mp.symm.map_eq
  have hQ : ∀ p : ℝ × (Fin k → ℝ),
      (∑ i, ((Fin.cons (0 : ℝ) m : Fin (k + 1) → ℝ) i + (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0).symm p i) ^ 2) = Qk p.2 + p.1 ^ 2 := by
    intro p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_zero]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, zero_add, hQk, Fin.zero_succAbove, cast_eq]
    ring
  have hsplit : noncentralChiSquared (k + 1) l
      = ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)).map
          (fun p => Qk p.2 + p.1 ^ 2) := by
    rw [ncChiSq_eq_pi_map (l := l) (w := Fin.cons (0 : ℝ) m) hvnorm, ← hsym,
      Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
    congr 1
    funext p
    simpa only [Function.comp_apply] using hQ p
  -- rearrange the product
  have hswap : ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)).map
        (fun p => Qk p.2 + p.1 ^ 2)
      = (((Measure.pi fun _ : Fin k => gaussianReal 0 1).map Qk).prod
          ((gaussianReal 0 1).map (fun u : ℝ => u ^ 2))).map (fun q : ℝ × ℝ => q.1 + q.2) := by
    rw [Measure.map_prod_map _ _ hQkmeas hsqmeas,
      Measure.map_map (by fun_prop) (hQkmeas.prodMap hsqmeas),
      ← Measure.prod_swap (μ := gaussianReal 0 1)
        (ν := Measure.pi fun _ : Fin k => gaussianReal 0 1),
      Measure.map_map (by fun_prop) measurable_swap]
    rfl
  rw [hsplit, hswap, ← ncChiSq_eq_pi_map (l := l) (w := m) hmnorm, ← chiSq_one_eq_map]

/-- **Tail form of the additivity.**  The `χ²_{k+1}(l)` upper tail is the `χ²_k(l)`-average of
the `χ²₁` upper tail at the shifted threshold. -/
private lemma ncChiSq_succ_Ioi {k : ℕ} (hk : 0 < k) (l : ℝ≥0) (c : ℝ) :
    noncentralChiSquared (k + 1) l (Set.Ioi c)
      = ∫⁻ x, StatLean.MultipleTesting.chiSquared 1 (Set.Ioi (c - x))
          ∂(noncentralChiSquared k l) := by
  rw [ncChiSq_succ_eq_prod_map hk l,
    Measure.map_apply (by fun_prop) measurableSet_Ioi,
    Measure.prod_apply ((measurable_fst.add measurable_snd) measurableSet_Ioi)]
  refine lintegral_congr fun x => ?_
  congr 1
  ext u
  simp only [Set.mem_preimage, Set.mem_Ioi]
  constructor <;> intro h <;> linarith


/-! ### One extra degree of freedom costs power -/

/-- **One-step degrees-of-freedom monotonicity.**  If the critical values `c₁` (for `k`) and
`c₂` (for `k+1`) are matched at the null, then the noncentral tail at `k+1` degrees of
freedom never exceeds the one at `k`.

The proof is the single-crossing argument: writing `q(x) = χ²₁(c₂ − x, ∞)` for the
conditional rejection probability of the `(k+1)`-dimensional test given the first `k`
coordinates, the difference `1_{(c₁,∞)} − q` is `≤ 0` below `c₁` and `≥ 0` above it, while
`χ²_k(l)` has a *nondecreasing* density `g` with respect to `χ²_k`
(`exists_monotone_density`); the pointwise inequality
`q·g + 1_{(c₁,∞)}·g(c₁) ≤ 1_{(c₁,∞)}·g + q·g(c₁)` then integrates to the claim, the two
`g(c₁)`-terms cancelling because the levels are matched. -/
private lemma ncChiSq_tail_succ_le {k : ℕ} (hk : 0 < k) (l : ℝ≥0) {c₁ c₂ : ℝ}
    (hlevel : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁)
      = StatLean.MultipleTesting.chiSquared (k + 1) (Set.Ioi c₂)) :
    noncentralChiSquared (k + 1) l (Set.Ioi c₂) ≤ noncentralChiSquared k l (Set.Ioi c₁) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨g, hgmono, hgnn, hgstrict, hg⟩ := exists_monotone_density hk l
  set μ : Measure ℝ := StatLean.MultipleTesting.chiSquared k with hμ
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x) with hG
  set A : ℝ≥0∞ := G c₁ with hA
  set P : ℝ → ℝ≥0∞ := Set.indicator (Set.Ioi c₁) 1 with hP
  set Q : ℝ → ℝ≥0∞ :=
    fun x => StatLean.MultipleTesting.chiSquared 1 (Set.Ioi (c₂ - x)) with hQ
  have hGmeas : Measurable G := ENNReal.measurable_ofReal.comp hgmono.measurable
  have hPmeas : Measurable P := (measurable_const : Measurable (1 : ℝ → ℝ≥0∞)).indicator
    measurableSet_Ioi
  have hQmeas : Measurable Q := by
    have hs : MeasurableSet ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂)) :=
      (measurable_fst.add measurable_snd) measurableSet_Ioi
    have heq : Q = fun x : ℝ => StatLean.MultipleTesting.chiSquared 1
        (Prod.mk x ⁻¹' ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂))) := by
      funext x
      simp only [hQ]
      congr 1
      ext u
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact measurable_measure_prodMk_left (ν := StatLean.MultipleTesting.chiSquared 1) hs
  have hQle : ∀ x, Q x ≤ 1 := fun x => prob_le_one
  -- the two tails as `χ²_k`-integrals of the density
  have hAval : noncentralChiSquared k l (Set.Ioi c₁) = ∫⁻ x, P x * G x ∂μ := by
    rw [← hg P hPmeas, hP, lintegral_indicator_one measurableSet_Ioi]
  have hBval : noncentralChiSquared (k + 1) l (Set.Ioi c₂) = ∫⁻ x, Q x * G x ∂μ := by
    rw [ncChiSq_succ_Ioi hk l c₂, ← hg Q hQmeas]
  -- the matched levels
  have hlev1 : ∫⁻ x, P x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    rw [hP, lintegral_indicator_one measurableSet_Ioi]
  have hlev2 : ∫⁻ x, Q x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    have h0 := ncChiSq_succ_Ioi hk (0 : ℝ≥0) c₂
    rw [noncentralChiSquared_zero hk, noncentralChiSquared_zero (by omega : 0 < k + 1)] at h0
    rw [hμ, ← h0, hlevel]
  -- the single-crossing pointwise inequality
  have hpt : ∀ x, Q x * G x + P x * A ≤ P x * G x + Q x * A := by
    intro x
    by_cases hx : x ∈ Set.Ioi c₁
    · have hAG : A ≤ G x := by
        refine ENNReal.ofReal_le_ofReal (hgmono ?_)
        exact le_of_lt hx
      obtain ⟨d, hd⟩ := exists_add_of_le hAG
      have hPx : P x = 1 := by rw [hP, Set.indicator_of_mem hx]; rfl
      rw [hPx, hd, one_mul, one_mul]
      have hQd : Q x * d ≤ d := by
        calc Q x * d ≤ 1 * d := mul_le_mul_right' (hQle x) d
          _ = d := one_mul d
      calc Q x * (A + d) + A = (Q x * A + A) + Q x * d := by ring
        _ ≤ (Q x * A + A) + d := by gcongr
        _ = A + d + Q x * A := by ring
    · have hGA : G x ≤ A := by
        refine ENNReal.ofReal_le_ofReal (hgmono ?_)
        simpa using hx
      have hPx : P x = 0 := by rw [hP, Set.indicator_of_notMem hx]
      rw [hPx, zero_mul, zero_mul, add_zero, zero_add]
      exact mul_le_mul_left' hGA _
  -- integrate and cancel the common finite term
  have hmain : (∫⁻ x, Q x * G x ∂μ) + (∫⁻ x, P x ∂μ) * A
      ≤ (∫⁻ x, P x * G x ∂μ) + (∫⁻ x, Q x ∂μ) * A := by
    rw [← lintegral_mul_const _ hPmeas, ← lintegral_mul_const _ hQmeas,
      ← lintegral_add_left (hQmeas.mul hGmeas), ← lintegral_add_left (hPmeas.mul hGmeas)]
    exact lintegral_mono hpt
  rw [hlev1, hlev2] at hmain
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfin : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A ≠ ⊤ := by
    refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
    rw [hA, hG]
    exact ENNReal.ofReal_ne_top
  rw [hAval, hBval]
  exact (ENNReal.add_le_add_iff_right hfin).mp hmain


/-! ### Support facts for the central chi-squared law -/

/-- `χ²_k` charges every interval of positive length inside the positive half-line. -/
private lemma chiSq_Ioo_pos {k : ℕ} (hk : 0 < k) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < StatLean.MultipleTesting.chiSquared k (Set.Ioo a b) := by
  have hkpos : (0 : ℝ) < (k : ℝ) / 2 := by positivity
  have hpdfpos : ∀ x ∈ Set.Ioo a b, 0 < gammaPDF ((k : ℝ) / 2) (1 / 2) x := by
    intro x hx
    rw [gammaPDF]
    exact ENNReal.ofReal_pos.mpr (gammaPDFReal_pos hkpos (by norm_num) (by linarith [hx.1]))
  rw [StatLean.MultipleTesting.chiSquared, gammaMeasure, withDensity_apply _ measurableSet_Ioo,
    pos_iff_ne_zero]
  intro hz
  have hmpdf : Measurable (gammaPDF ((k : ℝ) / 2) (1 / 2)) := fun t ht =>
    (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal ((k : ℝ) / 2) (1 / 2))) ht
  rw [lintegral_eq_zero_iff hmpdf] at hz
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioo a b →
      gammaPDF ((k : ℝ) / 2) (1 / 2) x = 0 := (ae_restrict_iff' measurableSet_Ioo).mp hz
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioo a b := by
    filter_upwards [hae] with x hx hmem
    exact (hpdfpos x hmem).ne' (hx hmem)
  have h3 := ae_iff.mp h2
  simp only [not_not, Set.setOf_mem_eq, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h3
  linarith

/-- The `χ²₁` upper tail is positive at every threshold. -/
private lemma chiSq_one_Ioi_pos (u : ℝ) :
    0 < StatLean.MultipleTesting.chiSquared 1 (Set.Ioi u) := by
  refine lt_of_lt_of_le (chiSq_Ioo_pos (k := 1) one_pos
    (a := max u 0 + 1) (b := max u 0 + 2) (by positivity) (by linarith)) (measure_mono ?_)
  intro x hx
  have := hx.1
  have hmax : u ≤ max u 0 := le_max_left _ _
  simp only [Set.mem_Ioi]
  linarith

/-- `χ²_k` puts no mass on the nonpositive half-line, so the `1 − α` critical value is
positive whenever `α < 1`. -/
private lemma chiSq_crit_pos {k : ℕ} (hk : 0 < k) {α c₀ : ℝ} (hα1 : α < 1)
    (hc : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₀) = ENNReal.ofReal α) :
    0 < c₀ := by
  haveI : NeZero k := ⟨hk.ne'⟩
  by_contra hcon
  push_neg at hcon
  have hac : StatLean.MultipleTesting.chiSquared k (Set.Iic 0) = 0 := by
    have hIio : StatLean.MultipleTesting.chiSquared k (Set.Iio 0) = 0 := by
      rw [StatLean.MultipleTesting.chiSquared, gammaMeasure,
        withDensity_apply _ measurableSet_Iio]
      exact lintegral_gammaPDF_of_nonpos le_rfl
    have hsing : StatLean.MultipleTesting.chiSquared k ({0} : Set ℝ) = 0 := by
      rw [StatLean.MultipleTesting.chiSquared, gammaMeasure]
      exact withDensity_absolutelyContinuous volume _ (by simp)
    have hsub : (Set.Iic (0 : ℝ)) ⊆ Set.Iio 0 ∪ {0} := by
      intro x hx
      rcases lt_or_eq_of_le (Set.mem_Iic.mp hx) with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine le_antisymm ?_ (zero_le _)
    calc StatLean.MultipleTesting.chiSquared k (Set.Iic 0)
        ≤ StatLean.MultipleTesting.chiSquared k (Set.Iio 0 ∪ {0}) := measure_mono hsub
      _ ≤ StatLean.MultipleTesting.chiSquared k (Set.Iio 0)
          + StatLean.MultipleTesting.chiSquared k ({0} : Set ℝ) := measure_union_le _ _
      _ = 0 := by rw [hIio, hsing, add_zero]
  have hfull : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₀) = 1 := by
    have hcompl : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₀)
        = 1 - StatLean.MultipleTesting.chiSquared k (Set.Iic c₀) := by
      rw [← measure_univ (μ := StatLean.MultipleTesting.chiSquared k),
        ← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _)]
    have hle : StatLean.MultipleTesting.chiSquared k (Set.Iic c₀) = 0 :=
      le_antisymm (hac ▸ measure_mono (Set.Iic_subset_Iic.mpr hcon)) (zero_le _)
    rw [hcompl, hle, tsub_zero]
  rw [hfull] at hc
  have : (1 : ℝ≥0∞) < 1 := by
    calc (1 : ℝ≥0∞) = ENNReal.ofReal α := hc
      _ < 1 := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr hα1
  exact lt_irrefl _ this


/-- **Strict one-step degrees-of-freedom monotonicity.**  For a *positive* noncentrality the
inequality of `ncChiSq_tail_succ_le` is strict: on any interval strictly inside `(0, c₁)` the
`(k+1)`-dimensional test still rejects with positive probability while the `k`-dimensional
one does not, and there the monotone density is *strictly* below its value at `c₁`. -/
private lemma ncChiSq_tail_succ_lt {k : ℕ} (hk : 0 < k) {l : ℝ≥0} (hl : 0 < l) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hlevel : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁)
      = StatLean.MultipleTesting.chiSquared (k + 1) (Set.Ioi c₂)) :
    noncentralChiSquared (k + 1) l (Set.Ioi c₂) < noncentralChiSquared k l (Set.Ioi c₁) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨g, hgmono, hgnn, hgstrict, hg⟩ := exists_monotone_density hk l
  set μ : Measure ℝ := StatLean.MultipleTesting.chiSquared k with hμ
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x) with hG
  set A : ℝ≥0∞ := G c₁ with hA
  set P : ℝ → ℝ≥0∞ := Set.indicator (Set.Ioi c₁) 1 with hP
  set Q : ℝ → ℝ≥0∞ :=
    fun x => StatLean.MultipleTesting.chiSquared 1 (Set.Ioi (c₂ - x)) with hQ
  have hGmeas : Measurable G := ENNReal.measurable_ofReal.comp hgmono.measurable
  have hPmeas : Measurable P :=
    (measurable_const : Measurable (1 : ℝ → ℝ≥0∞)).indicator measurableSet_Ioi
  have hQmeas : Measurable Q := by
    have hs : MeasurableSet ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂)) :=
      (measurable_fst.add measurable_snd) measurableSet_Ioi
    have heq : Q = fun x : ℝ => StatLean.MultipleTesting.chiSquared 1
        (Prod.mk x ⁻¹' ((fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' (Set.Ioi c₂))) := by
      funext x
      simp only [hQ]
      congr 1
      ext u
      simp only [Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact measurable_measure_prodMk_left (ν := StatLean.MultipleTesting.chiSquared 1) hs
  have hQle : ∀ x, Q x ≤ 1 := fun x => prob_le_one
  have hAval : noncentralChiSquared k l (Set.Ioi c₁) = ∫⁻ x, P x * G x ∂μ := by
    rw [← hg P hPmeas, hP, lintegral_indicator_one measurableSet_Ioi]
  have hBval : noncentralChiSquared (k + 1) l (Set.Ioi c₂) = ∫⁻ x, Q x * G x ∂μ := by
    rw [ncChiSq_succ_Ioi hk l c₂, ← hg Q hQmeas]
  have hlev1 : ∫⁻ x, P x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    rw [hP, lintegral_indicator_one measurableSet_Ioi]
  have hlev2 : ∫⁻ x, Q x ∂μ = StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) := by
    have h0 := ncChiSq_succ_Ioi hk (0 : ℝ≥0) c₂
    rw [noncentralChiSquared_zero hk, noncentralChiSquared_zero (by omega : 0 < k + 1)] at h0
    rw [hμ, ← h0, hlevel]
  -- the strict gap on an interval below the critical value
  set I : Set ℝ := Set.Ioo (c₁ / 3) (c₁ / 2) with hI
  have hIpos : 0 < μ I := chiSq_Ioo_pos hk (by linarith) (by linarith)
  have hghalf : g (c₁ / 2) < g c₁ := hgstrict hl _ _ (by linarith) (by linarith)
  have hAhalf : G (c₁ / 2) < A := by
    rw [hG, hA, hG]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (hgnn _) hghalf)).mpr hghalf
  obtain ⟨dg, hdg⟩ := exists_add_of_le hAhalf.le
  have hdgne : dg ≠ 0 := by
    intro h
    rw [h, add_zero] at hdg
    exact hAhalf.ne hdg.symm
  set δ : ℝ≥0∞ := Q (c₁ / 3) * dg with hδ
  have hδne : δ ≠ 0 := by
    rw [hδ]
    exact mul_ne_zero (chiSq_one_Ioi_pos _).ne' hdgne
  have hpt : ∀ x, Q x * G x + P x * A + I.indicator (fun _ => δ) x ≤ P x * G x + Q x * A := by
    intro x
    by_cases hxI : x ∈ I
    · rw [Set.indicator_of_mem hxI]
      have hx2 : x < c₁ / 2 := hxI.2
      have hx1 : c₁ / 3 < x := hxI.1
      have hPx : P x = 0 := by
        rw [hP, Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith)]
      have hGle : G x ≤ G (c₁ / 2) := ENNReal.ofReal_le_ofReal (hgmono hx2.le)
      have hQge : Q (c₁ / 3) ≤ Q x :=
        measure_mono (Set.Ioi_subset_Ioi (by linarith))
      rw [hPx, zero_mul, zero_mul, add_zero, zero_add]
      calc Q x * G x + δ
          ≤ Q x * G (c₁ / 2) + Q x * dg :=
            add_le_add (mul_le_mul_left' hGle _) (mul_le_mul_right' hQge dg)
        _ = Q x * (G (c₁ / 2) + dg) := by ring
        _ = Q x * A := by rw [← hdg]
    · rw [Set.indicator_of_notMem hxI, add_zero]
      by_cases hx : x ∈ Set.Ioi c₁
      · have hAG : A ≤ G x := ENNReal.ofReal_le_ofReal (hgmono (le_of_lt hx))
        obtain ⟨d, hd⟩ := exists_add_of_le hAG
        have hPx : P x = 1 := by rw [hP, Set.indicator_of_mem hx]; rfl
        rw [hPx, hd, one_mul, one_mul]
        have hQd : Q x * d ≤ d := by
          calc Q x * d ≤ 1 * d := mul_le_mul_right' (hQle x) d
            _ = d := one_mul d
        calc Q x * (A + d) + A = (Q x * A + A) + Q x * d := by ring
          _ ≤ (Q x * A + A) + d := by gcongr
          _ = A + d + Q x * A := by ring
      · have hGA : G x ≤ A := by
          refine ENNReal.ofReal_le_ofReal (hgmono ?_)
          simpa using hx
        have hPx : P x = 0 := by rw [hP, Set.indicator_of_notMem hx]
        rw [hPx, zero_mul, zero_mul, add_zero, zero_add]
        exact mul_le_mul_left' hGA _
  have hmain : ∫⁻ x, (Q x * G x + P x * A + I.indicator (fun _ => δ) x) ∂μ
      ≤ ∫⁻ x, (P x * G x + Q x * A) ∂μ := lintegral_mono hpt
  rw [lintegral_add_left ((hQmeas.mul hGmeas).add (hPmeas.mul measurable_const)),
    lintegral_add_left (hQmeas.mul hGmeas), lintegral_add_left (hPmeas.mul hGmeas),
    lintegral_indicator_const measurableSet_Ioo,
    lintegral_mul_const _ hPmeas, lintegral_mul_const _ hQmeas, hlev1, hlev2] at hmain
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hfin : StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (by rw [hA, hG]; exact ENNReal.ofReal_ne_top)
  have hrearr : ((∫⁻ x, Q x * G x ∂μ) + δ * μ I)
      + StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A
      ≤ (∫⁻ x, P x * G x ∂μ) + StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A := by
    calc ((∫⁻ x, Q x * G x ∂μ) + δ * μ I)
          + StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A
        = (∫⁻ x, Q x * G x ∂μ)
            + StatLean.MultipleTesting.chiSquared k (Set.Ioi c₁) * A + δ * μ I := by ring
      _ ≤ _ := hmain
  have hcancel : (∫⁻ x, Q x * G x ∂μ) + δ * μ I ≤ ∫⁻ x, P x * G x ∂μ :=
    (ENNReal.add_le_add_iff_right hfin).mp hrearr
  rw [hAval, hBval]
  refine lt_of_lt_of_le ?_ hcancel
  refine ENNReal.lt_add_right ?_ (by simp [hδne, hIpos.ne'])
  rw [← hBval]
  exact measure_ne_top _ _


/-- **Degrees-of-freedom monotonicity of the noncentral tail, chained.**  With critical
values matched at the common level `α < 1`, the noncentral chi-squared tail is nonincreasing
in the number of degrees of freedom, strictly so as soon as the noncentrality is positive. -/
private lemma ncChiSq_tail_antitone_df {α : ℝ} {c : ℕ → ℝ} (hα1 : α < 1)
    (hc : ∀ k, 0 < k → StatLean.MultipleTesting.chiSquared k (Set.Ioi (c k))
      = ENNReal.ofReal α) (l : ℝ≥0) :
    (∀ k₁ k₂ : ℕ, 0 < k₁ → k₁ ≤ k₂ →
        noncentralChiSquared k₂ l (Set.Ioi (c k₂))
          ≤ noncentralChiSquared k₁ l (Set.Ioi (c k₁)))
      ∧ (0 < l → ∀ k₁ k₂ : ℕ, 0 < k₁ → k₁ < k₂ →
          noncentralChiSquared k₂ l (Set.Ioi (c k₂))
            < noncentralChiSquared k₁ l (Set.Ioi (c k₁))) := by
  have hlevel : ∀ k, 0 < k →
      StatLean.MultipleTesting.chiSquared k (Set.Ioi (c k))
        = StatLean.MultipleTesting.chiSquared (k + 1) (Set.Ioi (c (k + 1))) := by
    intro k hk
    rw [hc k hk, hc (k + 1) (by omega)]
  have hmono : ∀ k₁ d : ℕ, 0 < k₁ →
      noncentralChiSquared (k₁ + d) l (Set.Ioi (c (k₁ + d)))
        ≤ noncentralChiSquared k₁ l (Set.Ioi (c k₁)) := by
    intro k₁ d hk₁
    induction d with
    | zero => simp
    | succ d ih =>
        refine le_trans ?_ ih
        have hkd : 0 < k₁ + d := by omega
        have hstep := ncChiSq_tail_succ_le hkd l (hlevel (k₁ + d) hkd)
        rw [show k₁ + (d + 1) = (k₁ + d) + 1 from by omega]
        exact hstep
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk₁ hle
    obtain ⟨d, rfl⟩ : ∃ d, k₂ = k₁ + d := ⟨k₂ - k₁, by omega⟩
    exact hmono k₁ d hk₁
  · intro hl k₁ k₂ hk₁ hlt
    have hstep : noncentralChiSquared (k₁ + 1) l (Set.Ioi (c (k₁ + 1)))
        < noncentralChiSquared k₁ l (Set.Ioi (c k₁)) :=
      ncChiSq_tail_succ_lt hk₁ hl (chiSq_crit_pos hk₁ hα1 (hc k₁ hk₁)) (hlevel k₁ hk₁)
    obtain ⟨d, rfl⟩ : ∃ d, k₂ = (k₁ + 1) + d := ⟨k₂ - (k₁ + 1), by omega⟩
    exact lt_of_le_of_lt (hmono (k₁ + 1) d (by omega)) hstep

end MLR

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
  -- Proof (single crossing + monotone likelihood ratio).  Reduce to one extra degree of
  -- freedom: with `χ²_{k+1}(λ) = χ²_k(λ) ⋆ χ²₁` (`ncChiSq_succ_eq_prod_map`, the mean vector
  -- being taken orthogonal to the split-off coordinate) the two powers are the `χ²_k(λ)`-
  -- integrals of `1_{(c_k,∞)}` and of `x ↦ χ²₁(c_{k+1} − x, ∞)`, whose difference is single
  -- crossing at `c_k` with matched null means.  The MLR of the family in the noncentrality
  -- (`exists_monotone_density`) then gives the one-step inequality `ncChiSq_tail_succ_le`,
  -- strict for `λ > 0` (`ncChiSq_tail_succ_lt`); `ncChiSq_tail_antitone_df` chains it.
  simp only [noncentralTail]
  obtain ⟨hmono, hstrict⟩ := ncChiSq_tail_antitone_df hα1 hc (h ^ 2).toNNReal
  refine ⟨fun k₁ k₂ hk₁ hle => ?_, fun hh k₁ k₂ hk₁ hlt => ?_⟩
  · exact ENNReal.toReal_mono (measure_ne_top _ _) (hmono k₁ k₂ hk₁ hle)
  · have hlpos : 0 < (h ^ 2).toNNReal :=
      Real.toNNReal_pos.mpr (by positivity)
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (hstrict hlpos k₁ k₂ hk₁ hlt)

/-! ### Private assembly infrastructure for the large-`k` tail limits -/

/-- **Moving-threshold portmanteau tail.** If probability measures `μs k` on `ℝ` converge
weakly to an *atomless* limit `ν` and the thresholds `tk k` converge to `t`, then the upper
tails converge: `μs k (t_k, ∞) → ν (t, ∞)`.

Squeeze between the open sets `(t + εₘ, ∞)` and the closed sets `[t − εₘ, ∞)` with
`εₘ = 1/(m+1) ↓ 0`, using the open/closed portmanteau inequalities. -/
private lemma tendsto_measure_Ioi_of_weakLimit
    {μs : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    [NoAtoms (ν : Measure ℝ)]
    (hconv : Tendsto μs atTop (𝓝 ν))
    {t : ℝ} {tk : ℕ → ℝ} (htk : Tendsto tk atTop (𝓝 t)) :
    Tendsto (fun k => (μs k : Measure ℝ) (Set.Ioi (tk k))) atTop
      (𝓝 ((ν : Measure ℝ) (Set.Ioi t))) := by
  set a : ℕ → ℝ≥0∞ := fun k => (μs k : Measure ℝ) (Set.Ioi (tk k)) with ha
  -- Lower bound: `ν(t, ∞) ≤ liminf a`.
  have hlow : (ν : Measure ℝ) (Set.Ioi t) ≤ liminf a atTop := by
    set G : ℕ → Set ℝ := fun m => Set.Ioi (t + 1 / (m + 1 : ℝ)) with hG
    have hGmono : Monotone G := by
      intro m m' hmm
      refine Set.Ioi_subset_Ioi ?_
      have hcast : (m : ℝ) ≤ m' := by exact_mod_cast hmm
      have : (1 : ℝ) / (m' + 1) ≤ 1 / (m + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have hGunion : (⋃ m, G m) = Set.Ioi t := by
      ext x
      simp only [Set.mem_iUnion, hG, Set.mem_Ioi]
      constructor
      · rintro ⟨m, hm⟩
        have : (0 : ℝ) < 1 / (m + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - t by linarith)
        exact ⟨m, by linarith⟩
    have hνG : Tendsto (fun m => (ν : Measure ℝ) (G m)) atTop
        (𝓝 ((ν : Measure ℝ) (Set.Ioi t))) := by
      have := tendsto_measure_iUnion_atTop (μ := (ν : Measure ℝ)) hGmono
      rwa [hGunion] at this
    refine le_of_tendsto hνG ?_
    filter_upwards with m
    have hopen : IsOpen (G m) := isOpen_Ioi
    refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hopen).trans ?_
    refine liminf_le_liminf ?_
    have hev : ∀ᶠ k in atTop, tk k < t + 1 / (m + 1 : ℝ) :=
      htk.eventually (eventually_lt_nhds (lt_add_of_pos_right t (by positivity)))
    filter_upwards [hev] with k hk
    exact measure_mono (Set.Ioi_subset_Ioi hk.le)
  -- Upper bound: `limsup a ≤ ν(t, ∞)`.
  have hup : limsup a atTop ≤ (ν : Measure ℝ) (Set.Ioi t) := by
    set F : ℕ → Set ℝ := fun m => Set.Ici (t - 1 / (m + 1 : ℝ)) with hF
    have hFanti : Antitone F := by
      intro m m' hmm
      refine Set.Ici_subset_Ici.mpr ?_
      have hcast : (m : ℝ) ≤ m' := by exact_mod_cast hmm
      have : (1 : ℝ) / (m' + 1) ≤ 1 / (m + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have hFinter : (⋂ m, F m) = Set.Ici t := by
      ext x
      simp only [Set.mem_iInter, hF, Set.mem_Ici]
      constructor
      · intro hx
        by_contra h
        push_neg at h
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t - x by linarith)
        have := hx m
        linarith
      · intro hx m
        have : (0 : ℝ) < 1 / (m + 1) := by positivity
        linarith
    have hνF : Tendsto (fun m => (ν : Measure ℝ) (F m)) atTop
        (𝓝 ((ν : Measure ℝ) (Set.Ici t))) := by
      have := tendsto_measure_iInter_atTop (μ := (ν : Measure ℝ))
        (fun m => (measurableSet_Ici).nullMeasurableSet) hFanti ⟨0, measure_ne_top _ _⟩
      rwa [hFinter] at this
    have hIci : (ν : Measure ℝ) (Set.Ici t) = (ν : Measure ℝ) (Set.Ioi t) :=
      measure_congr (MeasureTheory.Ioi_ae_eq_Ici (μ := (ν : Measure ℝ)) (a := t)).symm
    rw [hIci] at hνF
    refine ge_of_tendsto hνF ?_
    filter_upwards with m
    have hclosed : IsClosed (F m) := isClosed_Ici
    refine le_trans ?_ (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hclosed)
    refine limsup_le_limsup ?_
    have hev : ∀ᶠ k in atTop, t - 1 / (m + 1 : ℝ) < tk k :=
      htk.eventually (eventually_gt_nhds (sub_lt_self t (by positivity)))
    filter_upwards [hev] with k hk
    exact measure_mono (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hk.le))
  exact tendsto_of_le_liminf_of_limsup_le hlow hup

/-- **Existence of a standard-normal upper quantile.** For `α ∈ (0,1)` there is a `z` with
`N(0,1)(z, ∞) = α`. Atomless case of `exists_critical_constants`. -/
private lemma exists_gaussian_upper_quantile {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ z : ℝ, gaussianReal 0 1 (Set.Ioi z) = ENNReal.ofReal α := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  obtain ⟨C, γ, _, _, hCeq⟩ := exists_critical_constants (gaussianReal 0 1) hα hα1
  have hatom : (gaussianReal 0 1 {x : ℝ | x = C}).toReal = 0 := by
    have hsingle : {x : ℝ | x = C} = ({C} : Set ℝ) := by ext x; simp
    rw [hsingle, measure_singleton C, ENNReal.toReal_zero]
  rw [hatom, mul_zero, add_zero] at hCeq
  refine ⟨C, ?_⟩
  have hset : {x : ℝ | C < x} = Set.Ioi C := rfl
  rw [hset] at hCeq
  rw [← ENNReal.ofReal_toReal (measure_ne_top (gaussianReal 0 1) (Set.Ioi C)), hCeq]

/-- **Assembly of the large-`k` tail limit.** With standardised noncentralities `l k / √(2k)`
converging to `cc`, the noncentral tail `M(k, hseq k)` converges to `N(cc,1)(z, ∞)`, where `z`
is the standard-normal upper-`α` quantile. Combines
`weakConverges_noncentralChiSquared_standardized`, `tendsto_chiSquared_quantile_standardized`
and the moving-threshold portmanteau tail. -/
private lemma noncentralTail_tendsto_aux {α cc z : ℝ} {c : ℕ → ℝ} {hseq : ℕ → ℝ}
    (hc : ∀ k, 0 < k → chiSquared k (Set.Ioi (c k)) = ENNReal.ofReal α)
    (hz : gaussianReal 0 1 (Set.Ioi z) = ENNReal.ofReal α)
    (hl : Tendsto (fun k : ℕ => (hseq k) ^ 2 / Real.sqrt (2 * k)) atTop (𝓝 cc)) :
    Tendsto (fun k => noncentralTail k (c k) (hseq k)) atTop
      (𝓝 ((gaussianReal cc 1 (Set.Ioi z)).toReal)) := by
  classical
  set l : ℕ → ℝ≥0 := fun k => ((hseq k) ^ 2).toNNReal with hldef
  have hlcoe : ∀ k, (l k : ℝ) = (hseq k) ^ 2 := fun k => Real.coe_toNNReal _ (sq_nonneg _)
  have hl' : Tendsto (fun k : ℕ => (l k : ℝ) / Real.sqrt (2 * k)) atTop (𝓝 cc) := by
    apply hl.congr
    intro k
    rw [hlcoe]
  set μ' : ℕ → Measure ℝ := fun k => (noncentralChiSquared k (l k)).map
    (fun x => (x - k) / Real.sqrt (2 * k)) with hμ'
  have hwc := weakConverges_noncentralChiSquared_standardized (l := l) (c := cc) hl'
  have hμ'prob : ∀ k, IsProbabilityMeasure (μ' k) := by
    intro k
    have hmap : μ' k = (noncentralChiSquared k (l k)).map
        (fun x => (x - k) / Real.sqrt (2 * k)) := rfl
    rw [hmap]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  set μs : ℕ → ProbabilityMeasure ℝ := fun k => ⟨μ' k, hμ'prob k⟩ with hμs
  set ν : ProbabilityMeasure ℝ := ⟨gaussianReal cc 1, by infer_instance⟩ with hν
  haveI : NoAtoms (ν : Measure ℝ) := by
    show NoAtoms (gaussianReal cc 1); exact noAtoms_gaussianReal one_ne_zero
  have htend : Tendsto μs atTop (𝓝 ν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hA := hwc f
    simpa only [hμs, hμ', hν, ProbabilityMeasure.coe_mk] using hA
  set tk : ℕ → ℝ := fun k => (c k - k) / Real.sqrt (2 * k) with htk_def
  have htk : Tendsto tk atTop (𝓝 z) := tendsto_chiSquared_quantile_standardized hc hz
  have hport := tendsto_measure_Ioi_of_weakLimit htend htk
  have hportR : Tendsto (fun k => ((μs k : Measure ℝ) (Set.Ioi (tk k))).toReal) atTop
      (𝓝 (((ν : Measure ℝ) (Set.Ioi z)).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  refine hportR.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hskpos : (0 : ℝ) < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hcoe : ((μs k : Measure ℝ)) = μ' k := rfl
  have hpre : (μ' k) (Set.Ioi (tk k)) = noncentralChiSquared k (l k) (Set.Ioi (c k)) := by
    have hmap : μ' k = (noncentralChiSquared k (l k)).map
        (fun x => (x - k) / Real.sqrt (2 * k)) := rfl
    rw [hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    rw [lt_div_iff₀ hskpos]
    have hval : tk k * Real.sqrt (2 * (k : ℝ)) = c k - k := by
      simp only [htk_def]; rw [div_mul_cancel₀ _ hskpos.ne']
    rw [hval]; constructor <;> intro h <;> linarith
  show ((μs k : Measure ℝ) (Set.Ioi (tk k))).toReal
      = ((noncentralChiSquared k ((hseq k) ^ 2).toNNReal) (Set.Ioi (c k))).toReal
  rw [hcoe, hpre, hldef]

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
  -- Standard-normal upper-`α` quantile.
  obtain ⟨z, hz⟩ := exists_gaussian_upper_quantile hα hα1
  -- Boundedness of `hseq` forces the standardised noncentrality to `0`.
  have hl : Tendsto (fun k : ℕ => (hseq k) ^ 2 / Real.sqrt (2 * k)) atTop (𝓝 0) := by
    have hnum : Tendsto (fun k : ℕ => (hseq k) ^ 2) atTop (𝓝 (h ^ 2)) := hconv.pow 2
    have hden : Tendsto (fun k : ℕ => Real.sqrt (2 * (k : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    exact hnum.div_atTop hden
  -- The assembly gives the limit `N(0,1)(z, ∞) = α`.
  have key := noncentralTail_tendsto_aux hc hz hl
  rwa [hz, ENNReal.toReal_ofReal hα.le] at key

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
  -- The standardised noncentrality converges to the drift `γ` by hypothesis.
  have key := noncentralTail_tendsto_aux hc hz hrate
  -- Translation of the Gaussian shift: `N(γ,1)(z, ∞) = N(0,1)(z − γ, ∞)`.
  have htrans : gaussianReal γ 1 (Set.Ioi z) = gaussianReal 0 1 (Set.Ioi (z - γ)) := by
    have h1 : (gaussianReal 0 1).map (· + γ) = gaussianReal γ 1 := by
      rw [gaussianReal_map_add_const]; norm_num
    rw [← h1, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  rwa [htrans] at key

end StatLean.HypothesisTesting
