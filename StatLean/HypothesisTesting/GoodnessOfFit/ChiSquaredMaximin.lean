import StatLean.HypothesisTesting.GoodnessOfFit.ChiSquaredMultinomial
import StatLean.HypothesisTesting.GoodnessOfFit.AsymptoticMaximin
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction

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
open scoped ENNReal BigOperators NNReal

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
  -- TODO (RE-DERIVED; the previous note was wrong on the first point).
  --
  -- • This is **not** an instance of `asymptotic_maximin_upper_bound`, and cannot be made
  --   one: the shells do not match, and they mismatch in the *unusable* direction.  Under
  --   the reduction `z = (h₁,…,h_k)` (the last coordinate being determined by `∑ⱼ hⱼ = 0`)
  --   the transfer lemma's shell is the whole `{z : b² ≤ zᵀ Σ⁻¹ z}`, whereas
  --   `multinomialShell π b n` carries in addition the *sample-size dependent* positivity
  --   constraint `πⱼ + hⱼ/√n ≥ 0`; so `multinomialShell` maps onto a **subset**, and `sInf`
  --   over a subset is `≥` `sInf` over the superset.  The transfer lemma therefore bounds
  --   the wrong quantity.  (The mixture proof *does* give the multinomial statement, since
  --   the least-favourable `σ` is carried by the compact sphere `λ(h) = b²`, which lies
  --   inside the positivity constraint for all large `n`; but that is the proof, not the
  --   frozen statement.  The same remark applies to `SmoothTest.smoothTest_maximin_upper_bound`
  --   and is recorded in the note of `asymptotic_maximin_upper_bound`.)
  -- • Independently, the multinomial local-experiment data required by that lemma is still
  --   missing: the log-likelihood field `L n h` and its LAN quadratic expansion.  Only the
  --   centring half is available (`ChiSquaredMultinomial.reducedCount_weakConverges_gaussian`
  --   gives `Z n ⇒ N(0, Σ)`); the `hdens`/`hLAN` package is not.  Note also that `hdens`
  --   would need `Q n h ≪ Q n 0`, which fails at the boundary of the positivity constraint.
  --
  -- So the honest route is the mixture–Neyman–Pearson argument run directly on the moving
  -- shell — i.e. the same missing apparatus as `asymptotic_maximin_upper_bound` (the
  -- pre-agreed batch-ledger debt), not a corollary of it.
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
  -- TODO (RE-DERIVED; two of the three obstructions listed previously are now GONE).
  --
  -- • Tail monotonicity in the noncentrality is CLOSED: `noncentralChiSquared_tail_mono`
  --   and the `stdGaussian_normSq_le_antitone` it rests on are both proved axiom-clean in
  --   `ForMathlib/NoncentralChiSquared.lean` (unequal-weight Prékopa–Leindler).
  -- • The per-`h` local power is CLOSED: `ChiSquaredMultinomial.pearsonQ_local_power_nondegenerate`
  --   gives, axiom-clean, `power (Q n) 1{Qₙ > c} h → ncχ²_k(λ(h))(c,∞)` for every fixed
  --   centred `h`, together with the two strict bounds `α < value < 1`.  (Its no-atom and
  --   strict-comparison bricks live in that file.)
  -- • Consequently the `limsup ≤` half of the first conjunct is now routine: evaluate at a
  --   FIXED `h` with `∑ⱼ hⱼ = 0` and `λ(h) = b²`; such an `h` lies in `multinomialShell π b n`
  --   for every large `n` (the constraint `πⱼ + hⱼ/√n ≥ 0` holds eventually since `πⱼ > 0`),
  --   so `sInf … ≤ power_n(h) → ncχ²_k(b²)(c,∞)`.
  --
  -- WHAT IS ACTUALLY LEFT is a single, genuinely uniform statement: the `liminf ≥` half,
  -- i.e. `inf_{h ∈ multinomialShell π b n} power_n(h) ≥ ncχ²_k(b²)(c,∞) − ε` eventually.
  -- The shell is unbounded AND moves with `n`, so the competitor is a *diagonal* sequence
  -- `hₙ ∈ multinomialShell π b n` with `λ(hₙ)` possibly `→ ∞`; controlling `power_n(hₙ)`
  -- from below along such a sequence is a uniform (Berry–Esseen / tightness-over-the-shell)
  -- statement that no per-`h` weak limit supplies.  The natural brick is a multinomial
  -- Berry–Esseen over the ellipsoids `{Qₙ > c}`, uniform in the local parameter; the
  -- project has `ForMathlib/MultivariateBerryEsseen` only for slabs and balls of a *fixed*
  -- law, not for a triangular array of drifting multinomial rows.
  --
  -- Second conjunct is exactly `chiSquared_maximin_upper_bound` above (see its note: it is
  -- NOT an instance of `asymptotic_maximin_upper_bound`, the shell inclusion going the
  -- wrong way, and needs the mixture argument on the moving shell).
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
  -- TODO (RE-DERIVED: the proof is now pinned down to one named missing brick).
  --
  -- Reduction to the one-step case `k₂ = k₁ + 1` (then induct; `h = 0` gives equality
  -- `M(k,0) = α` for every `k ≥ 1`, which is why strictness is excluded there).  Write
  -- `χ²_{k+1}(λ) = χ²_k(λ) ⋆ χ²_1` (the extra coordinate is centred, the mean vector being
  -- carried by the first axis), put `G x = P{χ²_1 > c_{k+1} − x}` — nondecreasing, `0 ↑ 1` —
  -- and `ψ = 1_{(c_k,∞)} − G`.  Then
  --     `M(k+1,h) = E_λ[G]`,  `M(k,h) = E_λ[1_{(c_k,∞)}]`,
  -- and the matched levels give `E_0[ψ] = α − α = 0`.  Moreover `ψ ≤ 0` on `(−∞, c_k]` and
  -- `ψ ≥ 0` on `(c_k, ∞)`: `ψ` is *single crossing*.  Hence `E_λ[ψ] ≥ E_0[ψ] = 0`, i.e.
  -- `M(k+1,h) ≤ M(k,h)`, **provided the family `χ²_k(λ)` has monotone likelihood ratio in
  -- `λ`** (Das Gupta; Cochran 1952).
  --
  -- Stochastic ordering is NOT enough here, and in particular the available
  -- `noncentralChiSquared_tail_mono` does not suffice: `ψ` is *decreasing* on each of the
  -- two pieces, with an upward jump at `c_k`, so it is not monotone and only the MLR
  -- (single-crossing) lemma applies.
  --
  -- MISSING BRICK: `MLR of noncentralChiSquared k · in the noncentrality`.  Both standard
  -- routes need material absent from the project — the Bessel-series density of `χ²_k(λ)`,
  -- or the Poisson mixture representation `χ²_k(λ) = ∑ⱼ Pois(λ/2)(j) · χ²_{k+2j}` (whose
  -- MLR would then come from the Poisson family).  The repository's `noncentralChiSquared`
  -- is defined as a pushforward of a Gaussian and carries no density at all.
  sorry

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
