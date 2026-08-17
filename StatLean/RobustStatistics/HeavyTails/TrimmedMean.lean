import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.ConcentrationInequalities.Bernstein.Bernstein
import Mathlib.Probability.Moments.Variance

/-!
# The trimmed mean is sub-Gaussian — truncation at data-driven quantiles

Truncating at fixed levels cannot be sub-Gaussian (the levels must scale with the
confidence); the modern result — Oliveira–Orenstein (2019), presented as `LM §2.3` — is
that trimming a `log(1/δ)/n`-fraction *chosen from the data* is. This file formalizes
the sample-split variant analyzed in `LM Theorem 6`: one half of the data picks the
truncation levels as order statistics, the other half is averaged after truncation:

  `μ̂₂ₙ = (1/n) ∑ᵢ φ_{α,β}(Xᵢ)`,  `α = Y*₍εn₎`, `β = Y*₍₍₁₋ε₎n₎`, `ε = 16 log(8/δ)/(3n)`,

and `|μ̂₂ₙ − μ| ≤ 9σ√(log(8/δ)/n)` with probability `≥ 1 − δ`. Unlike median-of-means,
the trimmed mean is also robust to adversarial contamination (Lugosi–Mendelson (2021),
Ann. Statist. — bib note only; not formalized this round).

* `truncate` — the truncation function `φ_{a,b}` (`LM §2.3`); Huber's score is the
  symmetric special case `truncate (−c) c = huberPsi c`.
* `trimmedMeanAt` — the two-sample estimator with `Fin`-indexed truncation levels.
* `quantile` — `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3` proof).
* `orderStat_quantile_brackets` — the Bernstein bracketing `LM (2.6)`–`(2.7)`.
* `truncated_bias_le` / `truncated_concentration` — the two proof halves.
* `trimmedMean_deviation` — `LM Theorem 6`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.3, displays (2.6)–(2.7), Theorem 6; after R. I. Oliveira and P. Orenstein,
*The sub-Gaussian property of trimmed means* (2019). Truncation levels are Round-1
`orderStat`s; the count concentration is `ConcentrationInequalities.bernstein_inequality`.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting in
/-- **The truncation function** `φ_{a,b}(x) = max a (min b x)` (`LM §2.3`): the identity
on `[a, b]`, clipped to the nearer endpoint outside. For `a ≤ b` this is the projection
onto `[a, b]`; Huber's score is the symmetric case `truncate (−c) c = huberPsi c`. -/
noncomputable def truncate (a b x : ℝ) : ℝ := max a (min b x)

/-- Truncation projects into the interval: `a ≤ b → truncate a b x ∈ [a, b]`. -/
theorem truncate_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    truncate a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left b x)⟩

/-- Truncation fixes interval points: `x ∈ [a, b] → truncate a b x = x`. -/
theorem truncate_eq_self {a b x : ℝ} (hx : x ∈ Set.Icc a b) : truncate a b x = x := by
  rw [truncate, min_eq_right hx.2, max_eq_right hx.1]

open StatLean.MultipleTesting in
/-- **The two-sample trimmed mean** (`LM §2.3`, the estimator of Theorem 6): truncate
the `x`-sample at the `a`-th and `b`-th order statistics of the independent `y`-sample
and average. The intended indices are `a = εn − 1` and `b = (1−ε)n − 1` (0-indexed) for
the trimming fraction `ε`; they are parameters here, fixed by the theorem. -/
noncomputable def trimmedMeanAt {n : ℕ} (a b : Fin n) (x y : Fin n → ℝ) : ℝ :=
  sampleMean (fun i => truncate (orderStat y a) (orderStat y b) (x i))

/-- **The upper quantile function** `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3`
proof). For a probability measure and `p ∈ (0, 1)` the defining set is nonempty and
bounded above, so the supremum is honest. -/
noncomputable def quantile (P : Measure ℝ) (p : ℝ) : ℝ :=
  sSup {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}

/-! ### Right-tail mass: the elementary continuity bricks

`M ↦ P(X ≥ M)` is antitone with limits `1` at `−∞` and `0` at `+∞`; it is left-continuous
always (`Ici` is a decreasing intersection of `Ici`s) and right-continuous exactly when the
level carries no atom. These three facts are all the quantile lemmas below need. -/

/-- The right-tail mass `M ↦ P(X ≥ M)` is antitone. -/
private theorem tail_antitone (P : Measure ℝ) [IsProbabilityMeasure P] :
    Antitone (fun M : ℝ => P.real {x | M ≤ x}) := fun _ _ h =>
  measureReal_mono (fun _ hx => le_trans h hx)

/-- Right-tail mass tends to `1` at `−∞` (continuity from below: `⋃ M, [M, ∞) = ℝ`). -/
private theorem tail_tendsto_atBot (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun M : ℝ => P.real {x | M ≤ x}) atBot (𝓝 1) := by
  have hU : (⋃ M : ℝ, {x : ℝ | M ≤ x}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨x, le_rfl⟩
  have h := tendsto_measure_iUnion_atBot (μ := P) (s := fun M : ℝ => {x : ℝ | M ≤ x})
    (fun _ _ h _ hx => le_trans h hx)
  rw [hU, measure_univ] at h
  have := (ENNReal.tendsto_toReal (by simp)).comp h
  simpa [Function.comp, measureReal_def] using this

/-- Right-tail mass tends to `0` at `+∞` (continuity from above: `⋂ M, [M, ∞) = ∅`). -/
private theorem tail_tendsto_atTop (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (fun M : ℝ => P.real {x | M ≤ x}) atTop (𝓝 0) := by
  have hI : (⋂ M : ℝ, {x : ℝ | M ≤ x}) = (∅ : Set ℝ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    exact ⟨x + 1, by linarith⟩
  have h := tendsto_measure_iInter_atTop (μ := P) (s := fun M : ℝ => {x : ℝ | M ≤ x})
    (fun _ => (measurableSet_Ici (a := _)).nullMeasurableSet)
    (fun _ _ h _ hx => le_trans h hx) ⟨0, measure_ne_top P _⟩
  rw [hI, measure_empty] at h
  have := (ENNReal.tendsto_toReal (by simp)).comp h
  simpa [Function.comp, measureReal_def] using this

/-- Left-continuity of the right-tail mass, in the only form used: if the level `1 − p` is
attained strictly to the left of `Q`, it is attained at `Q`. -/
private theorem tail_le_of_forall_lt (P : Measure ℝ) [IsProbabilityMeasure P] {Q c : ℝ}
    (h : ∀ M, M < Q → c ≤ P.real {x | M ≤ x}) : c ≤ P.real {x | Q ≤ x} := by
  have hanti : Antitone (fun k : ℕ => {x : ℝ | Q - 1 / (k + 1) ≤ x}) := by
    intro k l hkl x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have h1 : (1 : ℝ) / (l + 1) ≤ 1 / (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hkl
    linarith
  have hI : (⋂ k : ℕ, {x : ℝ | Q - 1 / (k + 1) ≤ x}) = {x : ℝ | Q ≤ x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      refine not_lt.1 fun hlt => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < Q - x by linarith)
      have := hx k
      linarith
    · intro hx k
      have : (0:ℝ) < 1 / (k + 1) := by positivity
      linarith
  have hten := tendsto_measure_iInter_atTop (μ := P)
    (s := fun k : ℕ => {x : ℝ | Q - 1 / (k + 1) ≤ x})
    (fun _ => (measurableSet_Ici (a := _)).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hI] at hten
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hten
  refine ge_of_tendsto hreal ?_
  filter_upwards with k
  change c ≤ P.real {x : ℝ | Q - 1 / (k + 1) ≤ x}
  refine h _ ?_
  have : (0:ℝ) < 1 / (k + 1) := by positivity
  linarith

/-- The quantile's defining set is nonempty and bounded above when `0 < p < 1`
(`LM §2.3` proof, implicit): mass to the right tends to `1` at `−∞` and to `0` at
`+∞`. -/
theorem quantile_set_nonempty_bddAbove (P : Measure ℝ) [IsProbabilityMeasure P]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}.Nonempty ∧
      BddAbove {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} := by
  constructor
  · obtain ⟨M, hM⟩ :=
      ((tail_tendsto_atBot P).eventually_const_lt (show 1 - p < 1 by linarith)).exists
    exact ⟨M, hM.le⟩
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((tail_tendsto_atTop P).eventually_lt_const (show (0:ℝ) < 1 - p by linarith))
    exact ⟨K, fun M hM => not_lt.1 fun hlt => absurd hM (not_le.2 (hK M hlt.le))⟩

/-- **Right-tail mass at the quantile** (`LM §2.3` proof, "in that case
`P(X ≥ Q_p) = 1 − p`"): for a nonatomic distribution the quantile achieves its level
exactly. The no-atoms hypothesis is LM's "assume `X` has a nonatomic distribution"
simplification, carried explicitly. -/
theorem measure_ge_quantile (P : Measure ℝ) [IsProbabilityMeasure P]
    -- USER-INPUT: nonatomic distribution; LM §2.3 proof ("for ease of exposition")
    (hatom : ∀ t : ℝ, P {t} = 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    P.real {x | quantile P p ≤ x} = 1 - p := by
  obtain ⟨hne, hbdd⟩ := quantile_set_nonempty_bddAbove P hp hp1
  have hQ : quantile P p = sSup {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} := rfl
  refine le_antisymm ?_ (tail_le_of_forall_lt P fun M hM => ?_)
  · -- **Right-continuity at the quantile.** Beyond `Q` the defining inequality fails, and
    -- `(Q, ∞)` is the increasing union of the `[Q + 1/(k+1), ∞)`; the atom at `Q` is null.
    have hmono : Monotone (fun k : ℕ => {x : ℝ | quantile P p + 1 / (k + 1) ≤ x}) := by
      intro k l hkl x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have h1 : (1:ℝ) / (l + 1) ≤ 1 / (k + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hkl)
      linarith
    have hU : (⋃ k : ℕ, {x : ℝ | quantile P p + 1 / (k + 1) ≤ x})
        = {x : ℝ | quantile P p < x} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k, hk⟩
        have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < x - quantile P p by linarith)
        exact ⟨k, by linarith⟩
    have hten := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU] at hten
    have hreal := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hten
    have hlim : P.real {x : ℝ | quantile P p < x} ≤ 1 - p := by
      refine le_of_tendsto hreal ?_
      filter_upwards with k
      change P.real {x : ℝ | quantile P p + 1 / (k + 1) ≤ x} ≤ 1 - p
      by_contra hcon
      have hmem : quantile P p + 1 / (k + 1) ∈ {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} :=
        (not_le.1 hcon).le
      have hle := le_csSup hbdd hmem
      rw [← hQ] at hle
      have hpos : (0:ℝ) < 1 / (k + 1) := by positivity
      linarith
    have hsplit : P.real {x : ℝ | quantile P p ≤ x} ≤ P.real {x : ℝ | quantile P p < x} := by
      simp only [measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top P _) ?_
      calc P {x : ℝ | quantile P p ≤ x} ≤ P ({quantile P p} ∪ {x : ℝ | quantile P p < x}) := by
            refine measure_mono fun x hx => ?_
            rcases eq_or_lt_of_le (Set.mem_setOf_eq ▸ hx) with h | h
            · exact Or.inl h.symm
            · exact Or.inr h
        _ ≤ P {quantile P p} + P {x : ℝ | quantile P p < x} := measure_union_le _ _
        _ = P {x : ℝ | quantile P p < x} := by rw [hatom (quantile P p), zero_add]
    linarith
  · -- **Left-continuity below the quantile.** Every `M < Q` is dominated by a member of the
    -- defining set, so the level `1 − p` is attained at every such `M`.
    rw [hQ] at hM
    obtain ⟨M', hM'S, hMM'⟩ := exists_lt_of_lt_csSup hne hM
    exact le_trans hM'S (tail_antitone P hMM'.le)

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

open StatLean.MultipleTesting in
/-- **The Bernstein order-statistic brackets** (`LM (2.6)`–`(2.7)`): with probability at
least `1 − 4 exp(−(3/16) r)`, the trimming order statistics of an i.i.d. sample `Y` are
bracketed by population quantiles — writing `ε = r/n`,

  `Q_{ε/2} ≤ Y*₍εn₎ ≤ Q_{2ε}`  and  `Q_{1−2ε} ≤ Y*₍₍₁₋ε₎n₎ ≤ Q_{1−ε/2}`.

Each one-sided count deviation is a Bernstein event for indicator sums at rate
`exp(−(3/16)εn) = exp(−(3/16)r)`. -/
theorem orderStat_quantile_brackets {n r : ℕ} {Y : Fin n → Ξ → ℝ}
    {a b : Fin n}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hY_meas : ∀ i, Measurable (Y i))
    -- USER-INPUT: jointly independent sample; LM Theorem 6
    (hY_indep : iIndepFun Y μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hY_law : ∀ i, μprob.map (Y i) = P)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: the trim count is in the working range 1 ≤ r, 4r < n
    -- (so that ε = r/n has 2ε < 1/2); LM Theorem 6 sample-size condition
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the trimming indices, 0-indexed: a = εn − 1, b = (1−ε)n − 1;
    -- LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    1 - 4 * Real.exp (-(3 / 16) * r)
      ≤ μprob.real {ξ |
          quantile P (r / (2 * n)) ≤ orderStat (fun i => Y i ξ) a ∧
          orderStat (fun i => Y i ξ) a ≤ quantile P (2 * r / n) ∧
          quantile P (1 - 2 * r / n) ≤ orderStat (fun i => Y i ξ) b ∧
          orderStat (fun i => Y i ξ) b ≤ quantile P (1 - r / (2 * n))} := by
  sorry

/-- **The truncation-bias bound** (`LM Theorem 6` proof, the display
`|E[φ_{α,β}(X)|Y] − μ| ≤ σ√(32ε)`): whenever the truncation levels are quantile-
bracketed as in `orderStat_quantile_brackets`, the conditional bias of the truncated
variable is at most `σ√(32ε)` with `ε = r/n` — via Chebyshev on the tail location
(`Q_{1−2ε} ≤ μ + σ/√(2ε)`) and Cauchy–Schwarz on the truncated tails. Stated at the
population level: for any deterministic levels `α β` inside the brackets. -/
theorem truncated_bias_le {μ₀ σ2 : ℝ} {r n : ℕ} {α β : ℝ}
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ²; LM Theorem 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the levels sit inside the LM (2.6)–(2.7) brackets
    (hα₁ : quantile P (r / (2 * n)) ≤ α) (hα₂ : α ≤ quantile P (2 * r / n))
    (hβ₁ : quantile P (1 - 2 * r / n) ≤ β) (hβ₂ : β ≤ quantile P (1 - r / (2 * n))) :
    |(∫ x, truncate α β x ∂P) - μ₀| ≤ Real.sqrt σ2 * Real.sqrt (32 * r / n) := by
  sorry

open StatLean.MultipleTesting in
/-- **The trimmed mean is sub-Gaussian** (`LM Theorem 6`): two independent i.i.d.
samples of size `n` (presented as one jointly independent family on `Fin n ⊕ Fin n`;
`.inl` = averaged sample, `.inr` = truncation-calibration sample), variance `σ² > 0`,
`δ ∈ (0,1)` with `n > (16/3) log(8/δ)`, trim count `r = εn` for
`ε = 16 log(8/δ)/(3n)` (LM's "εn is an integer" simplification, carried as the
integrality hypothesis `hr`). Then with probability at least `1 − δ`,

  `|μ̂₂ₙ − μ₀| ≤ 9 σ √(log(8/δ)/n)`.

**Constant note.** LM's `9` combines a bias term they bound by `6σ√(log(8/δ)/n)` and a
Bernstein term bounded by `3σ√(log(8/δ)/n)`; the closure lane must verify the composite
constant and, per the project constants policy, repair to the provable value (keeping
the `σ√(log(8/δ)/n)` shape) with a documented deviation if `9` does not survive
formalization. -/
theorem trimmedMean_deviation {n r : ℕ} {Z : Fin n ⊕ Fin n → Ξ → ℝ}
    {a b : Fin n} {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hZ_meas : ∀ i, Measurable (Z i))
    -- USER-INPUT: the 2n observations are jointly independent; LM Theorem 6
    (hZ_indep : iIndepFun Z μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hZ_law : ∀ i, μprob.map (Z i) = P)
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ² > 0; LM Thm 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (hσ : 0 < σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: confidence level and sample-size condition; LM Theorem 6
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : 16 / 3 * Real.log (8 / δ) < n)
    -- USER-INPUT: trim count integrality ε·n = r; LM §2.3 step (1) simplification
    (hr : (r : ℝ) = 16 * Real.log (8 / δ) / 3) (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: trimming indices (0-indexed); LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    μprob.real {ξ | 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |trimmedMeanAt a b (fun i => Z (.inl i) ξ) (fun i => Z (.inr i) ξ) - μ₀|}
      ≤ δ := by
  sorry

end StatLean.RobustStatistics
